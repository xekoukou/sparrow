
#define _GNU_SOURCE

#include <sys/epoll.h>
#include <errno.h>
#include <stdio.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netdb.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <fcntl.h>
#include <time.h>
#include <stdlib.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include "tree.h"
#include "sparrow.h"

#define MAX_EVENTS 32
// #define MAX_DELAY 40 //in milliseconds. We wait that much before sending new data if we do not have much data.
// #define MAX_BUFF (1500 - 68) // The ethernet MTU is 1500 bytes minus the IP/TCP headers.
// One millisecond clock precision.
#define CLOCK_PRECISION 1000000
#define MAX_SEND_QUEUE 10


int64_t os_now(void) {
  struct timespec ts;
  int rc = clock_gettime(CLOCK_MONOTONIC, &ts);
  assert (rc == 0);
  return ((int64_t) ts.tv_sec) * 1000 + (((int64_t) ts.tv_nsec) / 1000000);
}

int64_t now(void) {
  uint32_t low;
  uint32_t high;
  __asm__ volatile("rdtsc" : "=a" (low), "=d" (high));
  int64_t tsc = (int64_t)((uint64_t)high << 32 | low);

  static int64_t last_tsc = -1;
  static int64_t last_now = -1;
  if(__builtin_expect(!!(last_tsc < 0), 0)) {
    last_tsc = tsc;
    last_now = os_now();
  }   

  if(__builtin_expect(!!(tsc - last_tsc <= (CLOCK_PRECISION / 2) && tsc >= last_tsc), 1))
    return last_now;

  last_tsc = tsc;
  last_now = os_now();
  return last_now;
}


//The current position is set by the multiplexer/serializer.

struct data_out_t {
  size_t cur;
  void * data;
  size_t len;
};

struct data_in_t {   //Send the data to the multiplexer/serializer when no more data are coming(?) or the buffer is full. The data present might be incomplete, thus the multiplexer will send the same buffer with the curr at the correct position.
  size_t cur;
  void * data;
  size_t len;
};

typedef struct data_out_t data_out_t;
typedef struct data_in_t data_in_t;

struct sparrow_socket_t {
  int listening; //BOOL
  int fd;
  int64_t expiry;
  data_out_t data_out;
  data_in_t data_in;
  RB_ENTRY (sparrow_socket_t) to_field;
  RB_ENTRY (sparrow_socket_t) fd_field;
};

typedef struct sparrow_socket_t sparrow_socket_t;

int cmp_fds(const void * sock1, const void * sock2) {
  const sparrow_socket_t * s1 = (const sparrow_socket_t *) sock1;
  const sparrow_socket_t * s2 = (const sparrow_socket_t *) sock2;
  return (s1->fd > s2->fd) - (s1->fd < s2->fd);
}

int cmp_tos(const void * sock1, const void * sock2) {
  const sparrow_socket_t * s1 = (const sparrow_socket_t *) sock1;
  const sparrow_socket_t * s2 = (const sparrow_socket_t *) sock2;
  return (s1->expiry > s2->expiry) - (s1->expiry < s2->expiry);
}



RB_HEAD (to_rb_t, sparrow_socket_t);
RB_PROTOTYPE (to_rb_t, sparrow_socket_t, to_field,cmp_tos);

RB_HEAD (fd_rb_t, sparrow_socket_t);
RB_PROTOTYPE (fd_rb_t, sparrow_socket_t, fd_field, cmp_fds);

RB_GENERATE (to_rb_t, sparrow_socket_t, to_field,cmp_tos);
RB_GENERATE (fd_rb_t, sparrow_socket_t, fd_field, cmp_fds);



struct sparrow_t {
  int fd;
  int event_cur;
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  struct fd_rb_t fd_rb_socks; // A tree container of sockets ordered by the fd.
  struct to_rb_t to_rb_socks; // A tree container of sockets ordered by the expiry.
  size_t already_expired;
};


sparrow_t * sparrow_new(void) {
  sparrow_t * sp = calloc(1,sizeof(sparrow_t));
  int fd = epoll_create1 (0);
  if (fd == -1) {
    perror("epoll_create1 failed to create epoll.");
    abort();
  }
  sp->fd = fd;
  sp->events_len = 0;
  RB_INIT(&(sp->fd_rb_socks));
  RB_INIT(&(sp->to_rb_socks));
  return sp;
}


//internal use only
void sparrow_add_socket(sparrow_t * sp, sparrow_socket_t *sock) {
  int rc;
  struct epoll_event event;
  event.data.fd = sock->fd;
  event.events = EPOLLIN;
  rc = epoll_ctl (sp->fd, EPOLL_CTL_ADD, sock->fd, &event);
  if (rc == -1) {
    perror(" epoll_ctl failed to add a socket to epoll");
    abort();
  }
  assert(RB_FIND(fd_rb_t, &(sp->fd_rb_socks), sock) == NULL);
  void *rtsearch = RB_INSERT(fd_rb_t, &(sp->fd_rb_socks), sock);
  assert(rtsearch == NULL);
}

//internal use only.
sparrow_socket_t * sparrow_socket_new(int fd) {
  sparrow_socket_t * sock = calloc(1,sizeof(sparrow_socket_t));
  sock->fd = fd;
  return sock;
}

//internal use only
sparrow_socket_t * sparrow_socket_set_non_blocking(sparrow_socket_t * sock) {
  int flags, rc;

  flags = fcntl (sock->fd, F_GETFL, 0);
  if (flags == -1) {
    perror ("fcntl failed to perform an action.");
    abort();
  }

  flags |= O_NONBLOCK;
  rc = fcntl (sock->fd, F_SETFL, flags);
  if (rc == -1) {
    perror ("fcntl failed to perform an action.");
    abort();
  }
  return sock;
}

//internal function
sparrow_socket_t * sparrow_socket_listen(sparrow_socket_t * sock) {
  int rc = listen(sock->fd,SOMAXCONN);
  if ( rc == -1 ) {
    perror("The socket failed to listen.");
    abort();
  }
  sock->listening = 1;
  return sock;
}

void sparrow_socket_bind(sparrow_t * sp, char * port) {
  struct addrinfo hints = {0};
  struct addrinfo *ret_addr;
  int rc, sfd;
  int flag = 1;

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  rc = getaddrinfo (NULL, port, &hints, &ret_addr);
  assert(rc == 0);

  sfd = socket (ret_addr->ai_family, ret_addr->ai_socktype, ret_addr->ai_protocol);
  assert(sfd != -1);
  
  rc = setsockopt(sfd,IPPROTO_TCP,TCP_NODELAY, (char *) &flag,sizeof(int));
  assert(rc == 0);
  rc = setsockopt(sfd,SOL_SOCKET,SO_REUSEPORT, (char *) &flag,sizeof(int));
  assert(rc == 0);

  rc = bind (sfd, ret_addr->ai_addr, ret_addr->ai_addrlen);
  if (rc != 0) {
    close (sfd);
    abort();
  }
  sparrow_socket_t * sock = sparrow_socket_new(sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  sparrow_socket_listen(sock);
}



sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port) {
  struct addrinfo hints = {0};
  struct addrinfo *ret_addr;
  int rc, sfd;

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  rc = getaddrinfo (address, port, &hints, &ret_addr);
  assert(rc == 0);

  sfd = socket (ret_addr->ai_family, ret_addr->ai_socktype, ret_addr->ai_protocol);
  assert(sfd != -1);
  rc = connect (sfd, ret_addr->ai_addr, ret_addr->ai_addrlen);
  if (rc != 0) {
    close (sfd);
    abort();
  }
  sparrow_socket_t * sock = sparrow_socket_new(sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  return sock;
}

//TODO It would be better if this was handled by sparrow. As well as possibly reconnecting on error.
void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock) {
  Dprintf("Connection closed: %d", sock->fd);
  close(sock->fd);
//  assert(sock->data_in.len == 0);
  RB_REMOVE(fd_rb_t, &(sp->fd_rb_socks), sock);
  RB_REMOVE(to_rb_t, &(sp->to_rb_socks), sock);
  free(sock);
}


//internal use only.
sparrow_socket_t * sparrow_socket_accept(sparrow_t * sp, sparrow_socket_t * lsock) {
  int nsfd = accept4(lsock->fd,NULL,NULL,SOCK_NONBLOCK);
  assert(nsfd != -1);
  sparrow_socket_t * sock = sparrow_socket_new(nsfd);
  sparrow_add_socket(sp,sock);
  return sock;
}



//Internal use only
int sparrow_handle_expired(sparrow_t * sp, sparrow_socket_t **_sock, int *event, int64_t *timeout){
  sparrow_socket_t * sock = RB_MIN(to_rb_t, &(sp->to_rb_socks));
  if(sp->already_expired > 0) {
    RB_REMOVE(to_rb_t, &(sp->to_rb_socks), sock);
    sp->already_expired--;
    *_sock = sock;
    *event = *event + 8;
    return 1;
  }
  if(sock !=NULL) {
    int64_t time = now();
    sparrow_socket_t * iter = sock;
    while ((iter != NULL) && (iter->expiry - time < 0 )) {
      sp->already_expired++;
      iter = RB_NEXT(to_rb_t, &(sp->to_rb_socks), iter);
    }
    if(sp->already_expired > 0) {
      RB_REMOVE(to_rb_t, &(sp->to_rb_socks), sock);
      sp->already_expired--;
      *_sock = sock;
      *event = 8;
      return 1;
    }
    *timeout = sock->expiry - time;
  } else {
    *timeout = -1;
  }
  return 0;
}


//Internal
//Requires an array of MAX_EVENT units.
int _sparrow_wait(sparrow_t * sp, sparrow_event_t * spev) {
  spev->event = 0;
  spev->error = 0;
  int64_t timeout;

  if(sparrow_handle_expired(sp, &(spev->sock), &(spev->event), &timeout)) {
    return 0;
  }

  if(sp->events_len == 0) {
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, timeout);
    //TODO Handle the errors.
    sp->event_cur = 0;
  }
  int i;
  sparrow_socket_t find_sock;
  for( i = sp->event_cur; i < sp->events_len; i++) {
    sp->event_cur++;
    find_sock.fd = sp->events[i].data.fd; 
    sparrow_socket_t * sock = RB_FIND(fd_rb_t, &(sp->fd_rb_socks), &find_sock);
    int event = sp->events[i].events;

    spev->sock = sock;

      //On error
      if((event & EPOLLERR) || (event & EPOLLHUP)) {
        printf("EPOLLERR || EPOLLHUP error.");
        spev->error = 1;
        sparrow_socket_close(sp,sock);
        return 0;
      }

    if(event & EPOLLOUT) {
      data_out_t *data_out = &(sock->data_out);
      assert(data_out->len > data_out->cur);
      assert(data_out->len != 0);
      int result = send(sock->fd, data_out->data + data_out->cur, data_out->len - data_out->cur, 0);

      //On error
      if(result < 0) {
        spev->error = 1;
        //TODO Make Dprintf.
        printf("Send error or connection closed.");
        sparrow_socket_close(sp,sock);
        return 0;
      }

      if(result + data_out->cur == data_out->len) {
        data_out->len = 0;

        struct epoll_event pevent;
        pevent.data.fd = sock->fd;
        pevent.events = EPOLLIN;
        int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
        if (rc == -1) {
          perror(" epoll_ctl failed to modify a socket to epoll");
          abort();
        }
        spev->event += 2;
      } else {
        data_out->cur += result;
      }
    }

    data_in_t *data_in = &(sock->data_in);
    if(event & EPOLLIN) {

      if(sock->listening) {
      // We accept a new client.
        spev->sock = sparrow_socket_accept(sp, sock);
        Dprintf("Listening Socket:\nfd:%d\n",sock->fd);
        spev->event += 16;
      } else {
        Dprintf("Receiving Socket:\nfd:%d\n",sock->fd);
        
        //TODO If we get data that we did not expect we close the connection. This could also happen when the other closes the connection.
        if(data_in->len == 0) {
          //TODO Make Dprintf
          printf("We got data that we did not expect or we received a signal that the connection closed.\nWe are closing the connection.\n");
          spev->error = 1;
          sparrow_socket_close(sp,sock);
          return 0;
        }

        assert(data_in->len > data_in->cur);
        int result = recv(sock->fd, data_in->data + data_in->cur, data_in->len - data_in->cur, 0);

        //On error or connection closed.
        //TODO We need to handle closed connections differently, possibly automatically reconnecting.
        if(result <= 0) {
          //TODO Make Dprintf
          printf("Receive error or we received a signal that the connection closed.\nWe are closing the connection.\n");
          spev->error = 1;
          sparrow_socket_close(sp,sock);
          return 0;
        }

        if(result + data_in->cur == data_in->len) {
          spev->cur = data_in->cur + result;
          spev->event += 4;
          data_in->len = 0;
        } else {
          data_in->cur += result;
        }
      }
    } else {
      if((!sock->listening) && data_in->len != 0) {
        spev->cur = data_in->cur;
        spev->event += 4;
      }
    }

    if(spev->event > 0) {
      return 0;
    }

  }
  sp->events_len = 0;

  return 1;
}

void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev) {

  while(_sparrow_wait(sp, spev)) {
  }
}

//The timeout should be changed when the data have been sent received. It is the job of the serializer/multiplexer to do that but care must be taken to do it correctly.
void sparrow_socket_set_timeout(sparrow_t * sp, sparrow_socket_t * sock, int64_t expiry) {

  if(sock->expiry > 0) {
    RB_REMOVE(to_rb_t, &(sp->to_rb_socks), sock);
  }
  sock->expiry = expiry;
  if(expiry > 0) {
    RB_INSERT(to_rb_t, &(sp->to_rb_socks), sock);
  }

}

int sparrow_send( sparrow_t * sp, sparrow_socket_t * sock, void * data, size_t len, int *error) {
  assert(data!=NULL);

  data_out_t *data_out = &(sock->data_out);
  assert(data_out->len == 0);
  data_out->data = data;
  data_out->len = len;
  data_out->cur = 0;

//Try to send as much as we can.

  int result = send(sock->fd, data_out->data + data_out->cur, data_out->len - data_out->cur, 0);

  //On error
  if(result <= 0) {
    sparrow_socket_close(sp,sock);
    *error = 1;
  }

  if(result + data_out->cur < data_out->len) {
    data_out->cur += result;

    struct epoll_event pevent;
    pevent.data.fd = sock->fd;
    pevent.events = EPOLLIN | EPOLLOUT;
    int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
    if (rc == -1) {
      perror(" epoll_ctl failed to modify a socket to epoll");
      abort();
    }
    return 0;
  } else {
    data_out->len = 0;
    return 1;
  }

}

void sparrow_recv( sparrow_t * sp, sparrow_socket_t * sock, void *data, size_t len) {

  Dprintf("Asking to receive socket:\nfd: %d\n",sock->fd);
  data_in_t *data_in = &(sock->data_in);
  assert(data_in->len == 0);
  data_in->data = data;
  data_in->len = len;
  data_in->cur = 0;
}

void * sparrow_socket_data_in(sparrow_socket_t *sock) {
  void *data = sock->data_in.data; 
  return data;
}

void * sparrow_socket_data_out(sparrow_socket_t *sock) {
  void *data = sock->data_out.data; 
  return data;
}
