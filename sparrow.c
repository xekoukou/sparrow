
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
#include <stdlib.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include "tree.h"
#include "sparrow.h"

#define MAX_EVENTS 32
// #define MAX_DELAY 40 //in milliseconds. We wait that much before sending new data if we do not have much data.
// #define MAX_BUFF (1500 - 68) // The ethernet MTU is 1500 bytes minus the IP/TCP headers.
// #define MAX_SEND_QUEUE 10
// #define MAX_INPUT_DELAY 20
#define MIN_OTIMEOUT_SAMPLE_INTERVAL 100

void * scalloc(size_t num, size_t size) {
  void * result = calloc(num, size);
  if(result == NULL) {
    exit(-1);
  }
  return result;
}

//TODO check for errors.
void * srealloc(void * prev_pointer, size_t size) {
  void * result = realloc(prev_pointer, size);
  if(result == NULL) {
    exit(-1);
  }
  return result;
}


struct data_out_t {
  size_t cur;
  void * data;
  size_t len;    //Len indicates that there is an output request.
};

struct data_in_t { 
  void * data;
  size_t len;   //Len indicates that there is an input request.
};

typedef struct data_out_t data_out_t;
typedef struct data_in_t data_in_t;

struct sparrow_socket_t {
  int listening; //BOOL
  int fd;
  int64_t out_expiry;
  data_out_t data_out;
  data_in_t data_in;
  RB_ENTRY (sparrow_socket_t) fd_field;
  RB_ENTRY (sparrow_socket_t) ot_field;
  void * parent; // a pointer to the higher level structure.
};

typedef struct sparrow_socket_t sparrow_socket_t;

int cmp_fds(const void * sock1, const void * sock2) {
  const sparrow_socket_t * s1 = (const sparrow_socket_t *) sock1;
  const sparrow_socket_t * s2 = (const sparrow_socket_t *) sock2;
  return (s1->fd > s2->fd) - (s1->fd < s2->fd);
}

RB_HEAD (fd_rb_t, sparrow_socket_t);
RB_GENERATE (fd_rb_t, sparrow_socket_t, fd_field, cmp_fds);

int cmp_ots(const void * sock1, const void * sock2) {
  const sparrow_socket_t * s1 = (const sparrow_socket_t *) sock1;
  const sparrow_socket_t * s2 = (const sparrow_socket_t *) sock2;
  return (s1->fd > s2->fd) - (s1->fd < s2->fd);
}

RB_HEAD (ot_rb_t, sparrow_socket_t);
RB_GENERATE (ot_rb_t, sparrow_socket_t, ot_field, cmp_ots);

struct sparrow_t {
  int fd;
  int event_cur;
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  struct fd_rb_t fd_rb_socks; // A tree container of sockets ordered by the fd.
  struct ot_rb_t ot_rb_socks; // A tree container of sockets ordered by the expiration if their outputs.
  int64_t default_ot;
  int64_t t_expiry;  // The time that the timeout expires.
  int64_t oltime; //Last time we checked for output expirations.
};

//Used to iterate over all sockets.
sparrow_socket_t * sparrow_first(sparrow_t * sp) {
  return RB_MIN(fd_rb_t, &(sp->fd_rb_socks));
}

sparrow_socket_t * sparrow_next(sparrow_t * sp, sparrow_socket_t * sock) {
  return RB_NEXT(fd_rb_t, &(sp->fd_rb_socks), sock);
}


//The timeout should be changed when the data have been sent received. It is the job of the serializer/multiplexer to do that but care must be taken to do it correctly. TODO update the comment
void sparrow_socket_set_timeout(sparrow_t * sp, int64_t timeout) {
  if(timeout > 0) {
    sp->t_expiry = now() + timeout;
  } else {
    sp->t_expiry = -1;
  }
}


int sparrow_try_immediate_send(sparrow_t * sp, sparrow_socket_t * sock) {
//Try to send as much as we can of there are data to send.

  data_out_t *data_out = &(sock->data_out);
  if(data_out->len != 0) {
  
    int result = send(sock->fd, data_out->data + data_out->cur, data_out->len - data_out->cur, 0);
  
    //On error
    if(result < 0 && (errno != EAGAIN)) {
      perror("Send error inside sparrow_send.\n");
      sparrow_socket_close(sp,sock);
      return -1;
    }
    
    if(result + data_out->cur < data_out->len) {
      if(result > 0) {
        data_out->cur += result;
      }
      return 0;
  
    } else {
  
      //We remove the socket from the output expiration tree.
      RB_REMOVE(ot_rb_t, &(sp->ot_rb_socks), sock);
      sock->out_expiry = -1;
      data_out->len = 0;
  
      struct epoll_event pevent = {0};
      pevent.data.fd = sock->fd;
      pevent.events = EPOLLIN;
      int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
      if (rc == -1) {
        perror(" epoll_ctl failed to modify a socket to epoll");
        exit(-1);
      }
  
      return 1;
    }
  }

  return 1;

}

int sparrow_send( sparrow_t * sp, sparrow_socket_t * sock, void * data, size_t len, sparrow_event_t * spev) {

  assert(data!=NULL);
  spev->sock = sock;
  spev->fd = sock->fd;
  spev->parent = sock->parent;
  spev->event = 0;

  data_out_t *data_out = &(sock->data_out);
  assert(data_out->len == 0);
  data_out->data = data;
  data_out->len = len;
  data_out->cur = 0;

//Try to send as much as we can.

  int result = send(sock->fd, data_out->data + data_out->cur, data_out->len - data_out->cur, 0);

  //On error
  if(result < 0 && (errno != EAGAIN)) {
    perror("Send error inside sparrow_send.\n");
    sparrow_socket_close(sp,sock);
    spev->event = 8;
    return 0;
  }

  if(result + data_out->cur < data_out->len) {
    if(result > 0) {
      data_out->cur += result;
    }

    struct epoll_event pevent = {0};
    pevent.data.fd = sock->fd;
    pevent.events = EPOLLIN | EPOLLOUT;
    int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
    if (rc == -1) {
      perror(" epoll_ctl failed to modify a socket to epoll");
      exit(-1);
    }

    //We add the socket to the output expiration tree.
    sock->out_expiry = now() + sp->default_ot;
    RB_INSERT(ot_rb_t, &(sp->ot_rb_socks), sock);
    Dprintf("I have more to send. Adding the socket to output expiry.\n");
    
    return 0;

  } else {
    data_out->len = 0;
    spev->event = 2;
    return 1;
  }

}

void sparrow_cancel_send( sparrow_t * sp, sparrow_socket_t * sock) {
  data_out_t *data_out = &(sock->data_out);
  assert(data_out->len != 0);
  data_out->len = 0;

  struct epoll_event pevent;
  pevent.data.fd = sock->fd;
  pevent.events = EPOLLIN;
  int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
  if (rc == -1) {
    perror(" epoll_ctl failed to modify a socket to epoll");
    exit(-1);
  }
}

void sparrow_recv( sparrow_t * sp, sparrow_socket_t * sock, void *data, size_t len) {

  Dprintf("Asking to receive socket:\nfd: %d\n",sock->fd);
  data_in_t *data_in = &(sock->data_in);
  assert(data_in->len == 0);
  data_in->data = data;
  data_in->len = len;
}

void sparrow_cancel_recv( sparrow_t * sp, sparrow_socket_t * sock) {
  data_in_t *data_in = &(sock->data_in);
  assert(data_in->len != 0);
  data_in->len = 0;
}

void * sparrow_socket_data_in(sparrow_socket_t *sock) {
  void *data = sock->data_in.data; 
  return data;
}

void * sparrow_socket_data_out(sparrow_socket_t *sock) {
  void *data = sock->data_out.data; 
  return data;
}


void sparrow_socket_set_parent(sparrow_socket_t * sock, void * parent) {
  sock->parent = parent;
}

void * sparrow_socket_get_parent(sparrow_socket_t * sock) {
  return sock->parent;
}


//internal use only.
sparrow_t * sparrow_new(int64_t dtimeout) {
  sparrow_t * sp = scalloc(1, sizeof(sparrow_t));
  int fd = epoll_create1 (0);
  if (fd == -1) {
    perror("epoll_create1 failed to create epoll.");
    exit(-1);
  }
  sp->fd = fd;
  sp->events_len = 0;
  RB_INIT(&(sp->fd_rb_socks));
  RB_INIT(&(sp->ot_rb_socks));
  sp->t_expiry = -1;
  sp->oltime = now();
  sp->default_ot = dtimeout;
  return sp;
}


//internal use only.
sparrow_socket_t * sparrow_socket_new(int fd) {
  sparrow_socket_t * sock = scalloc(1, sizeof(sparrow_socket_t));
  sock->fd = fd;
  sock->out_expiry = -1;
  sock->listening = 0;
  sock->parent = NULL;
  return sock;
}


//internal use only
void sparrow_add_socket(sparrow_t * sp, sparrow_socket_t *sock) {
  int rc;
  struct epoll_event event = {0};
  event.data.fd = sock->fd;
  event.events = EPOLLIN;
  rc = epoll_ctl (sp->fd, EPOLL_CTL_ADD, sock->fd, &event);
  if (rc == -1) {
    perror(" epoll_ctl failed to add a socket to epoll");
    exit(-1);
  }
  assert(RB_FIND(fd_rb_t, &(sp->fd_rb_socks), sock) == NULL);
  void *rtsearch = RB_INSERT(fd_rb_t, &(sp->fd_rb_socks), sock);
  assert(rtsearch == NULL);
}


//internal use only
sparrow_socket_t * sparrow_socket_set_non_blocking(sparrow_socket_t * sock) {
  int flags, rc;

  flags = fcntl (sock->fd, F_GETFL, 0);
  if (flags == -1) {
    perror ("fcntl failed to perform an action.");
    exit(-1);
  }

  flags |= O_NONBLOCK;
  rc = fcntl (sock->fd, F_SETFL, flags);
  if (rc == -1) {
    perror ("fcntl failed to perform an action.");
    exit(-1);
  }
  return sock;
}

//internal function
sparrow_socket_t * sparrow_socket_listen(sparrow_socket_t * sock) {
  int rc = listen(sock->fd,SOMAXCONN);
  if ( rc == -1 ) {
    perror("The socket failed to listen.");
    exit(-1);
  }
  sock->listening = 1;
  sock->parent = NULL;
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
    exit(-1);
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
  int flag = 1;

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  rc = getaddrinfo (address, port, &hints, &ret_addr);
  assert(rc == 0);

  sfd = socket (ret_addr->ai_family, ret_addr->ai_socktype, ret_addr->ai_protocol);
  assert(sfd != -1);

  rc = setsockopt(sfd,IPPROTO_TCP,TCP_NODELAY, (char *) &flag,sizeof(int));
  assert(rc == 0);

  rc = connect (sfd, ret_addr->ai_addr, ret_addr->ai_addrlen);
  if (rc != 0) {
    close (sfd);
    return NULL;
  }
  sparrow_socket_t * sock = sparrow_socket_new(sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  return sock;
}

void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock) {
  Dprintf("Connection closed: %d\n", sock->fd);
  close(sock->fd);
//  assert(sock->data_in.len == 0);
  RB_REMOVE(fd_rb_t, &(sp->fd_rb_socks), sock);
  if(sock->out_expiry > -1) {
    RB_REMOVE(ot_rb_t, &(sp->ot_rb_socks), sock);
  }
  free(sock);
}

void sparrow_close(sparrow_t ** sp) {
  sparrow_socket_t * sock;
  sparrow_socket_t * y;
  RB_FOREACH_SAFE(sock, fd_rb_t, &((*sp)->fd_rb_socks), y) {
    sparrow_socket_close(*sp, sock);
  }
  close((*sp)->fd);
  free(*sp);
  *sp = NULL;
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
int sparrow_handle_expired_ot(sparrow_t * sp, sparrow_event_t *spev, int64_t *timeout){
  int64_t time = now();

  if(time - sp->oltime > MIN_OTIMEOUT_SAMPLE_INTERVAL) {
    Dprintf("I am checking if there are output expiries\n");
    sparrow_socket_t * sock = RB_MIN(ot_rb_t, &(sp->ot_rb_socks));
    if(sock !=NULL) {
    Dprintf("There is a socket to check for output expiration\n");
      if(sock->out_expiry - time < 0) {
        printf("Output expiration error\n");
        RB_REMOVE(ot_rb_t, &(sp->ot_rb_socks), sock);
        spev->sock = NULL;
        spev->fd = sock->fd;
        spev->parent = sock->parent;
        sparrow_socket_close(sp, sock);
        spev->event = 8;
        return 1;
      }
      //If there is no new expirations update the time.
      sp->oltime = time;
      if((sp->t_expiry < 0) || (sock->out_expiry < sp->t_expiry)) {
        *timeout = sock->out_expiry - time;
        return 0;
      }
    }
  }
  if(sp->t_expiry < 0) {
    *timeout = -1;
  } else {
    *timeout = sp->t_expiry - time;
    if(*timeout < 0) {
      *timeout = 0;
    }
  }
  return 0;
}


//Internal
//Requires an array of MAX_EVENT units.
int _sparrow_wait(sparrow_t * sp, sparrow_event_t * spev) {
  spev->event = 0;
  int64_t timeout;

  if(sparrow_handle_expired_ot(sp, spev, &timeout)) {
    return 0;
  }

  if(sp->events_len == 0) {
    Dprintf("Timeout: %ld\n", timeout);
    sp->event_cur = 0;
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, timeout);

    if((sp->t_expiry > 0) && (sp->t_expiry - now() < 0)) {
      sp->t_expiry = -1;
      spev->event = 32;
      return 0;
    }
  }
  int i;
  sparrow_socket_t find_sock;
  for( i = sp->event_cur; i < sp->events_len; i++) {
    find_sock.fd = sp->events[i].data.fd; 
    sparrow_socket_t * sock = RB_FIND(fd_rb_t, &(sp->fd_rb_socks), &find_sock);
    int event = sp->events[i].events;

    spev->sock = sock;
    spev->fd = sock->fd;
    spev->parent = sock->parent;

      //On error
      if((event & EPOLLERR) || (event & EPOLLHUP)) {
        Dprintf("EPOLLERR || EPOLLHUP error\n");
        sparrow_socket_close(sp,sock);
        spev->event = 8;
        sp->events[i].events = 0;
        return 0;
      }

    if(event & EPOLLOUT) {
      data_out_t *data_out = &(sock->data_out);
      assert(data_out->len > data_out->cur);
      assert(data_out->len != 0);
      int result = send(sock->fd, data_out->data + data_out->cur, data_out->len - data_out->cur, 0);

      //On error
      if(result < 0) {
        sparrow_socket_close(sp,sock);
        spev->event = 8;
        sp->events[i].events = 0;
        Dprintf("Send error inside _sparrow_wait.\n");
        return 0;
      }

      if(result + data_out->cur == data_out->len) {
        //We remove the socket from the output expiration tree.
        Dprintf("We remove the socket from the output expiration tree.\n");
        RB_REMOVE(ot_rb_t, &(sp->ot_rb_socks), sock);
        sock->out_expiry = -1;
        data_out->len = 0;

        struct epoll_event pevent;
        pevent.data.fd = sock->fd;
        pevent.events = EPOLLIN;
        int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
        if (rc == -1) {
          perror(" epoll_ctl failed to modify a socket to epoll");
          exit(-1);
        }
        spev->event += 2;
        //Clear the bit
        sp->events[i].events &= ~EPOLLOUT;
        return 0;
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
        spev->fd = spev->sock->fd;
        spev->parent = spev->sock->parent;
        spev->event += 16;
        //Clear the bit
        sp->events[i].events &= ~EPOLLIN;
        return 0;
      } else {
        Dprintf("Receiving Socket:\nfd:%d\n",sock->fd);
        
        //If we get data that we did not expect we close the connection. This could also happen when the other closes the connection.
        if(data_in->len == 0) {
          Dprintf("We got data that we did not expect or we received a signal that the connection closed.\nWe are closing the connection.\n");
          sparrow_socket_close(sp,sock);
          spev->event = 8;
          sp->events[i].events = 0;
          return 0;
        }

        int result = recv(sock->fd, data_in->data , data_in->len , 0);

        //On error or connection closed.
        if(result <= 0) {
          Dprintf("Receive error or we received a signal that the connection closed.\nWe are closing the connection.\n");
          sparrow_socket_close(sp,sock);
          spev->event = 8;
          sp->events[i].events = 0;
          return 0;
        }

        spev->cur = result;
        spev->event += 4;
        data_in->len = 0;
        sp->events[i].events &= ~EPOLLIN;
        return 0;
      }
    }

    sp->event_cur++;
  }
  sp->events_len = 0;

  return 1;
}

void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev) {

  while(_sparrow_wait(sp, spev)) {
  }
}




