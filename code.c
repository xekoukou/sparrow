#define _GNU_SOURCE

#include <sys/epoll.h>
#include <errno.h>
#include <search.h>
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

#define MAX_EVENTS 32
// #define MAX_DELAY 40 //in milliseconds. We wait that much before sending new data if we do not have much data.
// #define MAX_BUFF (1500 - 68) // The ethernet MTU is 1500 bytes minus the IP/TCP headers.
#define MAX_SEND_QUEUE 10


struct sparrow_t {
  int fd;
  int event_cur;
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  void * tr_socks; // A tree container of sockets.
};

typedef struct sparrow_t sparrow_t;

sparrow_t * sparrow_init(sparrow_t * sp) {
  int fd = epoll_create1 (0);
  if (fd == -1) {
    perror("epoll_create1 failed to create epoll.");
    abort();
  }
  sp->fd = fd;
  sp->events_len = 0;
  return sp;
}


//TODO These function definitions need to be removed.
typedef void * val_fn_t (void ** data_in,int * in_len, void * val_data); //The validator function returns the new buffer and int that is to be used
                                                                         // as an imput buffer. The returned data is NULL if we need more validation
                                                                         // or the data themselves that are then sent to be deserialized.
typedef void * deser_fn_t (void *validated_data);
typedef void * ser_fn_t (void * data);

struct data_out_t {
  void * data;
  int len;
};

typedef struct data_out_t data_out_t;

struct sparrow_socket_t {
  int listening; //BOOL
  int fd;
  int timeout;
  int out_cur;
  data_out_t data_out[MAX_SEND_QUEUE];
  int out_queue_pos;
  int out_queue_frst_free_pos;
  int in_len;
  int in_cur;
  int in_min;
  void * data_in;
};

typedef struct sparrow_socket_t sparrow_socket_t;


int cmp_ints(const void * sock1, const void * sock2) {
  const sparrow_socket_t * s1 = (const sparrow_socket_t *) sock1;
  const sparrow_socket_t * s2 = (const sparrow_socket_t *) sock2;
  return (s1->fd > s2->fd) - (s1->fd < s2->fd);
}


//internal use only
void sparrow_add_socket(sparrow_t * sp, sparrow_socket_t *sock) {
  int result;
  struct epoll_event event;
  event.data.fd = sock->fd;
  event.events = EPOLLIN;
  result = epoll_ctl (sp->fd, EPOLL_CTL_ADD, sock->fd, &event);
  if (result == -1) {
    perror(" epoll_ctl failed to add a socket to epoll");
    abort();
  }
  assert(tfind(sock, &(sp->tr_socks), cmp_ints) == NULL);
  void *rtsearch = tsearch(sock, &(sp->tr_socks), cmp_ints);
  assert(rtsearch == sock);
}

//internal use only.
sparrow_socket_t * sparrow_socket_new(int fd) {
  sparrow_socket_t * sock = malloc(sizeof(sparrow_socket_t));
  memset(sock,0,sizeof(sparrow_socket_t));
  sock->fd = fd;
  return sock;
}

//internal use only
sparrow_socket_t * sparrow_socket_set_non_blocking(sparrow_socket_t * sock) {
  int flags, result;

  flags = fcntl (sock->fd, F_GETFL, 0);
  if (flags == -1) {
    perror ("fcntl failed to perform an action.");
    abort();
  }

  flags |= O_NONBLOCK;
  result = fcntl (sock->fd, F_SETFL, flags);
  if (result == -1) {
    perror ("fcntl failed to perform an action.");
    abort();
  }
  return sock;
}

//internal function
sparrow_socket_t * sparrow_socket_listen(sparrow_socket_t * sock) {
  int result = listen(sock->fd,SOMAXCONN);
  if ( result == -1 ) {
    perror("The socket failed to listen.");
    abort();
  }
  sock->listening = 1;
  return sock;
}

sparrow_socket_t * sparrow_socket_bind(sparrow_t * sp, char * port) {
  struct addrinfo hints = {0};
  struct addrinfo *ret_addr;
  int result, sfd;
  int flag = 1;

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  result = getaddrinfo (NULL, port, &hints, &ret_addr);
  assert(result == 0);

  sfd = socket (ret_addr->ai_family, ret_addr->ai_socktype, ret_addr->ai_protocol);
  assert(sfd != -1);
  
  result = setsockopt(sfd,IPPROTO_TCP,TCP_NODELAY, (char *) &flag,sizeof(int));
  assert(result == 0);

  result = bind (sfd, ret_addr->ai_addr, ret_addr->ai_addrlen);
  if (result != 0) {
    close (sfd);
    abort();
  }
  sparrow_socket_t * sock = sparrow_socket_new(sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  sparrow_socket_listen(sock);
  return sock;
}



sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port) {
  struct addrinfo hints = {0};
  struct addrinfo *ret_addr;
  int result, sfd;

  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  result = getaddrinfo (address, port, &hints, &ret_addr);
  assert(result == 0);

  sfd = socket (ret_addr->ai_family, ret_addr->ai_socktype, ret_addr->ai_protocol);
  assert(sfd != -1);
  result = connect (sfd, ret_addr->ai_addr, ret_addr->ai_addrlen);
  if (result != 0) {
    close (sfd);
    abort();
  }
  sparrow_socket_t * sock = sparrow_socket_new(sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  return sock;
}

void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock) {
  close(sock->fd);
  assert(sock->data_in == NULL);
  void * isItNull  = tdelete(sock, &(sp->tr_socks), cmp_ints);
  assert(isItNull != NULL);
  free(sock);
}


//internal use only.
void sparrow_socket_accept(sparrow_t * sp, sparrow_socket_t * lsock) {
  int nsfd = accept4(lsock->fd,NULL,NULL,SOCK_NONBLOCK);
  assert(nsfd != -1);
  sparrow_socket_t * sock = sparrow_socket_new(nsfd);
  sparrow_add_socket(sp,sock);
}


//Internal use only.
//Requires an array of MAX_EVENT units.
void * sparrow_wait(sparrow_t * sp, int timeout, int *sfd,int *in_min) {
  if(sp->events_len == 0) {
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, timeout);
    //TODO Handle the errors.
    sp->event_cur = 0;
  }
  int i;
  sparrow_socket_t find_sock;
  for( i = sp->event_cur; i < sp->events_len; i++) {
    find_sock.fd = sp->events[i].data.fd; 
    sparrow_socket_t * sock = tfind(&find_sock, &(sp->tr_socks), cmp_ints);
    int event = sp->events[i].events;
    
    if(event & EPOLLIN) {

      if(sock->listening) {
// We accept a new client.
        sparrow_socket_accept(sp, sock);
      } else {

        assert(sock->in_len > sock->in_cur);
        assert(sock->in_min < sock->in_cur);
        int result = recv(sock->fd, sock->data_in + sock->in_cur, sock->in_len - sock->in_cur, 0);
        assert(result > 0); //TODO we need to throw an error when the connection was shutdown. (result =0)
        if(result + sock->in_cur >= sock->in_min) {
          *in_min = result + sock->in_cur;

          sock->in_cur = 0;
          sock->in_len = 0;
          sock->in_min = 0;

          if(i == sp->events_len) {
            sp->events_len = 0;
          }
          *sfd = sock->fd;
          return sock->data_in;
        } else {
          sock->in_cur += result;
        }
      }
    }

    if(event & EPOLLOUT) {
      assert(sock->out_queue_pos != sock->out_queue_frst_free_pos);
      data_out_t data_out = sock->data_out[sock->out_queue_pos];
      assert(data_out.len > sock->out_cur);
      int result = send(sock->fd, data_out.data + sock->out_cur, data_out.len - sock->out_cur, 0);
      assert(result > 0);

      if(result + sock->out_cur == data_out.len) {
        free(data_out.data);
        sock->out_queue_pos = (sock->out_queue_pos + 1) % MAX_SEND_QUEUE;
        sock->out_cur = 0;

        if(sock->out_queue_pos == sock->out_queue_frst_free_pos) {
          struct epoll_event event;
          event.data.fd = sock->fd;
          event.events = EPOLLIN;
          result = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &event);
          if (result == -1) {
            perror(" epoll_ctl failed to modify a socket to epoll");
            abort();
          }
        }

      } else {
        sock->out_cur += result;
      }
    }
  }
  sp->events_len = 0;
  return sparrow_wait(sp, timeout, sfd, in_min);
}

// void  sparrow_send()



