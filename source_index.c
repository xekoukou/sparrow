<!DOCTYPE html>
<html>
<head>
<title>Sparrow</title>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<script src="Markdown.Converter.js"></script>
<script src="Markdown.Extra.js"></script>
<script src="jquery-2.1.4.min.js"></script>
<link rel="stylesheet" href="highlight/styles/default.css">
<script src="highlight/highlight.pack.js"></script>
<script src="MathJax-master/MathJax.js?config=TeX-AMS-MML_HTMLorMML"></script>
<script src="markdown.js"></script>
<link rel="stylesheet" href="markdown.css">
</head>
<body>
    <div style = "font-size:120%">
       <h1 style='text-align: center'>Sparrow</h1>
       <div class="markdown">


Sparrow is a network library for the idris language with the purpose of permitting fast asynchronous communication whie at the same time allowing protocol verifiability at compile time and being very simple to use.

TODO Explain the main goals of this library in detail. 
a) Easy and cost effective to build.
b) inspectable and understandable by everyone, even people that do not know how to program.
c) Adaptable as time passes and composable. Different parts of the protocol can be different as long as there is no direct interaction between those different parts.


TODO Explain the difficulties of building a network library in a functional programming language in which all data are immutable. Especially, there can be no callbacks. Thus we need to wrap the epoll for linux.


OK the first try would be to simply write a small program that does compile and work.

We will use an object to store the data of our epoll wrapper.

TODO. Sparrow does not buffer data. The application needs to do that itself. The application knows better the specific needs that it has and thus the buffering that it requires. The buffer can be put inside the validation function.

```c
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
#include <time.h>
#include <stdlib.h>
#include <netinet/in.h>
#include <netinet/tcp.h>

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


struct sparrow_t {
  int fd;
  int event_cur;
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  void * fd_tr_socks; // A tree container of sockets ordered by the fd.
  void * to_tr_socks; // A tree container of sockets ordered by the expiry.
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

```


```c

//TODO These function definitions need to be removed.
typedef void * val_fn_t (void ** data_in,size_t * in_len, void * val_data); //The validator function returns the new buffer and int that is to be used
                                                                         // as an imput buffer. The returned data is NULL if we need more validation
                                                                         // or the data themselves that are then sent to be deserialized.
typedef void * deser_fn_t (void *validated_data);
typedef void * ser_fn_t (void * data);

struct data_out_t {
  void * data;
  size_t len;
};

typedef struct data_out_t data_out_t;

struct sparrow_socket_t {
  int listening; //BOOL
  int fd;
  int64_t expiry_min; //The minimum value of the two positive expirys.
  int64_t expiry_in; // A zero expiry means that there is no expiry.
  int64_t expiry_out; // expiry_out is the minimum value of all expiries sent to the socket when sending data, so care must be taken.
  int out_cur;
  data_out_t data_out[MAX_SEND_QUEUE];
  int out_queue_pos;
  int out_queue_frst_free_pos;
  int out_full;
  size_t in_len;
  size_t in_cur;
  size_t in_min;
  void * data_in;
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
  return (s1->expiry_min > s2->expiry_min) - (s1->expiry_min < s2->expiry_min);
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
  assert(tfind(sock, &(sp->fd_tr_socks), cmp_fds) == NULL);
  void *rtsearch = tsearch(sock, &(sp->fd_tr_socks), cmp_fds);
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

sparrow_socket_t * sparrow_socket_bind(sparrow_t * sp, char * port) {
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
  return sock;
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

void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock) {
  close(sock->fd);
  assert(sock->data_in == NULL);
  assert(sock->out_queue_pos == sock->out_queue_frst_free_pos);
  assert(sock->out_full != 1);
  void * isItNull  = tdelete(sock, &(sp->fd_tr_socks), cmp_fds);
  assert(isItNull != NULL);
  tdelete(sock, &(sp->to_tr_socks), cmp_tos);
  free(sock);
}


//internal use only.
void sparrow_socket_accept(sparrow_t * sp, sparrow_socket_t * lsock) {
  int nsfd = accept4(lsock->fd,NULL,NULL,SOCK_NONBLOCK);
  assert(nsfd != -1);
  sparrow_socket_t * sock = sparrow_socket_new(nsfd);
  sparrow_add_socket(sp,sock);
}

void * sparrow_socket_clean(sparrow_t * sp, sparrow_socket_t * sock) {
  void * data_in = sock->data_in;
  sock->data_in = NULL;
  while(sock->out_queue_pos != sock->out_queue_frst_free_pos) {
    free(sock->data_out[sock->out_queue_pos].data);
    sock->out_queue_pos = (sock->out_queue_pos + 1) % MAX_SEND_QUEUE;
  }
  sparrow_socket_close(sp,sock);
  return data_in;
}


sparrow_socket_update_expiry(sparrow_t * sp ,sparrow_socket_t * sock, int64_t expiry) {

  tdelete(sock, &(sp->to_tr_socks), cmp_tos);
  if((expiry < sock->expiry_min) && (expiry > 0)) {
    sock->expiry_min = expiry;
    void *rtsearch = tsearch(sock, &(sp->to_tr_socks), cmp_tos);
    assert(rtsearch == sock);
  }
}

```

Sparrow_wait returns data when all the data have been received.

```c

//Internal use only.
//Requires an array of MAX_EVENT units.
void * sparrow_wait(sparrow_t * sp, int64_t expiry, int *sfd,int *in_min, int *error) {
  if(sp->events_len == 0) {
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, expiry);
    //TODO Handle the errors.
    sp->event_cur = 0;
  }
  int i;
  sparrow_socket_t find_sock;
  for( i = sp->event_cur; i < sp->events_len; i++) {
    sp->event_cur++;
    find_sock.fd = sp->events[i].data.fd; 
    sparrow_socket_t * sock = tfind(&find_sock, &(sp->fd_tr_socks), cmp_fds);
    int event = sp->events[i].events;

    *sfd = sock->fd;
    *error = 0;

    if(event & EPOLLOUT) {
      data_out_t data_out = sock->data_out[sock->out_queue_pos];
      assert(data_out.len > sock->out_cur);
      int result = send(sock->fd, data_out.data + sock->out_cur, data_out.len - sock->out_cur, 0);

      //On error
      if(result < 0) {
        *error = 1;
        return sparrow_socket_clean(sp,sock);
      }

      if(result + sock->out_cur == data_out.len) {
        free(data_out.data);
        sock->out_queue_pos = (sock->out_queue_pos + 1) % MAX_SEND_QUEUE;
        sock->out_cur = 0;
        sock->out_full = 0;

        if(sock->out_queue_pos == sock->out_queue_frst_free_pos) {
          struct epoll_event event;
          event.data.fd = sock->fd;
          event.events = EPOLLIN;
          int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &event);
          if (rc == -1) {
            perror(" epoll_ctl failed to modify a socket to epoll");
            abort();
          }
        }

      } else {
        sock->out_cur += result;
      }
    }

//We do not process more input events unless he have send some output first.
// TODO We need to explain that in the documentation.
    if((event & EPOLLIN) && !(sock->out_full)) {

      if(sock->listening) {
// We accept a new client.
        sparrow_socket_accept(sp, sock);
      } else {

        assert(sock->in_len > sock->in_cur);
        assert(sock->in_min < sock->in_cur);
        int result = recv(sock->fd, sock->data_in + sock->in_cur, sock->in_len - sock->in_cur, 0);

        //On error
        if(result < 0) {
          *error = 1;
          return sparrow_socket_clean(sp,sock);
        }

        if(result + sock->in_cur >= sock->in_min) {
          *in_min = result + sock->in_cur;

          sock->in_cur = 0;
          sock->in_len = 0;
          sock->in_min = 0;

          return sock->data_in;
        } else {
          sock->in_cur += result;
        }
      }
    }

  }
  sp->events_len = 0;

  return sparrow_wait(sp, expiry, sfd, in_min,error);
}

void  sparrow_send( sparrow_t * sp, int fd, void * data, size_t len, int64_t timeout) {
  assert(timeout >= 0);

  sparrow_socket_t find_sock;
  find_sock.fd = fd;
  sparrow_socket_t * sock = tfind(&find_sock, &(sp->fd_tr_socks), cmp_fds);
  assert(sock != NULL);
  assert(sock->out_full != 1);
  data_out_t * data_out = & sock->data_out[sock->out_queue_frst_free_pos];
  data_out->data = data;
  data_out->len = len;
  sock->out_queue_frst_free_pos = (sock->out_queue_frst_free_pos + 1) / MAX_SEND_QUEUE ;
  if(sock->out_queue_pos == sock->out_queue_frst_free_pos) {
    sock->out_full = 1;       
  }

  int64_t expiry = timeout + now();
  if(expiry < expiry_out
  sock->expiry_out = expiry;
  if((expiry < sock->expiry_min) && (expiry > 0)) {
    sock->expiry_min = expiry;
  }
}

void sparrow_recv( sparrow_t * sp, int fd, void *buf, size_t len, size_t min_len, int64_t timeout) {
  assert(timeout >= 0);

  sparrow_socket_t find_sock;
  find_sock.fd = fd;
  sparrow_socket_t * sock = tfind(&find_sock, &(sp->fd_tr_socks), cmp_fds);
  assert(sock != NULL);
  assert(sock->in_len == 0);
  assert(sock->expiry_in == -1);

  sock->in_len = len;
  sock->in_min = min_len;
  sock->data_in = buf;

  int64_t expiry = timeout + now();
  sock->expiry_in = expiry;

  if((expiry < sock->expiry_min) && (expiry > 0)) {
    sock->expiry_min = expiry;
  }
}

```



       </div>
    </div>
</body>
</html>
