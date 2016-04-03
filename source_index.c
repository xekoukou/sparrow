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
#include <stdlib.h>
#include <netinet/in.h>
#include <netinet/tcp.h>

#define MAX_EVENTS 32
#define OUTPUT_MAX_DELAY 40 //in milliseconds. We wait that much before sending new data if we do not have much data.
#define OUTPUT_MAX_BUFF (1500 - 68) // The ethernet MTU is 1500 bytes minus the IP/TCP headers.
#define MAX_SEND_QUEUE 10


struct sparrow_t {
  int fd;
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
  return sp;
}

```


```c

struct sparrow_socket_t {
  int listening; //BOOL
  int fd;
  int timeout;
  int out_len;
  int queue_pos;
  int queue_frst_free_pos;
  int in_len;
  int in_cur;
  void * data_out[MAX_SEND_QUEUE];
  void * data_in;
//TODO (remove) void * (* const val_fn) (void ** data_in,int * in_len, void * val_data); //The validator function returns the new buffer and int that is to be used
                                                                         // as an imput buffer. The returned data is NULL if we need more validation
                                                                         // or the data themselves that are then sent to be deserialized.
//TODO (remove) void * (*const deser_fn) (void *validated_data);
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
void sparrow_socket_init(sparrow_socket_t * sock, int fd) {
  memset(sock,0,sizeof(sparrow_socket_t));
  sock->fd = fd;
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
  sparrow_socket_t * sock = malloc(sizeof(sparrow_socket_t));
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
  sparrow_socket_init(sock,sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  sparrow_socket_listen(sock);
  return sock;
}



sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port) {
  sparrow_socket_t * sock = malloc(sizeof(sparrow_socket_t));
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
  sparrow_socket_init(sock,sfd);
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

void sparrow_socket_accept(sparrow_t * sp, int fd) {
  int nsfd = accept4(fd,NULL,NULL,SOCK_NONBLOCK);
  assert(nsfd != -1);
  sparrow_socket_t * sock = malloc(sizeof(sparrow_socket_t));
  sparrow_socket_init(sock,nsfd);
  sparrow_add_socket(sp,sock);
}

//Internal use only.
//Requires an array of MAX_EVENT units.
int sparrow_wait(sparrow_t * sp, int timeout) {
  int n = epoll_wait(sp->fd, sp->events, MAX_EVENTS, timeout);
  //TODO Handle the errors.
  int i;
  sparrow_socket_t find_sock;
  for( i = 0; i < n; i++) {
    find_sock.fd = sp->events[i].data.fd; 
    sparrow_socket_t * sock = tfind(&find_sock, &(sp->tr_socks), cmp_ints);
    int event = sp->events[i].events;
    
    if(event|EPOLLIN) {
      if(sock->listening) {
        sparrow_socket_accept(sp, sock->fd);
      } else {
         
      }
    }
  }
  return n;
}




```



       </div>
    </div>
</body>
</html>
