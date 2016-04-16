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


TODO. Sparrow does not buffer data. The application needs to do that itself. The application knows better the specific needs that it has and thus the buffering that it requires. The buffer can be put inside the validation function.


# Epoll Wrapper

The first thing that we need to do is to provide a wrap around linux epoll's that simplifies the api for the asynchronous communications. This wrapper needs to be able to do only one thing.

**Given a buffer, the wrapper needs to be able to send or receive data into it unless a timeout expires.**

There is a small difference between a receive and a send though. Because we want to reduce the number of recv system calls, we provide the wrapper a buffer that might be bigger that the data that are available. If the client doesn't send more data
, that would mean that we would never receive the data that the client already sent. To aleviate this problem, we immediately return as much data as we currently have without waiting to fill the buffer.

## Examples

### A simple receive and response Protocol

This example simply has one program binding to the local port and wait to receive one message from the other program. The other program connects , sends the msg and then exits.

First of all, we need to include our library header 'sparrow.h'. Then, we create an object that handles all our asynchronous communications. We bind to the port "9003" and we wait for sparrow to give our first event. We know that one client will connect and transmit one msg, thus we first handle the connection. We use the socket we get from the connection event to ask sparrow to wait for a msg. We need to provide a buffer to sparrow so as to copy the msg. **Keep in mind that we drop data that we do not expect.** After we have received the msg, we print it and exit.

```c simple_test_server.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev);


  if(spev.event & 16) {
    char *data = malloc(50);
    sparrow_recv(sp, spev.sock, data,50);
  }
  //New Msg
  sparrow_wait(sp,&spev);
  if(spev.event & 4) {
    char * data_out = sparrow_socket_data_in(spev.sock);
    printf("Received :\n%s\n",data_out);
    free(data_out);
  }

  sparrow_close(&sp);
  return 0;
}

```

The client simply sents a Msgs. Waits till it sparrow tells it that it sent it and exits.

```c simple_test_client.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  char *data = malloc(50);
  sprintf(data,"Hello there!");

  sparrow_event_t spev;
  sparrow_send(sp, sock, data, 50, &spev);

  sparrow_wait(sp,&spev);
  printf("I sent : %s",data);
  
  sparrow_close(&sp);
  return 0;
}

```


### A Timeout Example

Everything looks great till now, but reality is different than the constructs we use to have in our heads. We might expect a msg to come but that msg might never come. We need to be able to cancel our order to receive or send a msg. The way we detect failures is by waiting for a period of time before we give up. That is the meaning of setting a timeout. Sparrow only allows a single timeout per socket, thus we need to update our timeout as we give a new receive or send command, or as soon as the timeout expires and there are pending requests. Keep in mind that we can concurrently have a single receive and a single send request at the same time.

Sparrow requires the precise time that a request will expire. To find the current time, we call the 'now' function.

```c timeout_server.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev);

  if(spev.event & 16) {
    char *data = malloc(50);
    sparrow_socket_set_timeout(sp, spev.sock, now() + 5000);
    sparrow_recv(sp, spev.sock, data,50);
  }

  sparrow_wait(sp,&spev);
  if(spev.event & 8) {
    printf("Recv timeout expired\n");
    return -1;
  }

  return 0;
}

```

Our client does not send any msgs so as to test that sparrow returns an event when the timeout expires.

```c timeout_client.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  sleep(7);
  sparrow_close(&sp);
  return 0;
}

```

### Network Errors

Network errors do happen. The client might close the connection before we finish our communication protocol. Other errors might happen as well. Sparrow does not distinguish between errors. It doesn't also distinguish between errors and timeouts.
Timeouts lead to the closure of the connection as any other error. Sparrow returns the same event ('8') for both.


## Time

We will get time from the system. Because clock_gettime is an expensive system call, we use the Time Stamp Counter to determine whether enough time has passed till our last call to get the time. If more than 1/2 of our clock_precision has passed, we check the system time again. 

The reason we do not use the Time Stamp Counter to track time is because TSC counts the cycles of a cpu core. With the current turbocharge technology, the frequency of a processor can change dynamically, thus making the time imprecise. Moreover, our application can be migrated to a different core which has a different number of cycles.


```c time.c
#include <time.h>
#include <stdint.h>
#include <assert.h>

// One millisecond clock precision.
#define CLOCK_PRECISION 1000000

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


```

## Sparrow Internal Data Structs

Output data buffers need to contain the point till which they had already sent because the network might not allow all the data to be transmitted at once. Both output and input data buffers need to know their length for obvious reasons:

```c sparrow.c.dna
function data_buffer_definitions() {
./!dots(1)

struct data_out_t {
  size_t cur;
  void * data;
  size_t len;
};

struct data_in_t { 
  void * data;
  size_t len;
};

typedef struct data_out_t data_out_t;
typedef struct data_in_t data_in_t;

./!dots(-1)
}
```

The socket needs to know 

1. if it is listening for connections or not,
2. its file descriptor obviously as the fd is used to perform system calls to the operating system,
3. an expiration time that represents the time till we wish to wait to receive or send data. 

The socket will also contain pointers to the buffers and two fields that are used to order all the sockets according to the file descriptor and the expiry time. We will use those orderings to retrieve the apropriate socket when a new event occurs or a timeout has expired.

It is important to note that we only use one expiry time for a single socket. It is up to the higher level abstraction (serializer/multiplexer) to update this expiry time for the next event it wants to track for that socket.

```c sparrow.c.dna
function sparrow_socket_definition() {
./!dots(1)
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
./!dots(-1)
}
```

The sparrow struct keeps two trees that contain the sockets, one in expiry time order and the other in file descriptor order.
It caches all the events that have occured and the expired sockets that have ,you know, expired. We do the caching because we will only return one event at a time. Thus, when a new call happens, we send one of the cached events. The sparrow struct also contains the file descriptor of epoll.

```c sparrow.c.dna
function sparrow_definition() {
./!dots(1)
struct sparrow_t {
  int fd;
  int event_cur;
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  struct fd_rb_t fd_rb_socks; // A tree container of sockets ordered by the fd.
  struct to_rb_t to_rb_socks; // A tree container of sockets ordered by the expiry.
  size_t already_expired;
};
./!dots(-1)
}
```

## Ordering of Sockets

We use Niels Provos code to generate Red Black trees to order our sockets. The relevant code is here.

```c sparrow.c.dna
function tree_generation() {
./!dots(1)

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
RB_HEAD (fd_rb_t, sparrow_socket_t);

RB_GENERATE (to_rb_t, sparrow_socket_t, to_field,cmp_tos);
RB_GENERATE (fd_rb_t, sparrow_socket_t, fd_field, cmp_fds);


./!dots(-1)
}
```


```c sparrow.c.dna
./!dots(1)

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
#define MAX_SEND_QUEUE 10
#define MAX_INPUT_DELAY 20


./!dots(-1)
data_buffer_definitions(); 

sparrow_socket_definition();

tree_generation();

sparrow_definition();
./!dots(1)


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

```


```c sparrow.c.dna

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
    abort();
  }
  sparrow_socket_t * sock = sparrow_socket_new(sfd);
  freeaddrinfo (ret_addr);
  sparrow_socket_set_non_blocking(sock); 
  sparrow_add_socket(sp,sock);
  return sock;
}

//Internal
void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock) {
  printf("Connection closed: %d", sock->fd);
  close(sock->fd);
//  assert(sock->data_in.len == 0);
  RB_REMOVE(fd_rb_t, &(sp->fd_rb_socks), sock);
  RB_REMOVE(to_rb_t, &(sp->to_rb_socks), sock);
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


```

Sparrow_wait returns data when the input buffer is full or there are no more data to receive.
It also returns when all the outpul buffer has been sent.

```c sparrow.c.dna

//Internal use only
int sparrow_handle_expired(sparrow_t * sp, sparrow_event_t *spev, int64_t *timeout){
  sparrow_socket_t * sock = RB_MIN(to_rb_t, &(sp->to_rb_socks));
  if(sp->already_expired > 0) {
    RB_REMOVE(to_rb_t, &(sp->to_rb_socks), sock);
    sp->already_expired--;
    spev->sock = sock;
    spev->event += 8;
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
      spev->sock = sock;
      spev->event += 8;
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
  int64_t timeout;

  if(sparrow_handle_expired(sp, spev, &timeout)) {
    return 0;
  }

  if(sp->events_len == 0) {
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, timeout);
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
        spev->event = 8;
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
        spev->event = 8;
        Dprintf("Send error inside _sparrow_wait.\n");
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
        
        //If we get data that we did not expect we close the connection. This could also happen when the other closes the connection.
        if(data_in->len == 0) {
          Dprintf("We got data that we did not expect or we received a signal that the connection closed.\nWe are closing the connection.\n");
          spev->event = 8;
          sparrow_socket_close(sp,sock);
          return 0;
        }

        int result = recv(sock->fd, data_in->data , data_in->len , 0);

        //On error or connection closed.
        //TODO We need to handle closed connections differently, possibly automatically reconnecting.
        if(result <= 0) {
          Dprintf("Receive error or we received a signal that the connection closed.\nWe are closing the connection.\n");
          spev->event = 8;
          sparrow_socket_close(sp,sock);
          return 0;
        }

        spev->cur = result;
        spev->event += 4;
        data_in->len = 0;
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

int sparrow_send( sparrow_t * sp, sparrow_socket_t * sock, void * data, size_t len, sparrow_event_t * spev) {
  assert(data!=NULL);
  spev->sock = sock;
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
    spev->event = 2;
    return 1;
  }

}

void sparrow_recv( sparrow_t * sp, sparrow_socket_t * sock, void *data, size_t len) {

  Dprintf("Asking to receive socket:\nfd: %d\n",sock->fd);
  data_in_t *data_in = &(sock->data_in);
  assert(data_in->len == 0);
  data_in->data = data;
  data_in->len = len;
}

void * sparrow_socket_data_in(sparrow_socket_t *sock) {
  void *data = sock->data_in.data; 
  return data;
}

void * sparrow_socket_data_out(sparrow_socket_t *sock) {
  void *data = sock->data_out.data; 
  return data;
}
```

```c sparrow.h
#ifndef _SPARROW_H_
#define _SPARROW_H_

#include <unistd.h>
#include <stdlib.h>

#if (defined DEBUG_LOG) 
  #define Dprintf(x, ...) printf(x, ##__VA_ARGS__)
#else 
  #define Dprintf(x, ...)
#endif  

typedef struct sparrow_t sparrow_t;
typedef struct sparrow_socket_t sparrow_socket_t;

struct sparrow_event_t {
  sparrow_socket_t * sock;
  size_t cur;
  int event;
};

typedef struct sparrow_event_t sparrow_event_t;

sparrow_t * sparrow_new(void);

void sparrow_socket_bind(sparrow_t * sp, char * port);

sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port); 

void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev);

void sparrow_socket_set_timeout(sparrow_t * sp, sparrow_socket_t *sock, int64_t expiry);

int sparrow_send( sparrow_t * sp, sparrow_socket_t *sock, void * data, size_t len, sparrow_event_t * spev);

void sparrow_recv( sparrow_t * sp, sparrow_socket_t *sock, void *data, size_t len);

void sparrow_close(sparrow_t ** sp);
//TODO Remove these, the serializer/multiplexer is supposed to keep a pointer to its buffer.
void * sparrow_socket_data_in(sparrow_socket_t *sock);
void * sparrow_socket_data_out(sparrow_socket_t *sock);
int64_t now(void);

#endif
```





```c thr_server.c
#include "sparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9001");
  sparrow_event_t spev;


  char *data = malloc(50);


  sparrow_wait(sp,&spev);
  int64_t time = now();
    if(spev.event & 8) {
      printf("An error occured\n");
      return -1;
    }
    if(spev.event & 16) {
      sparrow_recv(sp, spev.sock, data,50);
    }



  int i = 0;
  while (i < 2000000) {
    sparrow_wait(sp,&spev);
    if(spev.event & 8) {
      printf("An error occured\n");
      break;
    }
    if(spev.event & 4) {
      if(spev.cur == 50) {
        char * data_in = sparrow_socket_data_in(spev.sock);
        Dprintf("Received :\n%s\n",data_in);
        sparrow_recv(sp, spev.sock, data,50);
        i++;
      }
    }
  }
  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Msgs received: %d\n", i);

  return 0;
}

```
```c thr_client.c
#include "sparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9001");
  int i = 0;
  sparrow_event_t spev;
  spev.event = 0;
  int sent = 1;
  char *data = malloc(50);
  while(i < 2000000) {
    if((spev.event & 2) || (sent == 1)) {

      sprintf(data,"Hello there!");
      sent = sparrow_send(sp, sock, data, 50, &spev);
      if(spev.event & 8) {
        Dprintf("An error occured");    
        break;
      }
    }
    if(sent == 0) {
      sparrow_wait(sp,&spev);
    }

    if((spev.event & 2) || (sent == 1)) {
      char * data_out = sparrow_socket_data_out(sock);
      Dprintf("Sent :\n%s\n",data_out);
      i++;
    }
  }

  sparrow_close(&sp);
  exit(0);
}

```


       </div>
    </div>
</body>
</html>
