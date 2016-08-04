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


# Interleaved Sparrow 

```c isparrow.h
#ifndef _ISPARROW_H_
#define _ISPARROW_H_


#endif
```

```c isparrow.c.dna
./!dots(1)

#include"bsparrow.h"
#include"msparrow.h"
#include<sodium.h>
#include<assert.h>
#include"tree.h"

struct isparrow_timeout_t {
  int64_t expiry;
  int fd;
  unsigned char path_hash[crypto_generichash_BYTES];
  uint64_t counter;
  RB_ENTRY (isparrow_timeout_t) tm_field;
};

typedef struct isparrow_timeout_t isparrow_timeout_t;

int cmp_tm(const void * tm1_, const void * tm2_) {
  const isparrow_timeout_t * tm1 = (const isparrow_timeout_t *) tm1_;
  const isparrow_timeout_t * tm2 = (const isparrow_timeout_t *) tm2_;
  int64_t xp = (tm1->expiry > tm2->expiry) - (tm1->expiry < tm2->expiry);
  if(xp != 0) {
    return xp;
  } else {
    int fd = (tm1->fd > tm2->fd) - (tm1->fd < tm2->fd);
    if (fd != 0) {
      return fd;
    } else {
      return memcmp(tm1->path_hash, tm2->path_hash, crypto_generichash_BYTES);
    }
  }
}

RB_HEAD (tm_rb_t, isparrow_timeout_t);
RB_GENERATE (tm_rb_t, isparrow_timeout_t, tm_field, cmp_tm);

struct isparrow_t {
  struct tm_rb_t tm_rb;
};

typedef struct isparrow_t isparrow_t;
//4 bytes for the counter
//32 bytes for the path crypto_generichash


//TODO Should we return the path or just the hash?
isparrow_timeout_t * isparrow_add_path(isparrow_t * isp, int fd, unsigned char * prev_hash, uint64_t new_local_id) {
  isparrow_timeout_t * tm = scalloc(1, sizeof(isparrow_timeout_t));
  tm->fd = fd;
  tm->expiry = -1;
  tm->counter = 0;

  size_t all_together_length = crypto_generichash_BYTES + sizeof(int64_t);
  unsigned char all_together[all_together_length];
  if(prev_hash !=NULL) {
    memcpy(all_together, prev_hash, crypto_generichash_BYTES);
    memcpy(all_together + crypto_generichash_BYTES, (unsigned char *) &new_local_id, sizeof(new_local_id));
    crypto_generichash(tm->path_hash, crypto_generichash_BYTES, all_together, all_together_length, NULL, 0);
  } else {
    crypto_generichash(tm->path_hash, crypto_generichash_BYTES,(unsigned char *) &new_local_id, sizeof(uint64_t), NULL, 0);
  }

  void *rtsearch = RB_INSERT(tm_rb_t, &(isp->tm_rb), tm);
  assert(rtsearch == NULL);

  return tm;
}

int compare_hashes(const void *pointer1,const void *pointer2) {
  unsigned char * h1 = *((unsigned char **) pointer1);
  unsigned char * h2 = *((unsigned char **) pointer2);

  return memcmp(h1, h2, crypto_generichash_BYTES);
}


isparrow_timeout_t * isparrow_merge_paths(isparrow_t * isp,int fd, isparrow_timeout_t **tms, int length) {

  qsort(tms, length, sizeof(void *), &compare_hashes);

  isparrow_timeout_t * tm = scalloc(1, sizeof(isparrow_timeout_t));
  tm->fd = fd;
  tm->expiry = -1;
  tm->counter = 0;
  assert(tm->path_hash[0] == 0);

  size_t all_together_length = 2 * crypto_generichash_BYTES;
  unsigned char all_together[all_together_length];

  int i;
  for(i = 0; i < length; i++) {
    memcpy(all_together, tms[i], crypto_generichash_BYTES);
    memcpy(all_together + crypto_generichash_BYTES, tm->path_hash, crypto_generichash_BYTES);
    crypto_generichash(tm->path_hash, crypto_generichash_BYTES, all_together, all_together_length, NULL, 0);
  }

  void *rtsearch = RB_INSERT(tm_rb_t, &(isp->tm_rb), tm);
  assert(rtsearch == NULL);

  return tm;
}



void isparrow_prep_send(isparrow_t *isp, char * data, int64_t counter, unsigned char * prev_hash, uint64_t new_local_id) {
  size_t all_together_length = crypto_generichash_BYTES + sizeof(int64_t);
  unsigned char all_together[all_together_length];
  memcpy(all_together, prev_hash, crypto_generichash_BYTES);
  memcpy(all_together + crypto_generichash_BYTES, &new_local_id, sizeof(new_local_id));
  crypto_generichash((unsigned char *) data, crypto_generichash_BYTES, all_together, all_together_length, NULL, 0);

//  void *rtsearch = RB_INSERT(fd_rb_t, &(sp->fd_rb_socks), sock);
//  assert(rtsearch == NULL);
//  memcpy(data + crypto_generichash_BYTES, counter + 1
}


//It needs to either return a timeout event or return the hash of the path of the socket.
void isparrow_route_msg(isparrow_t * isp, int fd, sparrow_msg_t *msg) {
   
}



./!dots(-1)
```

# Salty MSG Cryptography

//TODO In the future

```c csparrow.h
#ifndef _CSPARROW_H_
#define _CSPARROW_H_

#include<libsodium.h>


#endif
```

```c csparrow.c

struct csparrow_t {
  
}


```


# Simple MSG delimination

The simple message delimination is very.. simple. We.. simply add a 64bit number at the beginning of each message that indicates the size of the msg.

```c msparrow.h
#ifndef _MSPARROW_H_
#define _MSPARROW_H_

#include "bsparrow.h"
#include<string.h> 
#include<stdint.h> 

struct sparrow_msg_t {
  char * data;
  int64_t len;
};

typedef struct sparrow_msg_t sparrow_msg_t;

void msparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock);

int msparrow_get_msg(bsparrow_t * bsp, bsparrow_event_t * bspev, sparrow_msg_t * msg);

void msparrow_print_msg(sparrow_msg_t *msg);
char * sparrow_msg_get_data(sparrow_msg_t * msg);
int64_t sparrow_msg_get_length(sparrow_msg_t * msg);
#endif
```

```c msparrow.c.dna
./!dots(1)
#include "msparrow.h"
#include "bsparrow.h"
#include<string.h> 
#include<stdio.h> 
#include<assert.h> 

void msparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  bsparrow_recv(bsp, bsock, 8);
}

./!dots(-1)
function do_we_have_all_data() {
./!dots(+1)

if(*size + 8 > bspev->total_length) {
  return NULL;
} else {
  data = scalloc(1, *size);
}

./!dots(-1)
}
./!dots(+1)

//Internal use only.
void * get_data(bsparrow_event_t * bspev,  int64_t * size) {
  char * data = NULL;

  size_t position_of_next_copy = 0;
  size_t eight_position = 0;
  size_t position_on_last_buffer = 0;
  buffer_list_t * iter = bspev->list;

  if(bspev->first_buffer_length > 0) {
     if(8 > bspev->first_buffer_length) {
      memcpy(size, bspev->first_buffer, bspev->first_buffer_length);
      eight_position = bspev->first_buffer_length;
    } else {
      memcpy(size, bspev->first_buffer, 8);
./!dots(-1)
.      @{do_we_have_all_data()}
./!dots(+1)
      goto step_zero;
    }
  }

  if(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);    //length here must be big enough to have the 8 bits.
    assert(length >= (8 - eight_position));
    memcpy((char *) size + eight_position, buffer, 8 - eight_position);
./!dots(-1)
.    @{do_we_have_all_data()}
./!dots(+1)
    memcpy(data, buffer + (8 - eight_position), length - (8 - eight_position));   
    position_of_next_copy = length - (8 - eight_position);
    goto step_one;
  }

  assert(bspev->last_buffer_length >= 8 - eight_position);

  memcpy((char *) size + eight_position, bspev->last_buffer, 8 - eight_position);
./!dots(-1)
.  @{do_we_have_all_data()}
./!dots(+1)
  position_on_last_buffer = 8 - eight_position;
  goto step_two;


step_zero: ;

  if(*size > bspev->first_buffer_length - 8) {
    memcpy(data, bspev->first_buffer + 8, bspev->first_buffer_length - 8);
    position_of_next_copy = bspev->first_buffer_length - 8;
  } else {
    memcpy(data, bspev->first_buffer + 8, *size);
    return data;
  }

step_one: ;

  while(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);
    memcpy(data + position_of_next_copy, buffer, length);
    position_of_next_copy += length;
  }

step_two: ;
 
  if(bspev->last_buffer_length) {
    memcpy(data + position_of_next_copy, bspev->last_buffer + position_on_last_buffer, *size - position_of_next_copy);
  }

  return data;
}

int msparrow_get_msg(bsparrow_t * bsp, bsparrow_event_t * bspev, sparrow_msg_t * msg) {
  assert(bspev->event == 4);
  
  if(bspev->total_length < 8) {
    bsparrow_recv(bsp, bspev->bsock, 8);
    return 0;
  } else {
    msg->data = get_data(bspev, &(msg->len));
    if(msg->data == NULL) {
      bsparrow_recv(bsp, bspev->bsock, msg->len + 8);
      return 0;
    } else {
      bsparrow_got_some(bsp, bspev->bsock, msg->len + 8);
      return 1; 
    }
  }
}

void msparrow_print_msg(sparrow_msg_t *msg) {

  printf("Received :\n\n%.*s\n\n", (int) msg->len, msg->data);
  printf("Length : %ld\n", msg->len);

  free(msg->data);

}

char * sparrow_msg_get_data(sparrow_msg_t * msg) {
  return msg->data;
}

int64_t sparrow_msg_get_length(sparrow_msg_t * msg) {
  return msg->len;
}
./!dots(-1)
```

## Examples {#msparrow_examples}

### Throughput Test {#Msparrow_throughput_Test} 

```c mthr_server.c
#include "msparrow.h"
#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>


void printmsg(sparrow_msg_t msg) {

  Dprintf("Received :\n\n%s\n\n", msg.data);
  Dprintf("Length : %ld\n", msg.len);

  free(msg.data);

}

void get_msg(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev, sparrow_msg_t * msg) {
  msparrow_recv(bsp, bsock);

  while(1) {
    bsparrow_set_timeout(bsp, 5000);
    bsparrow_wait(bsp, bspev, 0);

    if(bspev->event & 4) {
      bsparrow_set_timeout(bsp, -1);
      if(msparrow_get_msg(bsp, bspev, msg)) {
        return;
      }
    }

    if(bspev->event & 32) {
      printf("timeout error. The client must have crushed");
      exit(-1);
    }
  }
}


void results(int i, int64_t time, int msg_size) {
  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Length : %d\n", msg_size);
  printf("Msgs received: %d\n", i);
}

int main(int argc, char ** argv) {
  
  assert(argc == 3);
  uint64_t msg_size = atoi(argv[1]);
  int loop_length = atoi(argv[2]);

  bsparrow_t * bsp = bsparrow_new(50000, 4000, 2, 2, 1, "9003");

  bsparrow_event_t bspev;
  bsparrow_socket_t * bsock;
  bsparrow_wait(bsp, &bspev, 0);

  if(bspev.event & 16) {
    bsock = bspev.bsock;
    bsparrow_socket_assign_id(bsock, 1);
  } else {
    exit(-1);
  }
  
  sparrow_msg_t msg;
  int j = 0;
  int64_t time = now();
  while(j < loop_length) {
    int i = 0;
    while(i < 10000) {
      if(i == 5000) {
        char *data = scalloc(1, 100);
        uint64_t temp = 92;
        memcpy(data, &temp, 8);
        sprintf(data + 8,"Got 50, need mooooreee!");
        bsparrow_send(bsp, bsock, &data, 100);
        Dprintf("I am sending an aknowledge msg at msg number: %lu\n", j*100 + 50);
      }
      get_msg(bsp, bsock, &bspev, &msg); 
    
      Dprintf("i: %d\n", i); 
      Dprintf("Remaining length: %lu\n", bspev.total_length -msg_size);
      printmsg(msg);
      i++;
    }
    Dprintf("j: %d\n", j); 
    Dprintf("Remaining length: %lu\n", bspev.total_length -msg_size);
    j++;
  }

  printf("Sending: Got them all, thanks!\n");
  char *data = scalloc(1, 100);
  uint64_t temp = 92;
  memcpy(data, &temp, 8);
  sprintf(data + 8, "Got them all, thanks!");
  bsparrow_send(bsp, bsock, &data, 100);
  results(j*10000, time, msg_size);

  bsparrow_destroy(bsp);
  return 0;
}

```


```c mthr_client.c
#include "msparrow.h"
#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

void printmsg(sparrow_msg_t msg) {

  Dprintf("Received :\n\n%s\n\n", msg.data);
  Dprintf("Length : %ld\n", msg.len);

  free(msg.data);

}

void get_msg(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev, sparrow_msg_t * msg) {
  msparrow_recv(bsp, bsock);

  while(1) {
    bsparrow_set_timeout(bsp, 5000);
    bsparrow_wait(bsp, bspev, 0);

    if(bspev->event & 4) {
      bsparrow_set_timeout(bsp, -1);
      if(msparrow_get_msg(bsp, bspev, msg)) {
        return;
      }
    }

    if(bspev->event & 32) {
      printf("timeout error. The client must have crushed");
      exit(-1);
    }
  }
}


int main(int argc, char ** argv) {
  
  assert(argc == 3);
  int msg_size = atoi(argv[1]);
  int loop_length = atoi(argv[2]);

  bsparrow_t * bsp = bsparrow_new(50000, 4000, 15001, 2, 0, NULL);
  bsparrow_socket_t * bsock = bsparrow_socket_connect(bsp, 1, "127.0.0.1", "9003");
  
  int j = 0;
  while(j < loop_length) {
    int i = 0;
    while(i < 10000) {
      char *data = scalloc(1, msg_size);
      uint64_t temp = msg_size - 8;
      memcpy(data, &temp, 8);
      sprintf(data + 8,"Hello there!");
      bsparrow_send(bsp, bsock, &data, msg_size);
      Dprintf("I: %d\n", i);
      i++;
    }

    //Getting an unknowledge msg after every 100 msgs
    bsparrow_event_t bspev ={0};
    sparrow_msg_t msg;
    get_msg(bsp, bsock, &bspev, &msg);
    printmsg(msg);
    Dprintf("J: %d\n", j);
    j++;

  }
  printf("I finished sending the data.\n");


  //Getting an unknowledge msg
  bsparrow_event_t bspev ={0};
  sparrow_msg_t msg;
  get_msg(bsp, bsock, &bspev, &msg);
  printmsg(msg);

  bsparrow_destroy(bsp);
  return 0;

}

```


# Buffered Sparrow {#BSparrow}

The buffered sparrow handles the buffers needed for the sockets. It tries to batch together requests when it can. In case of input events, it receives data of at least the length of its buffer (if there are data) even though the requested data are less than than. Thus in subsequent requests, the data will already be there. For send requests, we have disabled Nagle's algorithm and we batch send requests when the throughput pushes back the number of sends we can send.

Secondly, in case there is a failure in a socket, it tries to reconnect.

The api of this layer is such so as to be able to be able to get complete messages in the upper layer, without the upper layer having to keep the data in another buffer while the message is received. That is why we have the ```bsparrow_got_some``` function that tells bsparrow that the buffer specified completes a single message, we have copied the data and thus is free to use the memory for new messages.


## Examples {#bsparrow_examples}

First, we initialize bsparrow. The parameters it takes are

* The buffer size of the sockets that should be above the average size of the message multiplied by two.
* The output timeout that is used to close the connection if a socket is not able to send the data after the specified amount of time.
* The maximum output queue that sets a limit on the number of withstanding output requests. Again we close the socket if the limit is reached.
* The maximum number of sockets that have a pending output request. If it is reached we only handle output requests till it goes back to normal.
* A boolean value whether we are listening to a port or not.
* The port itself.

Then we wait for a connection event. The event is saved into bspev. The third parameter of bsparrow_wait is used to tell bsparrow_wait whether we want to only wait for outputs to be processed. Here we want an input event, thus we set it to ```0```.

When the connection is received, we tell bsparrow that we expect to receive an amount of data. If we didn't do that, bsparrow would throw the received data and probably close the connection.
//TODO I think that we need to keep the connection and only throw the data.

After that, we wait for the data to be received. bspev exposes the internal buffers of bsparrow. The data will be in pultiple buffers because of the batching process we try to do. For a correct way to get a msg, look at the throughput test.

When we have received the complete msg, we tell bsparrow that we got part of the buffer and that it can reuse it.

### Simple Test {#Bsparrow_Simple_Test} 


```c bsimple_test_server.c
#include "bsparrow.h"
#include <stdio.h>
#include <assert.h>

int main(void) {

  bsparrow_t * bsp = bsparrow_new(100, 5000, 100, 2, 1, "9003");

  bsparrow_event_t bspev;
  bsparrow_wait(bsp, &bspev, 0);

  if(bspev.event & 16) {
    bsparrow_socket_assign_id(bspev.bsock, 1);
    bsparrow_recv(bsp, bspev.bsock, 50);
  }

  bsparrow_wait(bsp, &bspev, 0);

  if(bspev.event & 4) {
    assert(bspev.first_buffer_length == 0);
    assert(bspev.list == NULL);
    size_t last_buffer_length = bspev.last_buffer_length;
    char * last_buffer = bspev.last_buffer;
    printf("Received :\n%s\n",last_buffer);
    printf("Length :\n%lu\n",last_buffer_length);
    bsparrow_got_some(bsp, bspev.bsock, last_buffer_length);
  }

  bsparrow_destroy(bsp);
  return 0;
}

```

When we send data, withere bsparrow_send sends them immediately or we need to call bsparrow_wait so that bsparrow sends them when the other end is able to receive more. bsparrow_wait does not return an event that it has sent the data. 

That is why here, we use a timeout to return after a few seconds.

```c bsimple_test_client.c
#include "bsparrow.h"
#include <stdio.h>
#include <assert.h>

int main(void) {

  bsparrow_t * bsp = bsparrow_new(100, 5000, 100, 2, 0, NULL);
  bsparrow_socket_t * bsock = bsparrow_socket_connect(bsp, 1, "127.0.0.1", "9003");

  char *data = scalloc(1, 50);
  sprintf(data,"Hello there!");

  bsparrow_event_t bspev;
  bsparrow_send(bsp, bsock, &data, 50);

  bsparrow_wait(bsp, &bspev, 0);

  bsparrow_set_timeout(bsp, 5000);
  assert(bspev.event == 32);
  printf("I sent : Hello there!");
  
  bsparrow_destroy(bsp);
  return 0;
}

```

### Throughput Test {#Bsparrow_throughput_Test} 

Setting the timeout here allows to close a connection if we fail to receive data after a specific period of time. This is the normal way to use the timeout. Timeouts are the only way to find if a connection or the other end have problems. This leads to the simplification of error handling. 

```c bthr_server.c
#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>


void printmsg(bsparrow_event_t *bspev, size_t size) {
  //Copy the msg to a new buffer.
  char * msg = scalloc(1, size);

  size_t position = 0;
  if(bspev->first_buffer_length > 0) {
    if(size > bspev->first_buffer_length) {
      memcpy(msg, bspev->first_buffer, bspev->first_buffer_length);
      position = bspev->first_buffer_length;
    } else {
      memcpy(msg, bspev->first_buffer, size);
      position = size;
    }
  }

  buffer_list_t * iter = bspev->list;
  while(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);
    memcpy(msg + position, buffer, length);
    position += length;
  }
 
  if(bspev->last_buffer_length) {
    memcpy(msg + position, bspev->last_buffer, size - position);
  }
  Dprintf("Received :\n\n%s\n\n", msg);
  Dprintf("Length : %d\n", size);

  free(msg);

}

void get_msg(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev, size_t size) {
  while(1) {
    bsparrow_recv(bsp, bsock, size);

    bsparrow_set_timeout(bsp, 5000);
    bsparrow_wait(bsp, bspev, 0);

    if(bspev->event & 4) {
      bsparrow_set_timeout(bsp, -1);
      if(bspev->total_length >= size) {
        break;
      }
    }

    if(bspev->event & 32) {
      printf("timeout error. The client must have crushed");
      exit(-1);
    }
    assert(bspev->event & 4);
  }
}


void results(int i, int64_t time, int msg_size) {
  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Length : %d\n", msg_size);
  printf("Msgs received: %d\n", i);
}

int main(int argc, char ** argv) {

  assert(argc == 3);
  int msg_size = atoi(argv[1]);
  int loop_length = atoi(argv[2]);

  bsparrow_t * bsp = bsparrow_new(50000, 4000, 2, 2, 1, "9003");

  bsparrow_event_t bspev;
  bsparrow_socket_t * bsock;
  bsparrow_wait(bsp, &bspev, 0);

  if(bspev.event & 16) {
    bsock = bspev.bsock;
    bsparrow_socket_assign_id(bsock, 1);
  } else {
    exit(-1);
  }
  
  int j = 0;
  int64_t time = now();
  while(j < loop_length) {
    int i = 0;
    while(i < 10000) {
      if(i == 5000) {
        char *data = scalloc(1, 100);
        sprintf(data,"Got 50, need mooooreee!");
        bsparrow_send(bsp, bsock, &data, 100);
        Dprintf("I am sending an aknowledge msg at msg number: %lu\n", j*100 + 50);
      }
      get_msg(bsp, bsock, &bspev, msg_size); 
    
      Dprintf("i: %d\n", i); 
      i++;
      Dprintf("Remaining length: %lu\n", bspev.total_length -msg_size);
      printmsg(&bspev, msg_size);
      bsparrow_got_some(bsp, bsock, msg_size);
    }
    Dprintf("j: %d\n", j); 
    Dprintf("Remaining length: %lu\n", bspev.total_length -msg_size);
    j++;
  }

  printf("Sending: Got them all, thanks!\n");
  char *data = scalloc(1, 100);
  sprintf(data,"Got them all, thanks!");
  bsparrow_send(bsp, bsock, &data, 100);

  results(j*10000, time, msg_size);

  bsparrow_destroy(bsp);
  return 0;
}

```


```c bthr_client.c
#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


void printmsg(bsparrow_event_t *bspev, size_t size) {
  //Copy the msg to a new buffer.
  char * msg = scalloc(1, size);

  size_t position = 0;
  if(bspev->first_buffer_length > 0) {
    if(size > bspev->first_buffer_length) {
      memcpy(msg, bspev->first_buffer, bspev->first_buffer_length);
      position = bspev->first_buffer_length;
    } else {
      memcpy(msg, bspev->first_buffer, size);
      position = size;
    }
  }

  buffer_list_t * iter = bspev->list;
  while(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);
    memcpy(msg + position, buffer, length);
    position += length;
  }
 
  if(bspev->last_buffer_length) {
    memcpy(msg + position, bspev->last_buffer, size - position);
  }
  Dprintf("Received :\n\n%s\n\n", msg);
  Dprintf("Length : %d\n", 100);

  free(msg);

}



void get_msg(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev, size_t size) {
  while(1) {
    bsparrow_recv(bsp, bsock, size);

    bsparrow_set_timeout(bsp, 6000);
    bsparrow_wait(bsp, bspev, 0);

    if(bspev->event & 4) {
      bsparrow_set_timeout(bsp, -1);
      if(bspev->total_length >= size) {
        break;
      }
    }

    if(bspev->event & 32) {
      printf("timeout error. The client must have crushed");
      exit(-1);
    }
    assert(bspev->event & 4);
  }
}



int main(int argc, char ** argv) {
  
  assert(argc == 3);
  int msg_size = atoi(argv[1]);
  int loop_length = atoi(argv[2]);

  bsparrow_t * bsp = bsparrow_new(50000, 4000, 15001, 2, 0, NULL);
  bsparrow_socket_t * bsock = bsparrow_socket_connect(bsp, 1, "127.0.0.1", "9003");
  
  int j = 0;
  while(j < loop_length) {
    int i = 0;
    while(i < 10000) {
      char *data = scalloc(1, msg_size);
      sprintf(data,"Hello there!");
      bsparrow_send(bsp, bsock, &data, msg_size);
      Dprintf("I: %d\n", i);
      i++;
    }

    //Getting an unknowledge msg after every 100 msgs
    bsparrow_event_t bspev ={0};
  
    get_msg(bsp, bsock, &bspev, 100);
  
    printmsg(&bspev, 100);
    bsparrow_got_some(bsp, bspev.bsock, 100);
    Dprintf("J: %d\n", j);
    j++;

  }
  printf("I finished sending the data.\n");


  //Getting an unknowledge msg
  bsparrow_event_t bspev ={0};
  get_msg(bsp, bsock, &bspev, 100);
  printmsg(&bspev, 100);
  bsparrow_got_some(bsp, bspev.bsock, 100);

  bsparrow_destroy(bsp);
  return 0;

}

```



## BSparrow API {#BSparrow_api}

```c bsparrow.h
#ifndef _BSPARROW_H_
#define _BSPARROW_H_

#include<stdlib.h>

//TODO move these definitions into a different file.
#if (defined DEBUG_LOG) 
  #define Dprintf(x, ...) printf(x, ##__VA_ARGS__)
#else 
  #define Dprintf(x, ...)
#endif  

#define MIN_RETRY_INTERVAL 1000

typedef struct buffer_list_t buffer_list_t;

buffer_list_t * buffer_list_next(buffer_list_t * list, char ** data, size_t * length);

typedef struct bsparrow_socket_t bsparrow_socket_t;

struct bsparrow_event_t {
  int64_t id;
  int event;
  bsparrow_socket_t * bsock;
  char * first_buffer;
  size_t first_buffer_length;
  buffer_list_t * list;
  char * last_buffer;
  size_t last_buffer_length;
  size_t total_length;
};

typedef struct bsparrow_event_t bsparrow_event_t;

typedef struct bsparrow_t bsparrow_t;


bsparrow_t * bsparrow_new(size_t buffer_size, int64_t dtimeout, int max_output_queue, int max_output_sockets, int listening, char * port);

void bsparrow_destroy(bsparrow_t * bsp);

bsparrow_socket_t * bsparrow_socket_connect(bsparrow_t * bsp, int64_t id, char * address, char * port);

void bsparrow_socket_destroy(bsparrow_t * bsp, bsparrow_socket_t ** bsock);

void bsparrow_socket_assign_id(bsparrow_socket_t *bsock, int64_t id);

void bsparrow_socket_set_parent(bsparrow_socket_t * bsock, void * parent);

void * bsparrow_socket_get_parent(bsparrow_socket_t * bsock);

void bsparrow_set_timeout(bsparrow_t * bsp, int64_t timeout);

void bsparrow_wait(bsparrow_t * bsp, bsparrow_event_t * bspev, int only_output);

//The memory is owned by bsparrow. It will block if the queue becomes large. //TODO Is this the correct way to handle this?
void bsparrow_send(bsparrow_t * bsp, bsparrow_socket_t * bsock, char ** data, size_t len);

//Idris can give me a pointer , not a pointer of a pointer.
void bsparrow_send_idris(bsparrow_t * bsp, bsparrow_socket_t * bsock, char * data, size_t len);

//The len should never decrease.
void bsparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t len);

void bsparrow_got_some(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t that_much);

//Getters - Setters

int64_t bsparrow_event_get_id(bsparrow_event_t * bspev);

void bsparrow_event_set_id(bsparrow_event_t * bspev, int64_t id);

int bsparrow_event_get_event(bsparrow_event_t * bspev);

void bsparrow_event_set_event(bsparrow_event_t * bspev, int event);

bsparrow_socket_t * bsparrow_event_get_bsock(bsparrow_event_t * bspev);

void bsparrow_event_set_bsock(bsparrow_event_t * bspev, bsparrow_socket_t * bsock);


int64_t now(void);

void * scalloc(size_t num, size_t size);
//TODO check for errors.
void * srealloc(void * prev_pointer, size_t size);
#endif
```

The events that are sent by the bsparrow functions are as follows:

* (4) Input event triggered when new input has arrived.
* (16) New Accepted Connection triggered when a new client connects to our listening port.
* (32) Timeout event triggered when the timeout set has expired. Used to set the input timeout.

## BSparrow implementation {#BSparrow_implementation}


### Buffer data Structures {#Buffer_data_structures}

The most noteworthy part of bsparrow are the buffer structures it uses so as to reduce the number of systems calls.

### Output buffer data structure {#Output_Buffer_data_structure}

The output buffer is very simple. When we send some data, bsparrow takes control of the specific memory and is thus responsible of freeing it. If the memory exceeds the size of the output buffer as set in the ```bsparrow_new``` function, then we use the original memory as the buffer. We specify the is_it_default boolean to know to free it if it is the original memory. When the memory of the output request is smaller than our buffer, then we batch multiple requests together if there are any other reqs pending. In this case, we copy the data to our buffer and free the memory of the request.

Apart from the output buffer, we also have the queue of pending output requests per socket. The queue is cyclical and expands and contructs according to the number of requests that we have. The queue is FIFO. Keep in mind the way we use it.

First, we request the oldest request. If we have enough buffer memory to batch it with other previous requests, then we pop it out of the queue. So it is a two stage process.

```c bsparrow.c.dna
function output_buffer_structures() {
./!dots(1)

struct buffer_out_t {
  int is_it_default;
  char * allocated_memory;
  char * default_memory;
};

typedef struct buffer_out_t buffer_out_t;

struct out_request_t {
  char * data;
  size_t len;
};

typedef struct out_request_t out_request_t;

struct oqueue_t {
  out_request_t * requests;
  int len;
  int first_free_pos;
  int last_free_pos;
  int pos_filled;
};

typedef struct oqueue_t oqueue_t;

void oqueue_new(oqueue_t * oq) {
  oq->requests = scalloc(1, sizeof(out_request_t) * 10);
  oq->len = 10;
  oq->first_free_pos = 0;
  oq->last_free_pos = 9;
}


void oqueue_destroy(oqueue_t * oq) {
  assert(oq->len > 0);
  assert(oq->pos_filled == 0);
  free(oq->requests);
  oq->requests = NULL;
}


int oqueue_next(oqueue_t * oq, int i) {
  assert(oq->len > 0);
  if(oq->len == (i + 1)) {
    return 0;
  } else {
    return i + 1;
  }
}

void oqueue_push_req(oqueue_t * oq, out_request_t * oreq) {
  assert(oq->len > 0);
  //Increase the queue if almost full.
  if(oq->first_free_pos == oq->last_free_pos) {
    out_request_t * reqs = scalloc(oq->len * 10, sizeof(out_request_t));
    int i;
    int j = 0;
    for(i = oqueue_next(oq, oq->last_free_pos); i != oq->first_free_pos; i = oqueue_next(oq,i)) {
      memcpy(&(reqs[j]), &(oq->requests[i]),sizeof(out_request_t));
      j++;
    }
    free(oq->requests);
    oq->requests = reqs;
    oq->first_free_pos = oq->pos_filled;
    oq->last_free_pos = oq->len * 10 - 1;
    oq->len = oq->len * 10;
  }

  memcpy(&(oq->requests[oq->first_free_pos]), oreq, sizeof(out_request_t));
  oq->first_free_pos = oqueue_next(oq, oq->first_free_pos);
  oq->pos_filled++;
}

void oqueue_del_oldest_req(oqueue_t * oq) {
  assert(oq->len > 0);
  assert(oq->pos_filled > 0);

  int pos = oqueue_next(oq, oq->last_free_pos);
  assert(pos != oq->first_free_pos);

  oq->last_free_pos = pos;
  oq->pos_filled--;

   //Decrease the queue if almost empty.
  if((oq->len > 10) && (oq->pos_filled < (oq->len / 10))) {
    out_request_t * reqs = scalloc(oq->len / 10, sizeof(out_request_t));
    int i;
    int j = 0;
    for(i = oqueue_next(oq, oq->last_free_pos); i != oq->first_free_pos; i = oqueue_next(oq, i)) {
      memcpy(&(reqs[j]), &(oq->requests[i]),sizeof(out_request_t));
      j++;
    }
    free(oq->requests);
    oq->requests = reqs;
    oq->first_free_pos = oq->pos_filled;
    oq->last_free_pos = (oq->len / 10) - 1;
    oq->len = oq->len / 10;

  }

}

//You need to pop it if you use it. The memory is owned by the queue.
out_request_t * oqueue_oldest_req(oqueue_t * oq) {
  assert(oq->len > 0);
  out_request_t * req = NULL;

  if(oq->pos_filled > 0) {
    int pos = oqueue_next(oq, oq->last_free_pos);
    assert(pos != oq->first_free_pos);
    req = &(oq->requests[pos]);
  }

  return req;
}


void oqueue_empty(oqueue_t * oq) {
  assert(oq->len > 0);
  out_request_t * req;
  while((req = oqueue_oldest_req(oq)) != NULL) {
    free(req->data);
    req->data = NULL;
    oqueue_del_oldest_req(oq);
  }
}


./!dots(-1)
}
```

### Input buffer data structure {#Input_Buffer_data_structure}

The input buffer data structures are a bit more complicated but the basic idea is simple. We want to be able to receive msgs without having to malloc enough memory to store the data every time a msg arrives. If we assume that the average msg size is AS, then a buffer that is size AS will suffice to receive that msg. The main problem though is that in most cases, we would want to request more data, than the data that our next msg contains. Thus, after our application receives the next msg, a residue will remain in our buffer.
(The reason we request more data is so that we reduce the number of system calls.)

The residue can be in any part of the buffer, thus blocking us in using it to get more msgs. In order to avoid this, we use two buffers, where the first is used to receive new data and the other is used to keep the residue if it exists.

Things get even more complicated because of two reasons. 

1. First, the msg can exceed the size of our bufferm thus we would need to allocate a new piece of memory to save the input data. We also need to maintain a tag that will tell us whether a specific memory is not part of the default buffer and thus should be deleted.

2. Secondly, the application might not know the size of the msg, and thus continually request more data. Keep in mind that bsparrow is responsible in keeping all the data till the complete msg is received. In order to solve that problem, I have introduced a buffer list with the number of buffer that we had to use to save all the input data. As in the previous cases, we have boolean that tells us if we have to free the buffer when the complete msg is received.

```c bsparrow.c.dna
function input_buffer_structures() {
./!dots(1)

struct buffer_list_t {
  void * data;
  size_t len;
  int should_be_freed;
  struct buffer_list_t * next;
};

buffer_list_t * buffer_list_next(buffer_list_t * list, char ** data, size_t * length) {
  *data = list->data;
  *length = list->len;
  return list->next;
}

void buffer_list_destroy(buffer_list_t ** list_) {
  buffer_list_t * item = *list_;
  buffer_list_t * prev_item;
  while(item != NULL) {
    prev_item = item;
    item = item->next;
    if(prev_item->should_be_freed) {
      free(prev_item->data);
    }
    free(prev_item);
  }
  *list_ = NULL;
}

struct buffer_in_t {
  buffer_list_t * list;
  buffer_list_t * last_item;
  size_t total_length_received;
  char * prev_data;  //Pointers to buffer_one, buffer_two and big_buffer.
  int prev_data_tag;  //0 1 or 2 
  char * new_data;   //
  int new_data_tag;
  size_t cur_length;
  size_t residue_start;
  size_t residue_length;
  size_t new_data_len;
  char * default_memory;     
};

typedef struct buffer_in_t buffer_in_t;

./!dots(-1)
}
```

## Bsparrow socket {#Bsparrow_socket}

The bsparrow socket structure contains:

* In case we connected, the address and port so that in case of failure, we can automatically try to reconnect.
* The sparrow socket needed to perform the operations as well as the buffers and output queue.
* Boolean values that indicate whether the socket is operational or destroyed.
* The retries of reconnection.
* Whether our sparrow socket is able to send more data or not.

We need out_more because bsparrow_wait doesn't return output events, thus we are unable to know if we can send more.

The boolean internally destroyed indicates that we have freed all the memory that this sockets allocates but we haven't freed the socket itself. The internal destruction happens when an error is unrecoverable. BUT we do not send error events to the higher levels. The only way that higher levels can witness the error is through an input timeout. Thus, because higher levels might own the bsocket, we do not free its memory. When new requests from higher levels arrive, they immediately silently fail.


```c bsparrow.c.dna
function bsparrow_socket() {
./!dots(1)

struct bsparrow_socket_t {
  int64_t id;
  int we_connected;
  char * address;
  char * port;
  sparrow_socket_t * sock;
  buffer_in_t buff_in;
  buffer_out_t buff_out;
  oqueue_t oq;
  int internally_destroyed;
  int operational;
  int retries;
  int out_more; //Indicates whether the last time we sent data, the socket was ready to receive more immediately.
  bsparrow_event_t imbspev;
  void * parent;
};

./!dots(-1)
}
```

## Bsparrow {#Bsparrow_impl}

Bsparrow contains many properties that are set when it is initiated.

* MAX RETRIES : It specifies the maximum number of reconnection retries before the socket is considered unrecoverable ans is destroyed.
* MAX OUTPUT QUEUE: The maximum number of pending output requests. To protect from slow end points that could trigger memory depletion, we close the connection when it is reached. Also, look at sparrow's output timeout option that protects from end points that do not receive new data or very slowly.
* MAX OUTPUT SOCKETS: It is used so that we block creating many sockets that have output requests. Again, we protect against memory depletion.

Bsparrow also contains two lists. The first list is the list of non operational sockets that we try to reconnect. The second list contains events that are triggered independent of bsparrow_wait. We save them and send them to the higher levels from bsparrow_wait so that the higher level's code is simpler at processing events.


//TODO The list api is a bit tricky. It might require some explanation.

```c bsparrow.c.dna
function bsparrow() {
./!dots(1)

struct non_op_bsock_list_t {
  bsparrow_socket_t * bsock;
  struct non_op_bsock_list_t * next;
};

typedef struct non_op_bsock_list_t non_op_bsock_list_t;

non_op_bsock_list_t * non_op_bsock_list_add(non_op_bsock_list_t * list, bsparrow_socket_t * bsock) {
  assert(bsock->operational == 0);
  non_op_bsock_list_t * item = scalloc(1, sizeof(non_op_bsock_list_t));
  item->bsock = bsock;

  if(list != NULL) {
    item->next = list->next;
    list->next = item->next;
    return list;
  } else {
    return item;
  }
}

//Returns the list because we might remove the first element of the list.
non_op_bsock_list_t * non_op_bsock_list_rem_next(non_op_bsock_list_t * list, non_op_bsock_list_t * prev_item) {
  if(list == NULL) {
    return NULL;
  }

  if(prev_item == NULL) {
    non_op_bsock_list_t * next_item = list->next;
    free(list);
    return next_item;
  }

  non_op_bsock_list_t * next_item = prev_item->next;
  if(next_item !=NULL) {
    prev_item->next = next_item->next;
    free(next_item);
  }
  return list;
}


struct bsparrow_event_list_t {
  bsparrow_event_t * bspev;
  struct bsparrow_event_list_t * next;
};

typedef struct bsparrow_event_list_t bsparrow_event_list_t;

bsparrow_event_list_t * bsparrow_event_list_add(bsparrow_event_list_t * list, bsparrow_event_t * bspev) {
  bsparrow_event_list_t * item = scalloc(1, sizeof(bsparrow_event_list_t));
  item->bspev = bspev;

  if(list != NULL) {
    item->next = list->next;
    list->next = item->next;
    return list;
  } else {
    return item;
  }
}

//Returns the list because we might remove the first element of the list.
bsparrow_event_list_t * bsparrow_event_list_rem_next(bsparrow_event_list_t * list, bsparrow_event_list_t * prev_item) {
  if(list == NULL) {
    return NULL;
  }

  if(prev_item == NULL) {
    bsparrow_event_list_t * next_item = list->next;
    free(list);
    return next_item;
  }

  bsparrow_event_list_t * next_item = prev_item->next;
  if(next_item !=NULL) {
    prev_item->next = next_item->next;
    free(next_item);
  }
  return list;
}



struct bsparrow_t {
  sparrow_t * sp;
  size_t buffer_size; // The maximum memomry of most of the objects * 2.
  int max_retries;
  non_op_bsock_list_t * non_op_bsock_list;
  bsparrow_event_list_t * ibspev_list;  //An event that is triggered immediate after a function call and that we want to save so as
  // to be handled by bsparrow_wait itself (rather than handled separately.)
  int max_output_queue; //The maximum size of the output queue of a socket.
  int64_t rltime; //Last time we retried to connect to nonoperational connections.
  int max_output_sockets;  //The number of sockets that have output data till bsparrow stops receiving new connections.
  int total_output_sockets;
};



./!dots(-1)
}
```
## Convenient Setters/Getters {#Bsparrow_set_get}

The idris language does not at the moment provide a convinient way to access the fields of a struct. That is why we implement setters and getters for "bsparrow_event_t"

```c bsparrow.c.dna
function get_set_functions() {
./!dots(1)

int64_t bsparrow_event_get_id(bsparrow_event_t * bspev) {
  return bspev->id;
}

void bsparrow_event_set_id(bsparrow_event_t * bspev, int64_t id) {
  bspev->id = id;
}

int bsparrow_event_get_event(bsparrow_event_t * bspev) {
  return bspev->event;
}

void bsparrow_event_set_event(bsparrow_event_t * bspev, int event) {
  bspev->event = event;
}

bsparrow_socket_t * bsparrow_event_get_bsock(bsparrow_event_t * bspev) {
  return bspev->bsock;
}

void bsparrow_event_set_bsock(bsparrow_event_t * bspev, bsparrow_socket_t * bsock) {
  bspev->bsock = bsock;
}





./!dots(-1)
}
```

## The remaining Bsparrow implementation {#Bsparrow_rem_impl}


```c bsparrow.c.dna
function handle_error() {
./!dots(1)
if(!bsock->we_connected) {
  bsparrow_socket_internal_destroy(bsp, bsock);
} else {
  bsock->sock = NULL;
  bsparrow_socket_clean(bsp, bsock);
  bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
}
./!dots(-1)
}
```

```c bsparrow.c.dna
./!dots(1)

#include "sparrow.h"
#include "bsparrow.h"
#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include<assert.h>
#include "tree.h"


//TODO We need an initialization function for the buffer socket. It is performed if there are stored session in hd or if a new session is requested from the network or initiated by us.

./!dots(-1)
input_buffer_structures();
output_buffer_structures();
bsparrow_socket();
bsparrow();
get_set_functions();
./!dots(+1)




./!dots(-1)
function default_socket_values() {
./!dots(1)
bsock->internally_destroyed = 0;
bsock->out_more = 1;
bsock->buff_in.new_data = bsock->buff_in.default_memory;
bsock->buff_in.new_data_tag = 0;
bsock->buff_in.prev_data = bsock->buff_in.default_memory + bsp->buffer_size / 2;
bsock->buff_in.prev_data_tag = 1;
bsock->buff_in.cur_length = 0;
bsock->buff_in.residue_start = 0;
bsock->buff_in.residue_length = 0;
bsock->buff_in.list = NULL;
bsock->buff_in.total_length_received = 0;
bsock->buff_in.new_data_len = bsp->buffer_size / 2;
bsock->buff_out.allocated_memory = bsock->buff_out.default_memory;
bsock->buff_out.is_it_default = 1;
./!dots(-1)
}
./!dots(1)





//Internal use only
void bsparrow_socket_clean(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  assert(bsock->operational == 0);
  assert(bsock->sock == NULL);
  //Clean input buffer list
  buffer_in_t * buffer = &(bsock->buff_in);
  buffer_list_destroy(&(buffer->list));

  //Clean the rest probable big_buffers
  if(buffer->prev_data_tag == 2) {
    free(buffer->prev_data);
  }
  if(buffer->new_data_tag == 2) {
    free(buffer->new_data);
  }
  if(!bsock->buff_out.is_it_default) {
    free(bsock->buff_out.allocated_memory);
    bsock->buff_out.allocated_memory = bsock->buff_out.default_memory;
  }

  oqueue_empty(&(bsock->oq));

./!dots(-1)
.  @{default_socket_values()}
./!dots(1)
}


//Internal use
bsparrow_socket_t * bsparrow_socket_initialize_internal(bsparrow_t * bsp,sparrow_socket_t * sock, int64_t id, int we_connected, char * address, char * port) {
  bsparrow_socket_t * bsock = scalloc(1, sizeof(bsparrow_socket_t));
  bsock->sock = sock;
  if(sock != NULL) {
    bsock->operational = 1;
  } else {
    //This can only happen when we connect, not when we accept a new connection.
    assert(we_connected == 1);
    bsock->operational = 0;
    bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
  }
  bsock->id = id;
  bsock->we_connected = we_connected;
  if(we_connected) {
    bsock->address = scalloc(1, strlen(address) + 1);
    bsock->port = scalloc(1, strlen(port) + 1);
    strcpy(bsock->address, address);
    strcpy(bsock->port, port);
  }
  sparrow_socket_set_parent(bsock->sock, bsock);
  bsock->buff_in.default_memory = scalloc(1, bsp->buffer_size);
  bsock->buff_out.default_memory = scalloc(1, bsp->buffer_size);

./!dots(-1)
.  @{default_socket_values()}
./!dots(1)

  oqueue_new(&(bsock->oq));

  return bsock;
}

bsparrow_socket_t * bsparrow_socket_connect(bsparrow_t * bsp, int64_t id, char * address, char * port) {
  sparrow_socket_t * sock = sparrow_socket_connect(bsp->sp, address, port);
  if(sock) {
    return bsparrow_socket_initialize_internal(bsp, sock, id, 1, address, port); 
  } else {
    return NULL;
  }
}

//Internal use only We need to pass it to the higher levels to be given an id.
bsparrow_socket_t * bsparrow_socket_accept(bsparrow_t * bsp, sparrow_socket_t * sock) {
  return bsparrow_socket_initialize_internal(bsp, sock, -1 , 0, NULL, NULL);
}

void bsparrow_socket_assign_id(bsparrow_socket_t *bsock, int64_t id) {
  bsock->id = id;
}

void bsparrow_socket_set_parent(bsparrow_socket_t * bsock, void * parent) {
  bsock->parent = parent;
}

void * bsparrow_socket_get_parent(bsparrow_socket_t * bsock) {
  return bsock->parent;
}

//Internal use only
void bsparrow_socket_internal_destroy(bsparrow_t * bsp, bsparrow_socket_t * bsock) {

  if(bsock->we_connected) {
    free(bsock->address);
    free(bsock->port);
  }
  if(bsock->operational) {
    printf("Destroying socket.\n");
    sparrow_socket_close(bsp->sp, bsock->sock);
    bsock->operational = 0;
    bsock->sock = NULL;
  }

  free(bsock->buff_in.default_memory);

  free(bsock->buff_out.default_memory);

  bsparrow_socket_clean(bsp, bsock);
  oqueue_destroy(&(bsock->oq));

  bsock = NULL;
}

void bsparrow_socket_destroy(bsparrow_t * bsp, bsparrow_socket_t ** bsock_) {
  bsparrow_socket_t * bsock = *bsock_;
  if(!bsock->internally_destroyed) {
    bsparrow_socket_internal_destroy(bsp, bsock);
  }
  free(bsock);
  bsock = NULL;
}

bsparrow_t * bsparrow_new(size_t buffer_size, int64_t dtimeout, int max_output_queue, int max_output_sockets,  int listening, char * port) {

  if( ((buffer_size/2) * 2) != buffer_size) {
    printf("Buffer size should be a multiple of 2.\n");
    exit(1);
  }

  bsparrow_t * bsp = scalloc(1, sizeof(bsparrow_t));
  bsp->sp = sparrow_new(dtimeout);
  bsp->max_output_queue = max_output_queue;
  bsp->max_output_sockets = max_output_sockets;
  bsp->total_output_sockets = 0;
  bsp->buffer_size = buffer_size;
  bsp->rltime = now();

  if(listening) {
    sparrow_socket_bind(bsp->sp,port);
  }
  return bsp;
}

void bsparrow_destroy(bsparrow_t * bsp) {
  Dprintf("Inside bsparrow_destroy.\n");

  sparrow_socket_t * iter = sparrow_first(bsp->sp);
  bsparrow_socket_t * prev_iter;
  while(iter != NULL) {
    prev_iter = sparrow_socket_get_parent(iter);
    //This is only NULL when PREV_ITER is the listening socket. We need to provide an assert.
    if(prev_iter!=NULL) {
      bsparrow_socket_destroy(bsp, &prev_iter);
    }
    iter = sparrow_next(bsp->sp, iter);
  }

  bsparrow_event_list_t * eviter = bsp->ibspev_list; 
  while(eviter != NULL) {
    free(eviter->bspev);
    eviter = bsparrow_event_list_rem_next(eviter, NULL);
  }

  non_op_bsock_list_t * nopiter = bsp->non_op_bsock_list; 
  while(nopiter != NULL) {
    bsparrow_socket_destroy(bsp, &(nopiter->bsock));
    nopiter = non_op_bsock_list_rem_next(nopiter, NULL);
  }

  sparrow_close(&(bsp->sp));
  free(bsp);
}

void bsparrow_set_timeout(bsparrow_t * bsp, int64_t timeout) {
  sparrow_set_timeout(bsp->sp, timeout);
}



//Internal use only
void bsparrow_socket_process_next_out_req(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  assert(bsock->operational == 1);

  int more = 1;
  out_request_t * req;
  sparrow_event_t spev = {0};
  while(bsock->operational && more && ((req = oqueue_oldest_req(&(bsock->oq))) != NULL) ) {
  
    buffer_out_t * buffer= &(bsock->buff_out);
  
    //Free memory if you have to.
    if(buffer->is_it_default == 0) {
      free(buffer->allocated_memory);
      buffer->allocated_memory = buffer->default_memory;
      buffer->is_it_default = 1;
    }
    
    
    if(req->len > bsp->buffer_size) {
      buffer->allocated_memory = req->data;
      buffer->is_it_default = 0;
      more = sparrow_send(bsp->sp, bsock->sock, buffer->allocated_memory, req->len, &spev);
      oqueue_del_oldest_req(&(bsock->oq));
    } else {
      size_t total_req_len = 0;
      while((req != NULL) && (total_req_len + req->len <= bsp->buffer_size)) {
        memcpy(buffer->allocated_memory + total_req_len, req->data, req->len);
        free(req->data);
        req->data = NULL;
        total_req_len += req->len;
        oqueue_del_oldest_req(&(bsock->oq));
        req = oqueue_oldest_req(&(bsock->oq));
      }
      Dprintf("Total memory sent: %lu\n", total_req_len);
      more = sparrow_send(bsp->sp, bsock->sock, buffer->allocated_memory, total_req_len, &spev);
    }
  }

  //Adds the socket to the output sockets if it wasn't already in it.
  bsp->total_output_sockets = bsock->out_more - more;

  bsock->out_more = more;

  if(spev.event == 8) {
    assert(bsock->operational == 1);
    bsock->operational = 0;
    bsock->sock = NULL;
    assert(bsock->retries == 0);
./!dots(-1)
.    @{handle_error()}
./!dots(1)
  } 
}


void bsparrow_retry_single(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  sparrow_socket_t * sock = sparrow_socket_connect(bsp->sp, bsock->address, bsock->port);
  if(sock != NULL) {

    bsock->sock = sock;
    sparrow_socket_set_parent(sock, bsock);
    bsock->operational = 1;

  } else {
    bsock->retries++;
  }
}


// If one fails completely, return the apropriate event
void bsparrow_retry(bsparrow_t * bsp) {

  int64_t time = now();
  if(bsp->rltime + MIN_RETRY_INTERVAL > time) {
    return;
  }
  bsp->rltime = time;

  non_op_bsock_list_t * list = bsp->non_op_bsock_list;
  non_op_bsock_list_t * iter = bsp->non_op_bsock_list;
  non_op_bsock_list_t * prev_iter = NULL;
  
  while(iter != NULL) {
    bsparrow_retry_single(bsp, iter->bsock);
    if(iter->bsock->operational == 1) {
      bsp->non_op_bsock_list = non_op_bsock_list_rem_next(list, prev_iter);
    } else {
      if(iter->bsock->retries > bsp->max_retries) {
        bsparrow_socket_internal_destroy(bsp, iter->bsock);
        bsp->non_op_bsock_list = non_op_bsock_list_rem_next(list, prev_iter);
      }
    }
    prev_iter = iter;
    iter = iter->next;
  }
}

//Internal
void bsparrow_immediate_event(bsparrow_t * bsp, bsparrow_event_t * bspev) {
  bspev->event = 0;
  if(bsp->ibspev_list != NULL) {
    memcpy(bspev, bsp->ibspev_list->bspev, sizeof(bsparrow_event_t));
    bsp->ibspev_list = bsparrow_event_list_rem_next(bsp->ibspev_list, NULL);
  }
}

int bsparrow_wait_(bsparrow_t * bsp, bsparrow_event_t * bspev, int only_output) {
  
//handle immediate events. At this moment, only the bsparrow_send function creates immediate events.
//So that we handle all events in a single function, we save the immediate events so as to be sent out
//by bsparrow_wait.
  if(!only_output) {
    bsparrow_immediate_event(bsp, bspev);
    if(bspev->event != 0) {
      return 0;
    }
  }

  //Handle Events created due to retry efforts. Put a time rate when we retry a new connection.
  bsparrow_retry(bsp);

  //New events from the network.
  sparrow_event_t spev;
  bsparrow_socket_t * bsock;
    
  sparrow_wait(bsp->sp, &spev, only_output);
  int ev = spev.event;
  bsock = spev.parent;

  int at_least_once_output = 0;
  if((ev >> 1) & 1) {
    bsparrow_socket_process_next_out_req(bsp, bsock);
    at_least_once_output = 1;
  }

  //Error
  if((ev >> 3) & 1) {
    assert(bsock->operational == 1);
    bsock->operational = 0;
    bsock->sock = NULL;
    if(bsock->we_connected) {
      assert(bsock->retries == 0);
      bsparrow_socket_clean(bsp, bsock);
      bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
    } else {
      bsparrow_socket_internal_destroy(bsp, bsock);
    }
  }

  if(only_output) {
    if(at_least_once_output && bsp->total_output_sockets) {
      return 1;
    } else {
      return 0;
    }
  }


  bspev->event = 0;
  bspev->bsock = bsock;
  
  //Input timeout
  if((ev >> 5) & 1) {
    bspev->event = 32;
    return 0;
  }

  if((ev >> 2) & 1) {
    buffer_in_t * buffer = &(bsock->buff_in);
    
    buffer->cur_length = buffer->cur_length + spev.cur;
    buffer->total_length_received += spev.cur;

./!dots(-1)
.    @{fill_input_event()}
./!dots(1)
    return 0;

  }
  //New connection.
  if((ev >> 4) & 1) {
    bspev->bsock = bsparrow_socket_accept(bsp, spev.sock);
    bspev->id = bspev->bsock->id;
    bspev->event = 16;
    return 0;
  }

  return 1;
}


void bsparrow_wait(bsparrow_t * bsp, bsparrow_event_t * bspev, int only_output) {
  while(bsparrow_wait_(bsp, bspev, only_output)) {
  }
}

void bsparrow_send(bsparrow_t * bsp, bsparrow_socket_t * bsock, char ** data, size_t len) {

  //When it is not operational, simply drom the data.
  if(bsock->operational == 0) {
    free(*data);
    *data = NULL;
    return;
  }

  //All immediate events should have already been handled before waiting for more.
  assert(bsp->ibspev_list == NULL);

  out_request_t req;
  req.data = *data;
  *data = NULL;
  req.len = len;

  oqueue_push_req(&(bsock->oq), &req);
  
  if(bsock->out_more) {
    bsparrow_socket_process_next_out_req(bsp, bsock);
  } else {
    bsparrow_wait(bsp, NULL, 1);
  }

  //If we still have a number of output sockets that exceed the maximum number, then continue to wait till they decrease.
  while(bsp->total_output_sockets >= bsp->max_output_sockets) {
    bsparrow_wait(bsp, NULL, 1);
  }

// If the queue is bigger than the maximum allowed queue, destroy the socket.
//TODO For these cases, it is better not to reconnect, since that will not help.
//TODO The same is true for output timeouts.
//TODO More information is required as to the type of errors that can occur and the special handling that they might require.

  if(bsock->operational && (bsock->oq.pos_filled > bsp->max_output_queue)) {
    printf("The maximum output queue length was reached\n");
    bsock->operational = 0;
    sparrow_socket_close(bsp->sp, bsock->sock);
    bsock->sock = NULL;
    assert(bsock->retries == 0);
  
./!dots(-1)
.    @{handle_error()}
./!dots(1)
  }
}


void bsparrow_send_idris(bsparrow_t * bsp, bsparrow_socket_t * bsock, char * data, size_t len) {
  char * data_ = data;
  bsparrow_send(bsp, bsock, &data_, len);
}



./!dots(-1)
function fill_input_event() {
./!dots(1)
if(buffer->residue_length) {
  bspev->first_buffer_length = buffer->residue_length;
  bspev->first_buffer = buffer->prev_data + buffer->residue_start;
} else {
  bspev->first_buffer_length = 0;
  bspev->first_buffer = NULL;
}
bspev->list = buffer->list;
bspev->last_buffer = buffer->new_data;
bspev->last_buffer_length = buffer->cur_length;
bspev->total_length = buffer->total_length_received;
bspev->event = 4;
bspev->id = bsock->id;
bspev->bsock = bsock;

./!dots(-1)
}
./!dots(1)

//TODO The len should never decrease.
void bsparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t len) {

  if(bsock->operational == 1) {
    //All immediate events should have already be handled before waiting for more.
    assert(bsp->ibspev_list == NULL);
          
    buffer_in_t * buffer = &(bsock->buff_in);
    
    //We already have the data.
    if(buffer->total_length_received >= len) {
      bsparrow_event_t * bspev = &(bsock->imbspev);
  
./!dots(-1)
.      @{fill_input_event()}
./!dots(1)
  
      bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev_list, bspev);
      return;
    }
  
  
    //If there is still some memory left from the previous buffer keep receiving in it.
    if(buffer->new_data_len == buffer->cur_length) { 
  
      //We push the new data into the list
      buffer_list_t * item = scalloc(1, sizeof(buffer_list_t));
      if(buffer->new_data_tag !=2) {
        item->should_be_freed = 0;
      } else {
        item->should_be_freed = 1;
      }
      item->data = buffer->new_data;
      item->len = buffer->new_data_len;
      item->next = NULL;
      if(buffer->list == NULL) {
        buffer->list = item;
      } else {
        buffer->last_item->next = item;
      }
      buffer->last_item = item;
  
      void * new_memory;
      new_memory = scalloc(1, len - buffer->total_length_received);
      buffer->cur_length = 0;
  
  
      buffer->new_data = new_memory;
      buffer->new_data_tag = 2;
      buffer->new_data_len = len - buffer->total_length_received;
    }
  
    sparrow_recv(bsp->sp, bsock->sock, buffer->new_data + buffer->cur_length, buffer->new_data_len - buffer->cur_length); 
  }

}


void bsparrow_got_some(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t that_much) {
  buffer_in_t * buffer = &(bsock->buff_in);

  //We get all the data that we requested, no less, except the last request.
  assert((buffer->cur_length == 0) || (that_much >= buffer->total_length_received - buffer->cur_length));
  assert(that_much <= buffer->total_length_received);



  if(that_much <= buffer->residue_length) {
    buffer->residue_start = buffer->residue_start + that_much; 
    buffer->residue_length = buffer->residue_length - that_much;
    buffer->total_length_received = buffer->total_length_received - that_much;
    return;
  }

  //Here that_much > buffer->residue_length

  if(buffer->prev_data_tag == 2) {
    free(buffer->prev_data);  
  }

  buffer->residue_length = 0;
  
  //Clean list
  buffer_list_destroy(&(buffer->list));
  buffer->last_item = NULL;


  //Update the new residue.
  buffer->residue_start = buffer->cur_length - (buffer->total_length_received - that_much);  
  buffer->residue_length = buffer->total_length_received - that_much;
  buffer->cur_length = 0;
  buffer->prev_data_tag = buffer->new_data_tag;
  buffer->prev_data = buffer->new_data;

  buffer->total_length_received = buffer->residue_length;
  
  if(buffer->prev_data_tag != 0) {
    buffer->new_data = buffer->default_memory;
    buffer->new_data_tag = 0;
  } else {
    buffer->new_data = buffer->default_memory + (bsp->buffer_size / 2);
    buffer->new_data_tag = 1;
  }
  buffer->new_data_len = bsp->buffer_size / 2;
}

./!dots(-1)
```


## The output expiry problem {#output_expiry_problem}

Let me give you an example. Let us assume that we have two connections.
One of them is a bit slow, so we send as much data as we can and continue processing the input of second connection. 

If the second connection requires processing that takes a lot of time, the first connection might be able to receive new data but we were bizzy to be able to send the remaining data.
Thus, the output expiry might trigger not because the initial connection was very slow but because we were bizzy doing other things.

If on the other hand, we waited for the initial connection to finish getting the data, we are prone to an attack in which the first connection slows on purpose.

I have defined that we wait at least MIN_OUTPUT_WAIT time. Whether this is correct is another thing. Maybe it needs to be set by the user in the bsparrow_new function.  //TODO


# Epoll Wrapper {#Epoll_Wrapper}

The first thing that we need to do is to provide a wrap around linux epoll that simplifies the api for the asynchronous communications. This wrapper needs to be able to do only one thing.

**Given a buffer, the wrapper needs to be able to send or receive data into it unless a timeout expires.**

There is a small difference between a receive and a send though. Because we want to reduce the number of recv system calls, we provide the wrapper a buffer that might be bigger that the data that are available. If the client doesn't send more data
, that would mean that we would never receive the data that the client already sent. To aleviate this problem, we immediately return as much data as we currently have without waiting to fill the buffer.

## Examples {#sparrow_examples}

### A simple receive and response Protocol {#Simple_receive_response_protocol}

This example simply has one program binding to the local port and wait to receive one message from the other program. The other program connects , sends the msg and then exits.

First of all, we need to include our library header 'sparrow.h'. Then, we create an object that handles all our asynchronous communications. We bind to the port "9003" and we wait for sparrow to give our first event. We know that one client will connect and transmit one msg, thus we first handle the connection. We use the socket we get from the connection event to ask sparrow to wait for a msg. We need to provide a buffer to sparrow so as to copy the msg. **Keep in mind that we drop data that we do not expect.** After we have received the msg, we print it and exit.

```c simple_test_server.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev, 0);


  if(spev.event & 16) {
    char *data = scalloc(1, 50);
    sparrow_recv(sp, spev.sock, data,50);
  }
  //New Msg
  sparrow_wait(sp,&spev, 0);
  if(spev.event & 4) {
    char * data_out = sparrow_socket_data_in(spev.sock);
    printf("Received :\n%s\n",data_out);
    free(data_out);
  }

  sparrow_close(&sp);
  return 0;
}

```

The client simply sents a Msg.It waits till sparrow tells it that it sent it and exits.

```c simple_test_client.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  char *data = scalloc(1, 50);
  sprintf(data,"Hello there!");

  sparrow_event_t spev;
  sparrow_send(sp, sock, data, 50, &spev);

  sparrow_wait(sp,&spev, 0);
  printf("I sent : %s",data);
  
  sparrow_close(&sp);
  return 0;
}

```


### A Timeout Example

Everything looks great till now, but reality is different than the constructs we use to have in our heads. We might expect a msg to come but that msg might never come. We need to be able to cancel our order to receive or send a msg. The way we detect failures is by waiting for a period of time before we give up. That is the meaning of setting a timeout.

Sparrow requires the precise time that a request will expire. To find the current time, we call the 'now' function.

```c timeout_server.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev, 0);

  if(spev.event & 16) {
    char *data = scalloc(1, 50);
    sparrow_set_timeout(sp, 5000);
    sparrow_recv(sp, spev.sock, data,50);
  }

  sparrow_wait(sp,&spev, 0);
  if(spev.event & 32) {
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
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  sleep(7);
  sparrow_close(&sp);
  return 0;
}

```

### Network Errors {#Network_Errors}

Network errors do happen. The client might close the connection before we finish our communication protocol. Other errors might happen as well. Sparrow does not distinguish between errors.
If an output is not sent after the timeout has expired, it is treated as an error. 
Timeouts lead to the closure of the connection as any other error. Sparrow returns the same event ('8') for both.

It is important to note that timeouts set on sparrow_wait is not an error. Sparrow_wait expects input timeouts to be given and we treat input timeouts differently than output timeouts.
In essence, in case of error, like the non-transmission of a message, the input timeout will always trigger while the output timeout won't necessarily. 

The test bellow requires that the sample interval is very low (1ms).

//TODO It is assumed that in case the second agent crashes, there are more reliable ways of reacting to it than knowing that the ouptput msg never reached the destination. The msg might have been on the wire before the agent crashed.

```c ot_test_server.c
#include "sparrow.h"
#include <stdio.h>
#include <unistd.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev, 0);

  if(spev.event & 16) {
    printf("we connected and now we will wait for a period so that the client output timeout expires.\n");
    sleep(3);
  }

  sparrow_close(&sp);
  return 0;
}

```


```c ot_test_client.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(10);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  char *data = scalloc(1, 50000000);
  sprintf(data,"Hello there!");

  sparrow_event_t spev;
  sparrow_send(sp, sock, data, 50000000, &spev);

  sparrow_wait(sp,&spev, 0);

  if(spev.event & 8) {
    printf("An error occured.\n");
  }
  
  sparrow_close(&sp);
  return 0;
}

```


### Throughput test {#Throughput_Test}

It is time to test the performance of our library. We will transfer 2M msgs of 500 bytes size and then compute our throughput. In this test, we also check for the error event and if it happens, we exit.

```c thr_server.c
#include "sparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9001");
  
  char *data = scalloc(1, 50);
  
  sparrow_event_t spev;
  sparrow_wait(sp,&spev, 0);
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
    sparrow_wait(sp,&spev, 0);
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

  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9001");


  sparrow_event_t spev;
  spev.event = 0;
  int sent_immediately = 1;
  int i = 0;

  while(i < 2000000) {

    if((spev.event & 2) || (sent_immediately == 1)) {
      char *data = scalloc(1, 50);
      sprintf(data,"Hello there!");
      sent_immediately = sparrow_send(sp, sock, data, 50, &spev);
      if(spev.event & 8) {
        Dprintf("An error occured");    
        break;
      }
      free(data);
    }

    if(sent_immediately == 0) {
      sparrow_wait(sp,&spev, 0);
    }

    if((spev.event & 2) || (sent_immediately == 1)) {
      char * data_out = sparrow_socket_data_out(sock);
      Dprintf("Sent :\n%s\n",data_out);
      i++;
    }
  }

  sparrow_close(&sp);
  exit(0);
}

```

## Sparrow Api {#Sparrow_Api}

All the functions that are provided by the sparrow library can be found in the 'sparrow.h' header file.

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
  int fd;
  void * parent;
  sparrow_socket_t * sock;
  size_t cur;
  int event;
};

typedef struct sparrow_event_t sparrow_event_t;

sparrow_t * sparrow_new(int64_t dtimeout);

void sparrow_socket_bind(sparrow_t * sp, char * port);

sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port); 

//Only one event can be given at a time.
void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev, int only_output);

void sparrow_set_timeout(sparrow_t * sp, int64_t timeout);

int sparrow_send( sparrow_t * sp, sparrow_socket_t *sock, void * data, size_t len, sparrow_event_t * spev);

//TODO Is this needed?
void sparrow_cancel_send( sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_recv( sparrow_t * sp, sparrow_socket_t *sock, void *data, size_t len);

//TODO Is this needed?
void sparrow_cancel_recv( sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_close(sparrow_t ** sp);

//Used to iterate over all sockets.
sparrow_socket_t * sparrow_first(sparrow_t * sp);
sparrow_socket_t * sparrow_next(sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_socket_set_parent(sparrow_socket_t * sock, void * parent);

void * sparrow_socket_get_parent(sparrow_socket_t * sock);

//?TODO Remove these, the serializer/multiplexer is supposed to keep a pointer to its buffer.
void * sparrow_socket_data_in(sparrow_socket_t *sock);
void * sparrow_socket_data_out(sparrow_socket_t *sock);
int64_t now(void);

void * scalloc(size_t num, size_t size);
//TODO check for errors.
void * srealloc(void * prev_pointer, size_t size);

#endif
```


## Sparrow Implementation {#Sparrow_Implementation}

### Time {#Time}

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

### Sparrow Internal Data Structs {#Sparrow_Internal_Data_structs}

Output data buffers need to contain the point till which they had already sent because the network might not allow all the data to be transmitted at once. Both output and input data buffers need to know their length for obvious reasons:

```c sparrow.c.dna
function data_buffer_definitions() {
./!dots(1)

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

./!dots(-1)
}
```

The socket needs to know 

1. if it is listening for connections or not,
2. its file descriptor obviously as the fd is used to perform system calls to the operating system,
3. an expiration time that represents the time till we wish to wait for the data to be sent.

The socket will also contain pointers to the buffers and one fields that are used to order all the sockets according to the file descriptor. We will use this ordering to retrieve the apropriate socket when a new event occurs.

```c sparrow.c.dna
function sparrow_socket_definition() {
./!dots(1)
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
  int is_cur_output; // On the output loop or on the input loop.
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  struct fd_rb_t fd_rb_socks; // A tree container of sockets ordered by the fd.
  struct ot_rb_t ot_rb_socks; // A tree container of sockets ordered by the expiration if their outputs.
  int64_t default_ot;
  int64_t t_expiry;  // The time that the timeout expires.
  int64_t oltime; //Last time we checked for output expirations.
};
./!dots(-1)
}
```

### Ordering of Sockets {#Ordering_of_Sockets}

We use Niels Provos code to generate Red Black trees to order our sockets. The relevant code is here.

```c sparrow.c.dna
function tree_generation() {
./!dots(1)

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
  int64_t ot = (s1->out_expiry > s2->out_expiry) - (s1->out_expiry < s2->out_expiry);
  if(ot != 0) {
    return ot;
  } else {
    return (s1->fd > s2->fd) - (s1->fd < s2->fd);
  }
}

RB_HEAD (ot_rb_t, sparrow_socket_t);
RB_GENERATE (ot_rb_t, sparrow_socket_t, ot_field, cmp_ots);

./!dots(-1)
}
```

### External Socket Traversal {#External_Socket_Traversal}

We also create an api for others to iterate over the sockets.

```c sparrow.c.dna
function external_socket_traversal() {
./!dots(1)

//Used to iterate over all sockets.
sparrow_socket_t * sparrow_first(sparrow_t * sp) {
  return RB_MIN(fd_rb_t, &(sp->fd_rb_socks));
}

sparrow_socket_t * sparrow_next(sparrow_t * sp, sparrow_socket_t * sock) {
  return RB_NEXT(fd_rb_t, &(sp->fd_rb_socks), sock);
}

./!dots(-1)
}
```

### Sparrow Send and Receive {#Sparrow_send_receive}

The sparrow_send function tries to send the data. If it fails to send them all, it asks sparrow to send the rest.
On the other hand, Sparrow_receive simply accepts the buffer and waits for sparrow to receive the data when they come.

It is important to note that we always zero the length of the buffer in order to be able to assert in the future that we are not sending/receiving when there are already 
data to be sent received or the opposite that we have asked for data to be received when we receive data.

```c sparrow.c.dna
function sparrow_send_receive() {
./!dots(1)

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

  Dprintf("Send msg size: %lu\n", data_out->len - data_out->cur);
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

./!dots(-1)
}
```

### Reference to parent structure

We want to be able to reference the structure of the higher level structure, the buffered socket in particular from the socket struct.
We do not want to expose the sparrow socket struct to the higher levels, thus we implement accesor functions.

```c sparrow.c.dna
function sparrow_socket_parent_reference() {
./!dots(1)

void sparrow_socket_set_parent(sparrow_socket_t * sock, void * parent) {
  sock->parent = parent;
}

void * sparrow_socket_get_parent(sparrow_socket_t * sock) {
  return sock->parent;
}

./!dots(-1)
}

```

### Set timeout {#Set_timeout}

This function simply sets the timeout for sparrow. It is up to the higher level to update this timeout if more than one timeout events need to be handled.

```c sparrow.c.dna
function set_timeout_function() {
./!dots(1)

//The timeout should be changed when the data have been sent received. It is the job of the serializer/multiplexer to do that but care must be taken to do it correctly. TODO update the comment
void sparrow_set_timeout(sparrow_t * sp, int64_t timeout) {
  if(timeout > 0) {
    sp->t_expiry = now() + timeout;
  } else {
    sp->t_expiry = -1;
  }
}

./!dots(-1)
}
```

### Change of TCP state functions {#TCP_state_functions}

As we have already discussed some TCP state changes happen internally by the sparrow itself. For example there is no reason to listen after a bind because we do it automatically. We also accept new connections automatically.
The implementation in those functions is pretty standard. We use non-blocking sockets because otherwise sparrow_send would block. We have also flagged to allow the reuse of the same port. This is necessary because the integration of this library prohibits the
handling of signals that could allow us to clean the file descriptors after a Control-C event for example.

sparrow_socket_new and sparrow_new simply initialize the stucts. (and create an epoll fd)

```c sparrow.c.dna
function change_of_TCP_state_functions() {
./!dots(1)

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

  struct linger ling_flag;
  ling_flag.l_onoff = 1;
  ling_flag.l_linger = sp->default_ot / 1000;
  rc = setsockopt(sfd,SOL_SOCKET,SO_LINGER, (char *) &ling_flag,sizeof(struct linger));
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

  struct linger ling_flag;
  ling_flag.l_onoff = 1;
  ling_flag.l_linger = sp->default_ot / 1000;
  rc = setsockopt(sfd,SOL_SOCKET,SO_LINGER, (char *) &ling_flag,sizeof(struct linger));
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
  printf("Connection closed: %d\n", sock->fd);
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


./!dots(-1)
}
```

### Handling Output Timeout Errors

```c sparrow.c.dna
function sparrow_handle_ot_errors() {
./!dots(1)

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

./!dots(-1)
}
```

### The Sparrow_wait function {#Sparrow_wait}

This function is the one that does most of the work.

First it checks for expired actions and returns one if it exists.
Secondly it checks for cached events and processes them. If there are not any cached event it waits till there are new events that it then caches.

Keep in mind that we close the connection and return an error event on all errors. We also abort the application if the error is Operating system specific.

Thus the only remaining events that need to be handled are EPOLLOUT and EPOLLIN.

For EPOLLOUT, we simply send more data. If have send all the data, we simply stop waiting for EPOLLOUT events for that socket.

For EPOLLIN, if the socket is listening, we accept the new connection and return a "new connection" event with the new socket.
If we have new data, we receive as much as we can and immediately return a "RECV event".

```c sparrow.c.dna
function sparrow_wait_function() {
./!dots(1)

//internal use in sparrow_wait
sparrow_socket_t * find_sock(sparrow_t * sp, sparrow_event_t * spev, int fd) {
  sparrow_socket_t find_sock;
  find_sock.fd = fd; 
  sparrow_socket_t * sock = RB_FIND(fd_rb_t, &(sp->fd_rb_socks), &find_sock);

  spev->sock = sock;
  spev->fd = sock->fd;
  spev->parent = sock->parent;

  return sock;
}

//Internal
//Requires an array of MAX_EVENT units.
int _sparrow_wait(sparrow_t * sp, sparrow_event_t * spev, int only_output) {
  spev->event = 0;
  int64_t timeout;

  if(sparrow_handle_expired_ot(sp, spev, &timeout)) {
    return 0;
  }

  // We immediately return if there are no outputs to send
  if(only_output) {
    timeout = MIN_OUTPUT_WAIT;
  }

  if(sp->events_len == 0) {
    Dprintf("Timeout: %ld\n", timeout);
    sp->event_cur = 0;
    sp->is_cur_output = 1;
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, timeout);

    if((sp->t_expiry >= 0) && (sp->t_expiry - now() < 0)) {
      sp->t_expiry = -1;
      spev->event = 32;
      return 0;
    }
  }

  int i;
  if(sp->is_cur_output) {
    for( i = sp->event_cur; i < sp->events_len; i++) {
      int event = sp->events[i].events;
  
  
        //On error
      if((event & EPOLLERR) || (event & EPOLLHUP)) {
        //The socket might have been destroyed even though we still had events to process.
        sparrow_socket_t * sock = find_sock(sp, spev, sp->events[i].data.fd);
        if(sock == NULL) {
          continue;
        }

        printf("EPOLLERR || EPOLLHUP error\n");
        sparrow_socket_close(sp, sock);
        spev->event = 8;
        sp->events[i].events = 0;

        sp->event_cur++;
        return 0;
      }

      if(event & EPOLLOUT) {
        //The socket might have been destroyed even though we still had events to process.
        sparrow_socket_t * sock = find_sock(sp, spev, sp->events[i].data.fd);
        if(sock == NULL) {
          continue;
        }

        data_out_t *data_out = &(sock->data_out);
        assert(data_out->len > data_out->cur);
        assert(data_out->len != 0);
        Dprintf("Send msg size: %lu\n", data_out->len - data_out->cur);
        int result = send(sock->fd, data_out->data + data_out->cur, data_out->len - data_out->cur, 0);
  
        //On error
        if(result < 0) {
          sparrow_socket_close(sp,sock);
          spev->event = 8;
          sp->events[i].events = 0;
          printf("Send error inside _sparrow_wait.\n");
          sp->event_cur++;
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

          sp->event_cur++;
          return 0;
        } else {
          data_out->cur += result;

          sp->event_cur++;
          return 1;
        }
      }
    }
    sp->event_cur = 0;
    sp->is_cur_output = 0;
  } 

  if(!sp->is_cur_output) {
    if(only_output) {
      sp->events_len = 0;
      //We do not care for the timeout. We immediately return.
      return 0;
    }

    for( i = sp->event_cur; i < sp->events_len; i++) {
      int event = sp->events[i].events;
  
      if(event & EPOLLIN) {

        //The socket might have been destroyed even though we still had events to process.
        sparrow_socket_t * sock = find_sock(sp, spev, sp->events[i].data.fd);
        if(sock == NULL) {
          continue;
        }


        if(sock->listening) {
        // We accept a new client.
          spev->sock = sparrow_socket_accept(sp, sock);
          Dprintf("Listening Socket:\nfd:%d\n",sock->fd);
          spev->fd = spev->sock->fd;
          spev->parent = spev->sock->parent;
          spev->event += 16;
          //Clear the bit
          sp->events[i].events &= ~EPOLLIN;

          sp->event_cur++;
          return 0;

        } else {
          data_in_t *data_in = &(sock->data_in);

          Dprintf("Receiving Socket:\nfd:%d\n",sock->fd);
          
          //If we get data that we did not expect we close the connection. This could also happen when the other closes the connection.
          if(data_in->len == 0) {
            printf("We got data that we did not expect or we received a signal that the connection closed.\nWe are closing the connection.\n");
            sparrow_socket_close(sp,sock);
            spev->event = 8;
            sp->events[i].events = 0;

            sp->event_cur++;
            return 0;
          }
  
          int result = recv(sock->fd, data_in->data , data_in->len , 0);
  
          //On error or connection closed.
          if(result <= 0) {
            printf("Receive error or we received a signal that the connection closed.\nWe are closing the connection.\n");
            sparrow_socket_close(sp,sock);
            spev->event = 8;
            sp->events[i].events = 0;

            sp->event_cur++;
            return 0;
          }
  
          spev->cur = result;
          spev->event += 4;
          data_in->len = 0;
          sp->events[i].events &= ~EPOLLIN;

          sp->event_cur++;
          return 0;
        }
      }
    }
    sp->events_len = 0;
  }

  return 1;
}

void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev, int only_output) {

  while(_sparrow_wait(sp, spev, only_output)) {
  }
}


./!dots(-1)
}
```

### The remaining Code {#Remaining_code_sparrow_wrapper}

This is the main file in which all code is inserted. What is left writing here are the definitions and the inclusions of header files.

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
// #define MAX_SEND_QUEUE 10
// #define MAX_INPUT_DELAY 20
#define MIN_OTIMEOUT_SAMPLE_INTERVAL 100
#define MIN_OUTPUT_WAIT 10

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

./!dots(-1)
data_buffer_definitions(); 

sparrow_socket_definition();

tree_generation();

sparrow_definition();

external_socket_traversal();

set_timeout_function();

sparrow_send_receive();

sparrow_socket_parent_reference();

change_of_TCP_state_functions();

sparrow_handle_ot_errors(); 

sparrow_wait_function();

./!dots(1)

```








       </div>
    </div>
</body>
</html>
