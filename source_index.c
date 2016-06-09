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


# Sparrow Multiplexer

```c sparrow_multiplexer.c
// #include "sparrow_multiplexer.h"

struct sparrow_multiplexer_t {
  int sequenced; //Boolean indicating whether we have a single sequence of communication or multiple.
  int allInOneGo;  //All-in-one-go multiplexers are agnostic. IMPORTANT : One step before the subgraph starts, all other paths are
  // suspended till this subgraph finishes. This way, we do not require a signal to be transmitted to initiate the allinonego subgraph, 
  // allowing our library to be used to implement all types of protocols. (that do not have that signal).
  int agnostic; // It requires allInOneGo. It puts the continuation state inside the data.
  //We need to be able to represent the graph of interactions that this multiplexer represents as well as the position that it currently is.
  //We also need to have a way that other multiplexers can make requests to this multiplexer without knowing whether it is the multiplexer or the sparrow buffer. Timeouts need to be given to the multiplexer that made them so as to handle them as they see fit.
  //That could produce a hierarchy of timeouts.
  int multi_party_token_persistent; //Needed for multi-party protocols to guarantee agent-consistency.
  int persistent;//TODO Clarification: We have a multi-party token that is kept while connections might close and we have a different concept in which we save the current state into HDrive when a timeout expires. The second case requires that we search for this token in the database when a new connection arrives.
};




```

# Sparrow buffer {#Sparrow_buffer}

//TODO Clean this.

Sparrow_buffer is used to accept send and receive requests by our application, internally queue them till sparrow is able to process them. Internally,
it uses 2 buffers per input/output per socket. Their size are supposed to be higher than the average size of an object in our application. The reason
we use two buffers is that this way , we can serialize multiple objects without fear that we will not have space to process the second one. This way, we can put two or more objects in the same buffer and thus minimize the system calls.
If we do this for the output, then the input of the other process will need to keep two buffers to be able to deserialize one object without having to copy it to a new memory location. 

Ofcourse, this technique is only applicable when the size of an object is upper bounded or of fixed size. For objects that we do not know their size, we simply allocate a new piece of memory.

Since, we may have multiple send requests that are in the queue, our output buffer queue might need to expand.


The Maximum number of concurrent receive requests / send request are known beforehand thus, we can preallocate a number of input_timebuffers / output_buffers.


//TODO We need to know the level of the multiplexer that an input or output is for.

```c sparrow_buffer.c
#include "sparrow.h"
//#include "sparrow_buff.h"
//#include "sparrow_multiplexer.h"
#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include<assert.h>
#include "tree.h"




//TODO We need an initialization function for the buffer socket. It is performed if there are stored session in hd or if a new session is requested from the network or initiated by us.

struct buffer_list_t {
  void * data;
  int should_be_freed;
  struct buffer_list_t * next;
};

typedef struct buffer_list_t buffer_list_t;


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

struct buffer_out_t {
  size_t len;
  char * allocated_memory;
  char * default_memory;
};

typedef struct buffer_in_t buffer_in_t;
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
 oq->requests = scalloc(sizeof(out_request_t) * 10);
 oq->len = 10;
 oq->first_free_pos = 0;
 oq->last_free_pos = 9;
}

int oqueue_next(oqueue_t * oq, int i) {
  if(oq->len == (i + 1)) {
    return 0;
  } else {
    return i + 1;
  }
}

void oqueue_push_req(oqueue_t * oq, out_request_t * oreq) {
  //Increase the queue if almost full.
  if(oq->first_free_pos == oq->last_free_pos) {
    out_request_t * reqs = scalloc(sizeof(out_request_t) * oq->len * 10);
    int i;
    int j = 0;
    for(i = oq->last_free_pos + 1; i != oq->last_free_pos; i = oqueue_next(oq,i)) {
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

  if(oq->pos_filled > 0) {
    int pos = oqueue_next(oq, oq->last_free_pos);
    assert(pos != oq->first_free_pos);
  
    oq->last_free_pos = pos;
    oq->pos_filled--;
  
     //Decrease the queue if almost empty.
    if((oq->len > 10) && (oq->pos_filled < (oq->len / 10))) {
      out_request_t * reqs = scalloc(sizeof(out_request_t) * oq->len / 10);
      int i;
      int j = 0;
      for(i = oq->last_free_pos + 1; i != oq->last_free_pos; i = oqueue_next(oq,i)) {
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

}

//You need to pop it if you use it. The memory is owned by the queue.
out_request_t * oqueue_oldest_req(oqueue_t * oq) {
  out_request_t * req = NULL;

  if(oq->pos_filled > 0) {
    int pos = oqueue_next(oq, oq->last_free_pos);
    assert(pos != oq->first_free_pos);
    req = &(oq->requests[pos]);
  }

  return req;
}


struct bsparrow_socket_t {
  int64_t id;
  int we_connected;
  char * address;
  char * port;
  sparrow_socket_t * sock;
  buffer_in_t buff_in;
  buffer_out_t buff_out;
  oqueue_t oq;
  int operational;
  int retries;
  int out_more; //Indicates whether the last time we sent data, the socket was ready to receive more immediately.
  int idle_input;  //If the socket is idle it is destroyed since there is no use of it.
  int idle_output;
};

typedef struct bsparrow_socket_t bsparrow_socket_t;


struct non_op_bsock_list_t {
  bsparrow_socket_t * bsock;
  struct non_op_bsock_list_t * next;
};

typedef struct non_op_bsock_list_t non_op_bsock_list_t;

non_op_bsock_list_t * non_op_bsock_list_add(non_op_bsock_list_t * list, bsparrow_socket_t * bsock) {
  assert(bsock->operational == 0);
  non_op_bsock_list_t * item = scalloc(sizeof(non_op_bsock_list_t));
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

struct bsparrow_event_t {
  int event;
  bsparrow_socket_t * bsock;
  char * first_buffer;
  size_t first_buffer_length;
  buffer_list_t * list;
  char * last_buffer;
  size_t last_buffer_length;
};

typedef struct bsparrow_event_t bsparrow_event_t;

struct bsparrow_event_list_t {
  bsparrow_event_t * bspev;
  struct bsparrow_event_list_t * next;
};

typedef struct bsparrow_event_list_t bsparrow_event_list_t;

bsparrow_event_list_t * bsparrow_event_list_add(bsparrow_event_list_t * list, bsparrow_event_t * bspev) {
  bsparrow_event_list_t * item = scalloc(sizeof(bsparrow_event_list_t));
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
};

typedef struct bsparrow_t bsparrow_t;


//Internal use only
void bsparrow_socket_clean(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  //Clean input buffer list
  buffer_in_t * buffer = &(bsock->buff_in);
  buffer_list_t * item = buffer->list;
  buffer_list_t * prev_item;
  while(item != NULL) {
    prev_item = item;
    item = item->next;
    if(prev_item->should_be_freed) {
      free(prev_item->data);
    }
    free(prev_item);
  }

  //Clean the rest probable big_buffers
  if(buffer->prev_data_tag == 2) {
    free(buffer->prev_data);
  }
  if(buffer->new_data_tag == 2) {
    free(buffer->new_data);
  }

}


//Internal use
bsparrow_socket_t * bsparrow_socket_initialize_internal(bsparrow_t * bsp,sparrow_socket_t * sock, int64_t id, int we_connected, char * address, char * port) {
  bsparrow_socket_t * bsock = scalloc(sizeof(bsparrow_socket_t));
  bsock->sock = sock;
  if(sock != NULL) {
    bsock->operational = 1;
  } else {
    //This can only happen when we connect, not when we accept a new connection.
    assert(we_connected == 1);
    bsock->operational = 0;
    bsparrow_socket_clean(bsp, bsock);
    bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
  }
  bsock->id = id;
  bsock->we_connected = we_connected;
  if(we_connected) {
    bsock->address = scalloc(strlen(address) + 1);
    bsock->port = scalloc(strlen(port) + 1);
    strcpy(bsock->address, address);
    strcpy(bsock->port, port);
  }
  sparrow_socket_set_parent(bsock->sock, bsock);
  bsock->buff_in.default_memory = scalloc(bsp->buffer_size);
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

  bsock->buff_in.new_data_len = bsp->buffer_size;
  bsock->buff_out.allocated_memory = scalloc(bsp->buffer_size);
  bsock->buff_out.default_memory = bsock->buff_out.allocated_memory;
  bsock->buff_out.len = bsp->buffer_size;

  bsock->idle_input = 0;
  bsock->idle_output = 0;

  oqueue_new(&(bsock->oq));

  return bsock;
}

bsparrow_socket_t * bsparrow_socket_connect(bsparrow_t * bsp, int64_t id, char * address, char * port) {
  sparrow_socket_t * sock = sparrow_socket_connect(bsp->sp, address, port);
  return bsparrow_socket_initialize_internal(bsp, sock, id, 1, address, port); 
}

//Internal use only We need to pass it to the higher levels to be given an id.
bsparrow_socket_t * bsparrow_socket_accept(bsparrow_t * bsp, sparrow_socket_t * sock) {
  return bsparrow_socket_initialize_internal(bsp, sock, -1 , 0, NULL, NULL);
}

void bsparrow_socket_assign_id(bsparrow_socket_t *bsock, int64_t id) {
  bsock->id = id;
}


//Internal use only
void bsparrow_socket_destroy(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  if(bsock->we_connected) {
    free(bsock->address);
    free(bsock->port);
  }
  if(bsock->operational) {
    sparrow_socket_close(bsp->sp, bsock->sock);
  }
  free(bsock->buff_in.default_memory);
  free(bsock->buff_out.default_memory);

  bsparrow_socket_clean(bsp, bsock);

  free(bsock);
}

bsparrow_t * bsparrow_new(size_t buffer_size, int64_t dtimeout, int listening, char * port) {

  if( ((buffer_size/2) * 2) != buffer_size) {
    printf("Buffer size should be a multiple of 2.\n");
    exit(1);
  }

  bsparrow_t * bsp = scalloc(sizeof(bsparrow_t));
  bsp->sp = sparrow_new(dtimeout);
  bsp->buffer_size = buffer_size;
  if(listening) {
    sparrow_socket_bind(bsp->sp,port);
  }
  return bsp;
}

void bsparrow_socket_set_timeout(bsparrow_t * bsp, int64_t timeout) {
  sparrow_socket_set_timeout(bsp->sp, timeout);
}



//Internal use only
void bsparrow_socket_process_next_out_req(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  int more = 1;
  out_request_t * req;
  sparrow_event_t spev = {0};

  while(bsock->operational && more && ((req = oqueue_oldest_req(&(bsock->oq))) != NULL) ) {
  
    buffer_out_t buffer = bsock->buff_out;
  
    //Free memory if you have to.
    if(buffer.len > bsp->buffer_size) {
      free(buffer.allocated_memory);
      buffer.allocated_memory = buffer.default_memory;
      buffer.len = bsp->buffer_size;
    }
    
    
    if(req->len > buffer.len) {
      buffer.allocated_memory = req->data;
      buffer.len = req->len;
      more = sparrow_send(bsp->sp, bsock->sock, buffer.allocated_memory, buffer.len, &spev);
      oqueue_del_oldest_req(&(bsock->oq));
    } else {
      buffer.len = 0;
      while(buffer.len + req->len <= bsp->buffer_size) {
        memcpy(buffer.allocated_memory + buffer.len, req->data, req->len);
        free(req->data);
        buffer.len += req->len;
        oqueue_del_oldest_req(&(bsock->oq));
        req = oqueue_oldest_req(&(bsock->oq));
      }
      more = sparrow_send(bsp->sp, bsock->sock, buffer.allocated_memory, buffer.len, &spev);
    }
  }
  bsock->out_more = more;
  if(spev.event == 8) {
    assert(bsock->operational == 1);
    bsock->operational = 0;
    assert(bsock->retries == 0);
    if(!bsock->we_connected) {
      bsparrow_event_t * bspev = scalloc(sizeof(bsparrow_event_t));
      bspev->event = 8;
      bspev->bsock = bsock;
      bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev_list, bspev);
    } else {
      bsparrow_socket_clean(bsp, bsock);
      bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
    }
  } 
}


void bsparrow_retry_single(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev) {
  sparrow_socket_t * sock = sparrow_socket_connect(bsp->sp, bsock->address, bsock->port);
  if(sock != NULL) {
    bsock->sock = sock;
    sparrow_socket_set_parent(sock, bsock);
    bsock->operational = 1;

    bsparrow_event_t * bspev = scalloc(sizeof(bsparrow_event_t));
    bspev->event = 32;
    bspev->bsock = bsock;
    bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev_list, bspev);

  } else {
    bsock->retries++;
  }
}


// If one fails completely, return the apropriate event
void bsparrow_retry(bsparrow_t * bsp, bsparrow_event_t * bspev) {
  bspev->event = 0;

  non_op_bsock_list_t * list = bsp->non_op_bsock_list;
  non_op_bsock_list_t * iter = bsp->non_op_bsock_list;
  non_op_bsock_list_t * prev_iter = NULL;
  
  while(iter) {
    bspev->bsock = iter->bsock;
    bsparrow_retry_single(bsp, iter->bsock, bspev);
    if(iter->bsock->operational == 1) {
      bsp->non_op_bsock_list = non_op_bsock_list_rem_next(list, prev_iter);
    } else {
      if(iter->bsock->retries > bsp->max_retries) {
        bsp->non_op_bsock_list = non_op_bsock_list_rem_next(list, prev_iter);
        bspev->event = 8;
        break;
      }
    }
    prev_iter = iter;
    iter = iter->next;
  }
}


int bsparrow_wait_(bsparrow_t * bsp, bsparrow_event_t * bspev) {
  bspev->event = 0;
  
  //IMPORTANT This should always be first because the socket might be considered idle while it already has data. Thus it might be destroyed.
  //Handle Immediate Events first.
  if(bsp->ibspev_list != NULL) {
    memcpy(bspev, bsp->ibspev_list->bspev, sizeof(bsparrow_event_t));
    free(bsp->ibspev_list->bspev);
    bsp->ibspev_list = bsparrow_event_list_rem_next(bsp->ibspev_list, bsp->ibspev_list);
    return 0;
  }

  //Handle Events created due to retry efforts.
  bsparrow_retry(bsp, bspev);
  if(bspev->event != 0) {
    return 0;
  }

  //New events from the network.
  sparrow_event_t spev;
  bsparrow_socket_t * bsock;
    
  sparrow_wait(bsp->sp, &spev);
  int ev = spev.event;
  bsock = sparrow_socket_get_parent(spev.sock);
  bspev->bsock = bsock;

  if((ev >> 1) & 1) {
    if(bsock->oq.pos_filled == 0) {
      bsock->idle_output = 1;
      if(bsock->idle_input == 1) {
        bsparrow_socket_destroy(bsp, bsock);
        bspev->event = 2;
        return 0;
      }
    } 
    bsparrow_socket_process_next_out_req(bsp, bsock);
  }

  //Error or timeout
  if(((ev >> 5) & 1) || ((ev >> 3) & 1)) {
    assert(bsock->operational == 1);
    bsock->operational = 0;
    if(bsock->we_connected) {
      assert(bsock->retries == 0);
      bsparrow_socket_clean(bsp, bsock);
      bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
    } else {
      bspev->event = 8;
      return 0;
    }
  }

  if((ev >> 2) & 1) {
    buffer_in_t * buffer = &(bsock->buff_in);

    if(buffer->residue_length) {
      bspev->first_buffer_length = buffer->residue_length;
      bspev->first_buffer = buffer->prev_data + buffer->residue_start;
    } else {
      bspev->first_buffer_length = 0;
      bspev->first_buffer = NULL;
    }
    bspev->list = buffer->list;
    bspev->last_buffer = buffer->new_data;
    buffer->cur_length = buffer->cur_length + spev.cur;
    buffer->total_length_received += spev.cur;
    bspev->last_buffer_length = buffer->cur_length;
    bsock->idle_input = 1;
    if(bsock->idle_output == 1) {
        bsparrow_socket_destroy(bsp, bsock);
        bspev->event = 2;
    }

    bspev->event += 4;
  }
  //New connection.
  if((ev >> 4) & 1) {
    bsparrow_socket_accept(bsp, spev.sock);
    bspev->event = 16;
  }

  return 0;
}

void bsparrow_send(bsparrow_t * bsp, bsparrow_socket_t * bsock, void * data, size_t len) {
  bsock->idle_output = 0;
  out_request_t req;
  req.data = data;
  req.len = len;
  oqueue_push_req(&(bsock->oq), &req);

  if(bsock->out_more) {
    bsparrow_socket_process_next_out_req(bsp, bsock);
  }
}


//The len should never decrease.
void bsparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t len) {
  buffer_in_t * buffer = &(bsock->buff_in);
  assert(len > buffer->total_length_received);
  
  //We already have the data.
  if(buffer->residue_length > len) {
    bsparrow_event_t * bspev = scalloc(sizeof(bsparrow_event_t));
    bspev->event = 4;
    bspev->bsock = bsock;
    bspev->list = NULL;
    bspev->first_buffer_length = len;
    bspev->first_buffer = buffer->prev_data + buffer->residue_start;  
    bspev->last_buffer_length = 0;
    bspev->last_buffer = NULL;
    bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev_list, bspev);
    return;
  }

  assert(bsock->idle_input == 1);
  bsock->idle_input = 0;

  //If there is still some memory left from the previous buffer keep receiving in it.
  if((len > buffer->total_length_received) & (buffer->new_data_len == buffer->cur_length)) { 

    //We push the new data into the list
    buffer_list_t * item = scalloc(sizeof(buffer_list_t));
    if(buffer->new_data_tag !=2) {
      item->should_be_freed = 0;
    } else {
      item->should_be_freed = 1;
    }
    item->data = buffer->new_data;
    item->next = NULL;
    buffer->last_item->next = item;
    buffer->last_item = item;

    void * new_memory;
    new_memory = scalloc(len - buffer->total_length_received);
    buffer->cur_length = 0;


    buffer->new_data = new_memory;
    buffer->new_data_tag = 2;
    buffer->new_data_len = len - buffer->total_length_received;
  }

  if(bsock->operational == 1) {
    sparrow_recv(bsp->sp, bsock->sock, buffer->new_data + buffer->cur_length, buffer->new_data_len - buffer->cur_length); 
  }
}


void bsparrow_got_some(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t that_much) {
  buffer_in_t * buffer = &(bsock->buff_in);

  //We get all the data that we requested, no less, except the last request.
  assert((buffer->list == NULL) || (that_much >= buffer->total_length_received - buffer->cur_length));
  assert(that_much <= buffer->total_length_received);



  if(that_much < buffer->residue_length) {
    buffer->residue_start = buffer->residue_start + that_much; 
    buffer->residue_length = buffer->residue_length - that_much;
    return;
  }

  if((buffer->residue_length) && (buffer->prev_data_tag = 2)) {
    free(buffer->prev_data);  
  }

  buffer->residue_length = 0;
  
  //Clean list
  buffer_list_t * item = buffer->list;
  buffer_list_t * prev_item;
  while(item != NULL) {
    prev_item = item;
    item = item->next;
    if(prev_item->should_be_freed) {
      free(prev_item->data);
    }
    free(prev_item);
  }

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
    buffer->new_data = buffer->default_memory + bsp->buffer_size / 2;
    buffer->new_data_tag = 1;
  }
}

```





# Epoll Wrapper {#Epoll_Wrapper}

The first thing that we need to do is to provide a wrap around linux epoll that simplifies the api for the asynchronous communications. This wrapper needs to be able to do only one thing.

**Given a buffer, the wrapper needs to be able to send or receive data into it unless a timeout expires.**

There is a small difference between a receive and a send though. Because we want to reduce the number of recv system calls, we provide the wrapper a buffer that might be bigger that the data that are available. If the client doesn't send more data
, that would mean that we would never receive the data that the client already sent. To aleviate this problem, we immediately return as much data as we currently have without waiting to fill the buffer.

## Examples {#Examples}

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

The client simply sents a Msg.It waits till sparrow tells it that it sent it and exits.

```c simple_test_client.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
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

Everything looks great till now, but reality is different than the constructs we use to have in our heads. We might expect a msg to come but that msg might never come. We need to be able to cancel our order to receive or send a msg. The way we detect failures is by waiting for a period of time before we give up. That is the meaning of setting a timeout.

Sparrow requires the precise time that a request will expire. To find the current time, we call the 'now' function.

```c timeout_server.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev);

  if(spev.event & 16) {
    char *data = malloc(50);
    sparrow_socket_set_timeout(sp, 5000);
    sparrow_recv(sp, spev.sock, data,50);
  }

  sparrow_wait(sp,&spev);
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

//TODO It is assumed that in case the second agent crashes, there are more reliable ways of reacting to it than knowing that the ouptput msg never reached the destination. The msg might have been on the wire before the agent crashed.

```c ot_test_server.c
#include "sparrow.h"
#include <stdio.h>
#include <unistd.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev);

  if(spev.event & 16) {
    printf("we connected and now we will wait for a period so that the client output timeout expires.\n");
    sleep(4);
  }

  sparrow_wait(sp,&spev);
  return 0;
}

```


```c ot_test_client.c
#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(1000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  char *data = malloc(50);
  sprintf(data,"Hello there!");

  sparrow_event_t spev;
  sparrow_send(sp, sock, data, 50, &spev);

  sparrow_wait(sp,&spev);

  if(spev.event & 8) {
    printf("An error occured, in this case an output timeout expiry since the server crashed.\n");
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
  
  char *data = malloc(50);
  
  sparrow_event_t spev;
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

  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9001");

  char *data = malloc(50);

  sparrow_event_t spev;
  spev.event = 0;
  int sent_immediately = 1;
  int i = 0;

  while(i < 2000000) {

    if((spev.event & 2) || (sent_immediately == 1)) {
      sprintf(data,"Hello there!");
      sent_immediately = sparrow_send(sp, sock, data, 50, &spev);
      if(spev.event & 8) {
        Dprintf("An error occured");    
        break;
      }
    }

    if(sent_immediately == 0) {
      sparrow_wait(sp,&spev);
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
  sparrow_socket_t * sock;
  size_t cur;
  int event;
};

typedef struct sparrow_event_t sparrow_event_t;

sparrow_t * sparrow_new(int64_t dtimeout);

void sparrow_socket_bind(sparrow_t * sp, char * port);

sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port); 

void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev);

void sparrow_socket_set_timeout(sparrow_t * sp, int64_t timeout);

int sparrow_send( sparrow_t * sp, sparrow_socket_t *sock, void * data, size_t len, sparrow_event_t * spev);

void sparrow_cancel_send( sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_recv( sparrow_t * sp, sparrow_socket_t *sock, void *data, size_t len);

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

void * scalloc(size_t size);
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
  int events_len;
  struct epoll_event events [MAX_EVENTS];
  struct fd_rb_t fd_rb_socks; // A tree container of sockets ordered by the fd.
  struct ot_rb_t ot_rb_socks; // A tree container of sockets ordered by the expiration if their outputs.
  int64_t default_ot;
  int ot_already_expired;
  int64_t timeout;
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
  return (s1->fd > s2->fd) - (s1->fd < s2->fd);
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
    data_out->cur += result;

    struct epoll_event pevent;
    pevent.data.fd = sock->fd;
    pevent.events = EPOLLIN | EPOLLOUT;
    int rc = epoll_ctl (sp->fd, EPOLL_CTL_MOD, sock->fd, &pevent);
    if (rc == -1) {
      perror(" epoll_ctl failed to modify a socket to epoll");
      exit(-1);
    }

    sock->out_expiry = now() + sp->default_ot;
    
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

//The timeout should be changed when the data have been sent received. It is the job of the serializer/multiplexer to do that but care must be taken to do it correctly.
void sparrow_socket_set_timeout(sparrow_t * sp, int64_t timeout) {
  sp->timeout = timeout;
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
  sparrow_t * sp = scalloc(sizeof(sparrow_t));
  int fd = epoll_create1 (0);
  if (fd == -1) {
    perror("epoll_create1 failed to create epoll.");
    exit(-1);
  }
  sp->fd = fd;
  sp->events_len = 0;
  RB_INIT(&(sp->fd_rb_socks));
  RB_INIT(&(sp->ot_rb_socks));
  sp->timeout = -1;
  sp->ot_already_expired = 0;
  sp->default_ot = dtimeout;
  return sp;
}


//internal use only.
sparrow_socket_t * sparrow_socket_new(int fd) {
  sparrow_socket_t * sock = scalloc(sizeof(sparrow_socket_t));
  sock->fd = fd;
  sock->out_expiry = -1;
  return sock;
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
  sparrow_socket_t * sock = RB_MIN(ot_rb_t, &(sp->ot_rb_socks));
  if(sp->ot_already_expired > 0) {
    RB_REMOVE(ot_rb_t, &(sp->ot_rb_socks), sock);
    sp->ot_already_expired--;
    spev->sock = sock;
    spev->event = 8;
    return 1;
  }
  if(sock !=NULL) {
    int64_t time = now();
    sparrow_socket_t * iter = sock;
    while ((iter != NULL) && (iter->out_expiry - time < 0 )) {
      sp->ot_already_expired++;
      iter = RB_NEXT(ot_rb_t, &(sp->ot_rb_socks), iter);
    }
    if(sp->ot_already_expired > 0) {
      RB_REMOVE(ot_rb_t, &(sp->ot_rb_socks), sock);
      sp->ot_already_expired--;
      spev->sock = sock;
      sparrow_socket_close(sp, sock);
      spev->event = 8;
      return 1;
    }
    *timeout = sock->out_expiry - time;
    if(sp->timeout < *timeout) {
      *timeout = sp->timeout;
    }
  } else {
    *timeout = sp->timeout;
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

//Internal
//Requires an array of MAX_EVENT units.
int _sparrow_wait(sparrow_t * sp, sparrow_event_t * spev) {
  spev->event = 0;
  int64_t timeout;

  if(sparrow_handle_expired_ot(sp, spev, &timeout)) {
    return 0;
  }

  if(sp->events_len == 0) {
    sp->events_len = epoll_wait(sp->fd, sp->events, MAX_EVENTS, sp->timeout);
    if(sp->events_len == 0) {
      spev->event = 32;
      return 0;
    }
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
        printf("EPOLLERR || EPOLLHUP error.\n");
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
          exit(-1);
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

void * scalloc(size_t size) {
  void * result = calloc(1,size);
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
