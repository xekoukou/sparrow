
#include "sparrow.h"
#include "bsparrow.h"
#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include<assert.h>
#include "tree.h"


//TODO We need an initialization function for the buffer socket. It is performed if there are stored session in hd or if a new session is requested from the network or initiated by us.


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
    if(!bsock->we_connected) {
      bsparrow_socket_internal_destroy(bsp, bsock);
    } else {
      bsock->sock = NULL;
      bsparrow_socket_clean(bsp, bsock);
      bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
    }
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
  
    if(!bsock->we_connected) {
      bsparrow_socket_internal_destroy(bsp, bsock);
    } else {
      bsock->sock = NULL;
      bsparrow_socket_clean(bsp, bsock);
      bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
    }
  }
}


void bsparrow_send_idris(bsparrow_t * bsp, bsparrow_socket_t * bsock, char * data, size_t len) {
  char * data_ = data;
  bsparrow_send(bsp, bsock, &data_, len);
}




//TODO The len should never decrease.
void bsparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t len) {

  if(bsock->operational == 1) {
    //All immediate events should have already be handled before waiting for more.
    assert(bsp->ibspev_list == NULL);
          
    buffer_in_t * buffer = &(bsock->buff_in);
    
    //We already have the data.
    if(buffer->total_length_received >= len) {
      bsparrow_event_t * bspev = &(bsock->imbspev);
  
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

