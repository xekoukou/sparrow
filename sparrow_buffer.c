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
  assert(bspev->operational == 0);
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
  int default_max_retries;
  non_op_bsock_list_t * non_op_list;
  bsparrow_event_list_t ibspev_list;  //An event that is triggered immediate after a function call and that we want to save so as
  // to be handled by bsparrow_wait itself (rather than handled separately.)
};

typedef struct bsparrow_t bsparrow_t;


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
int bsparrow_socket_process_next_out_req(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
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
    assert(bsock->retries == 0);
    if(!bsock->we_connected) {
      bsparrow_event_t * bspev = scalloc(sizeof(bsparrow_event_t));
      bspev->event = 8;
      bspev->bsock = bsock;
      bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev, bspev);
    } else {
      bsock->operational = 0;
      bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
    }
    return 1;
  } else {
    return 0;
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
    if(bsock->operational == 1) {
      bsp->non_op_bsock_list = non_op_block_list_rem_next(list, prev_iter);
    } else {
      if(bsock->retries > bsp->max_retries) {
        bsp->non_op_bsock_list = non_op_block_list_rem_next(list, prev_iter);
        bspev->event = 8;
        break;
      }
    }
    prev_iter = iter;
    iter = iter->next;
  }
}

bsparrow_retry_single(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev) {
  sparrow_socket_t * sock = sparrow_socket_connect(bsp->sp, bsock->address, bsock->port);
  if(sock != NULL) {
    bsock->sock = sock;
    sparrow_socket_set_parent(sock, bsock);
    bsock->operational = 1;

    //retry input and output.
    if(bsock->idle_output == 0) {
      sparrow_event spev = {0};
      int more = sparrow_send(bsp, bsock->sock, bsock->buff_out.allocated_memory, bsock->buff_out.len, spev);  
      bsock->out_more = more;
      if(spev.event == 8) {
        bsock->retries++;
        return;
      }
    }
   
    if(bsock->idle_input == 0) {
      sparrow_recv(bsp->sp, bsock->sock, buffer->new_data + buffer->cur_length, buffer->new_data_len - buffer->cur_length); 
    }
  } else {
    bsock->retries++;
  }
}


int bsparrow_wait_(bsparrow_t * bsp, bsparrow_event_t * bspev) {
  bspev->event = 0;
  
  //IMPORTANT This should always be first because the socket might be considered idle while it already has data. Thus it might be destroyed.
  //Handle Immediate Events first.
  if(bsp->ibspev_list != NULL) {
    memcpy(bspev, bsp->ibspev_list->bspev, sizeof(bsparrow_event_t));
    free(bsp->ibspev_list->bspev);
    bsp->ibspev_list = non_op_block_list_rem_next(bsp->ibspev_list, bspev->ibspev_list);
  }

  //Handle Events created due to retry efforts.
  if(bspev->event == 0) {
    bsparrow_retry(bsp, bspev);
  }

  //New events from the network.
  sparrow_event_t spev;
  bsparrow_socket_t * bsock;
  if(bspev->event == 0) {
    
    sparrow_wait(bsp->sp, &spev);
    int ev = spev.event;
    bsock = sparrow_socket_get_parent(spev.sock);
    bspev->bsock = bsock;
  }

  if((ev >> 1) & 1) {
    if(bsock->oq.pos_filled == 0) {
      bsock->idle_output = 1;
      if(bsock->idle_input == 1) {
        bsparrow_socket_destroy(bsp, bsock);
        bspev->event = 2;
        return 0;
      }
    } 
    if(bsparrow_socket_process_next_out_req(bsp, bsock)) {
      return 0;
    }
    return 1;
  }

  //Error or timeout
  if(((ev >> 5) & 1) || ((ev >> 3) & 1)) {
    assert(bsock->operational == 1);
    bsock->operational = 0;
    if(bsock->we_connected) {
      assert(bsock->retries == 0);
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
      bspev->residue_length = 0;
      bspev->residue = NULL;
    }
    bspev->list = buffer->list;
    bspev->second_buffer = buffer->new_data;
    buffer->cur_length = buffer->cur_length + spev.cur;
    buffer->total_length_received += spev.cur;
    bspev->second_buffer_length = buffer->cur_length;
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
    bspev->list = NULL;
    bspev->first_buffer_length = len;
    bspev->first_buffer = buffer->prev_data + buffer->residue_start;  
    bspev->second_buffer_length = 0;
    bspev->second_buffer = NULL;
    bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev, bspev);
    return;
  }

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

  sparrow_recv(bsp->sp, bsock->sock, buffer->new_data + buffer->cur_length, buffer->new_data_len - buffer->cur_length); 
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

