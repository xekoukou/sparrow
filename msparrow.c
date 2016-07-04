#include "msparrow.h"
#include "bsparrow.h"
#include<string.h> 
#include<assert.h> 

void msparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  bsparrow_recv(bsp, bsock, 8);
}


//Internal use only.
void * get_data(bsparrow_event_t * bspev,  uint64_t * size) {
  char * data = NULL;

  size_t position = 0;
  size_t step_position = 0;
  buffer_list_t * iter = bspev->list;

  if(bspev->first_buffer_length > 0) {
     if(8 > bspev->first_buffer_length) {
      memcpy(size, bspev->first_buffer, bspev->first_buffer_length);
      position = bspev->first_buffer_length;
    } else {
      memcpy(size, bspev->first_buffer, 8);
      if(*size + 8 > bspev->total_length) {
        return NULL;
      } else {
        data = scalloc(1, *size);
      }
      goto step_zero;
    }
  }

  if(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);    //length here must be big enough to have the 8 bits.
    assert(length >= (8 - position));
    memcpy(size + position, buffer, 8 - position);
    if(*size + 8 > bspev->total_length) {
      return NULL;
    } else {
      data = scalloc(1, *size);
    }
    memcpy(data, buffer - (8 - position), length - (8 - position));   
    position = length - (8 - position);
    goto step_one;
  }
 
  if(bspev->last_buffer_length > 8 - position) {
    memcpy(size + position, bspev->last_buffer, 8 - position);
    if(*size + 8 > bspev->total_length) {
      return NULL;
    } else {
      data = scalloc(1, *size);
    }
    step_position = 8 - position;
    position = 0;
    goto step_two;
  }

  assert(1 == 0);

step_zero: ;

  if(bspev->first_buffer_length - 8 > 0) {
    if(*size > bspev->first_buffer_length - 8) {
      memcpy(data, bspev->first_buffer + 8, bspev->first_buffer_length - 8);
      position = bspev->first_buffer_length;
    } else {
      memcpy(data, bspev->first_buffer + 8, *size);
      return data;
    }
  }

step_one: ;

  while(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);
    memcpy(data + position, buffer, length);
    position += length;
  }

step_two: ;
 
  if(bspev->last_buffer_length) {
    memcpy(data + position, bspev->last_buffer + step_position, *size - position);
  }

  return data;
}

int msparrow_get_msg(bsparrow_t * bsp, bsparrow_event_t * bspev, msparrow_msg_t * msg) {
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

