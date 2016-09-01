#include "msparrow.h"
#include "bsparrow.h"
#include<string.h> 
#include<stdio.h> 
#include<assert.h> 

void msparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock) {
  bsparrow_recv(bsp, bsock, 8);
}


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
    assert(length >= (8 - eight_position));
    memcpy((char *) size + eight_position, buffer, 8 - eight_position);
    if(*size + 8 > bspev->total_length) {
      return NULL;
    } else {
      data = scalloc(1, *size);
    }
    memcpy(data, buffer + (8 - eight_position), length - (8 - eight_position));   
    position_of_next_copy = length - (8 - eight_position);
    goto step_one;
  }

  assert(bspev->last_buffer_length >= 8 - eight_position);

  memcpy((char *) size + eight_position, bspev->last_buffer, 8 - eight_position);
  if(*size + 8 > bspev->total_length) {
    return NULL;
  } else {
    data = scalloc(1, *size);
  }
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
