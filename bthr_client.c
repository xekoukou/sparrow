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

