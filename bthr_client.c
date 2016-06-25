#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MSG_SIZE 40000

int main(void) {

  bsparrow_t * bsp = bsparrow_new(50000, 1000, 100, 0, NULL);
  bsparrow_socket_t * bsock = bsparrow_socket_connect(bsp, 1, "127.0.0.1", "9003");
  
  int j = 0;
  while(j < 20000) {
    int i = 0;
    while(i < 100) {
      char *data = scalloc(1, MSG_SIZE);
      sprintf(data,"Hello there!");
      bsparrow_send(bsp, bsock, &data, MSG_SIZE);
      bsparrow_event_t bspev;
      bsparrow_immediate_event(bsp, &bspev);
      if(bspev.event & 8) {
        printf("An error occured.\n");
        exit(0);
      }
      i++;
    }

  //Getting an unknowledge msg after every 100 msgs
  bsparrow_event_t bspev ={0};

  while(1) {
    bsparrow_recv(bsp, bsock, 100);
    bsparrow_immediate_event(bsp, &bspev);
    
    
    if(bspev.event & 8) {
      printf("An error occured.\n");
      exit(1);
    }
  
    if(!(bspev.event & 4)) {
      bsparrow_wait(bsp, &bspev);
    }
    
    if(bspev.event & 8) {
      printf("An error occured.\n");
      exit(1);
    }
    
    assert(bspev.event & 4); 
    if(bspev.total_length >= 100) {
      break;
    }
  }


  //Copy the msg to a new buffer.
  char * msg = scalloc(1, 100);
  size_t position = 0;
  if(bspev.first_buffer_length > 0) {
    memcpy(msg, bspev.first_buffer, bspev.first_buffer_length);
    position = bspev.first_buffer_length;
  }
  buffer_list_t * iter = bspev.list;

  while(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);
    memcpy(msg + position, buffer, length);
    position += length;
  }

  memcpy(msg + position, bspev.last_buffer, bspev.last_buffer_length);
  Dprintf("Received :\n\n%s\n\n", msg);
  Dprintf("Length : %d\n", 100);
  bsparrow_got_some(bsp, bspev.bsock, 100);
  free(msg);


    j++;
  }
  printf("I finished sending the data.\n");


  //Getting an unknowledge msg
  bsparrow_event_t bspev ={0};
  bsparrow_recv(bsp, bsock, 100);
  bsparrow_immediate_event(bsp, &bspev);
  
  
  if(bspev.event & 8) {
    printf("An error occured.\n");
    exit(1);
  }

  if(!(bspev.event & 4)) {
    bsparrow_wait(bsp, &bspev);
  }
  
  if(bspev.event & 8) {
    printf("An error occured.\n");
    exit(1);
  }
  
  assert(bspev.event & 4); 


  //Copy the msg to a new buffer.
  char * msg = scalloc(1, 100);
  size_t position = 0;
  if(bspev.first_buffer_length > 0) {
    memcpy(msg, bspev.first_buffer, bspev.first_buffer_length);
    position = bspev.first_buffer_length;
  }
  buffer_list_t * iter = bspev.list;

  while(iter != NULL) {
    char * buffer;
    size_t length;
    iter = buffer_list_next(iter, &buffer, &length);
    memcpy(msg + position, buffer, length);
    position += length;
  }

  memcpy(msg + position, bspev.last_buffer, bspev.last_buffer_length);
  printf("Received :\n\n%s\n\n", msg);
  printf("Length : %d\n", 100);

  free(msg);


  bsparrow_destroy(&bsp);
  return 0;

}

