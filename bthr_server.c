#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MSG_SIZE 40000

void results(int i, int64_t time) {
  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Length : %d\n", MSG_SIZE);
  printf("Msgs received: %d\n", i);
}

int main(void) {

  bsparrow_t * bsp = bsparrow_new(50000, 1000, 100, 1, "9003");

  bsparrow_event_t bspev;
  bsparrow_wait(bsp, &bspev);

  if(bspev.event & 16) {
    bsparrow_socket_assign_id(bspev.bsock, 1);
  }
  
  int j = 0;
  int64_t time = now();
  while(j < 20000) {
    int i = 0;
    while(i < 100) {
      if(i == 50) {
        char *data = scalloc(1, 100);
        sprintf(data,"Got 50, need mooooreee!");
        bsparrow_send(bsp, bspev.bsock, &data, 100);
      }
      while(1) {
        bsparrow_recv(bsp, bspev.bsock, MSG_SIZE);
        bsparrow_immediate_event(bsp, &bspev);
    
    
        if(bspev.event & 8) {
          printf("An error occured.\n");
          results(j*100 + i, time);
          exit(1);
        }
        if(bspev.event & 4) {
          if(bspev.total_length >= MSG_SIZE) {
            break;
          }
          continue;
        }
    
    
        bsparrow_wait(bsp, &bspev);
        if(bspev.event & 8) {
          printf("An error occured.\n");
          results(j*100 + i, time);
          exit(1);
        }
    
        if(bspev.event & 4) {
          if(bspev.total_length >= MSG_SIZE) {
            break;
          }
        }
    
      }
      
      //Copy the msg to a new buffer.
      char * msg = scalloc(1, MSG_SIZE);
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
      Dprintf("Length : %d\n", MSG_SIZE);
      Dprintf("Msgs received : %d\n", i);
  
      bsparrow_got_some(bsp, bspev.bsock, MSG_SIZE);
      free(msg);
      i++;
    }
    j++;
  }

  char *data = scalloc(1, 100);
  sprintf(data,"Got them all, thanks!");
  bsparrow_send(bsp, bspev.bsock, &data, 100);

  results(j*100, time);

  bsparrow_destroy(&bsp);
  return 0;
}

