#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {

  bsparrow_t * bsp = bsparrow_new(100, 5000, 1, "9003");

  bsparrow_event_t bspev;
  bsparrow_wait(bsp, &bspev);

  if(bspev.event & 16) {
    bsparrow_socket_assign_id(bspev.bsock, 1);
  }
  
  int i = 0;
  int64_t time = now();
  while(i < 800000) { 
    bsparrow_recv(bsp, bspev.bsock, 50);
    bsparrow_immediate_event(bsp, &bspev);
    if(bspev.event & 8) {
      printf("An error occured.\n");
      exit(0);
    }

    bsparrow_wait(bsp, &bspev);
    if(bspev.event & 8) {
      printf("An error occured.\n");
      exit(0);
    }

    if(bspev.event & 4) {
      assert(bspev.first_buffer_length == 0);
      assert(bspev.list == NULL);
      size_t last_buffer_length = bspev.last_buffer_length;
      char * last_buffer = bspev.last_buffer;
      Dprintf("Received :\n%s\n",last_buffer);
      Dprintf("Length :\n%lu\n",last_buffer_length);
      bsparrow_got_some(bsp, bspev.bsock, last_buffer_length);
    }
    i++;
  }

  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Msgs received: %d\n", i);


  bsparrow_destroy(&bsp);
  return 0;
}

