#include "bsparrow.h"
#include <stdio.h>
#include <assert.h>

int main(void) {

  bsparrow_t * bsp = bsparrow_new(100, 5000, 100, 1, "9003");

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

  bsparrow_destroy(&bsp);
  return 0;
}

