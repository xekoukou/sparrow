#include "bsparrow.h"
#include <stdio.h>
#include <assert.h>

int main(void) {

  bsparrow_t * bsp = bsparrow_new(100, 5000, 0, NULL);
  bsparrow_socket_t * bsock = bsparrow_socket_connect(bsp, 1, "127.0.0.1", "9003");

  char *data = scalloc(1, 50);
  sprintf(data,"Hello there!");

  bsparrow_event_t bspev;
  bsparrow_send(bsp, bsock, &data, 50);

  bsparrow_set_timeout(bsp, 5000);
  bsparrow_wait(bsp, &bspev);

  assert(bspev.event == 32);
  printf("I sent : Hello there!");
  
  bsparrow_destroy(&bsp);
  return 0;
}

