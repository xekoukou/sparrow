#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {

  bsparrow_t * bsp = bsparrow_new(100, 5000, 0, NULL);
  bsparrow_socket_t * bsock = bsparrow_socket_connect(bsp, 1, "127.0.0.1", "9003");
  
  int i = 0;
  while(i < 800000) {
    char *data = scalloc(1, 50);
    sprintf(data,"Hello there!");
    bsparrow_send(bsp, bsock, &data, 50);
    bsparrow_event_t bspev;
    bsparrow_immediate_event(bsp, &bspev);
    if(bspev.event & 8) {
      printf("An error occured.\n");
      exit(0);
    }
    i++;
  }
  printf("I finished sending the data.\n");
  bsparrow_destroy(&bsp);
  return 0;

}

