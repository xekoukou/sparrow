#include "msparrow.h"
#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

void printmsg(msparrow_msg_t msg) {

  Dprintf("Received :\n\n%s\n\n", msg.data);
  Dprintf("Length : %lu\n", msg.len);

  free(msg.data);

}

void get_msg(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev, msparrow_msg_t * msg) {
  msparrow_recv(bsp, bsock);

  while(1) {
    bsparrow_set_timeout(bsp, 5000);
    bsparrow_wait(bsp, bspev, 0);

    if(bspev->event & 4) {
      bsparrow_set_timeout(bsp, -1);
      if(msparrow_get_msg(bsp, bspev, msg)) {
        return;
      }
    }

    if(bspev->event & 32) {
      printf("timeout error. The client must have crushed");
      exit(-1);
    }
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
      uint64_t temp = msg_size - 8;
      memcpy(data, &temp, 8);
      sprintf(data + 8,"Hello there!");
      bsparrow_send(bsp, bsock, &data, msg_size);
      Dprintf("I: %d\n", i);
      i++;
    }

    //Getting an unknowledge msg after every 100 msgs
    bsparrow_event_t bspev ={0};
    msparrow_msg_t msg;
    get_msg(bsp, bsock, &bspev, &msg);
    printmsg(msg);
    Dprintf("J: %d\n", j);
    j++;

  }
  printf("I finished sending the data.\n");


  //Getting an unknowledge msg
  bsparrow_event_t bspev ={0};
  msparrow_msg_t msg;
  get_msg(bsp, bsock, &bspev, &msg);
  printmsg(msg);

  bsparrow_destroy(&bsp);
  return 0;

}

