#include "msparrow.h"
#include "bsparrow.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
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


void results(int i, int64_t time, int msg_size) {
  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Length : %d\n", msg_size);
  printf("Msgs received: %d\n", i);
}

int main(int argc, char ** argv) {
  
  assert(argc == 3);
  uint64_t msg_size = atoi(argv[1]);
  int loop_length = atoi(argv[2]);

  bsparrow_t * bsp = bsparrow_new(50000, 4000, 2, 2, 1, "9003");

  bsparrow_event_t bspev;
  bsparrow_socket_t * bsock;
  bsparrow_wait(bsp, &bspev, 0);

  if(bspev.event & 16) {
    bsock = bspev.bsock;
    bsparrow_socket_assign_id(bsock, 1);
  } else {
    exit(-1);
  }
  
  msparrow_msg_t msg;
  int j = 0;
  int64_t time = now();
  while(j < loop_length) {
    int i = 0;
    while(i < 10000) {
      if(i == 5000) {
        char *data = scalloc(1, 100);
        uint64_t temp = 92;
        memcpy(data, &temp, 8);
        sprintf(data + 8,"Got 50, need mooooreee!");
        bsparrow_send(bsp, bsock, &data, 100);
        Dprintf("I am sending an aknowledge msg at msg number: %lu\n", j*100 + 50);
      }
      get_msg(bsp, bsock, &bspev, &msg); 
    
      Dprintf("i: %d\n", i); 
      Dprintf("Remaining length: %lu\n", bspev.total_length -msg_size);
      printmsg(msg);
      i++;
    }
    Dprintf("j: %d\n", j); 
    Dprintf("Remaining length: %lu\n", bspev.total_length -msg_size);
    j++;
  }

  printf("Sending: Got them all, thanks!\n");
  char *data = scalloc(1, 100);
  uint64_t temp = 92;
  memcpy(data, &temp, 8);
  sprintf(data + 8, "Got them all, thanks!");
  bsparrow_send(bsp, bsock, &data, 100);
  results(j*10000, time, msg_size);

  bsparrow_destroy(&bsp);
  return 0;
}

