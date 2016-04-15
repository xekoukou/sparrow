#include "sparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9001");
  sparrow_event_t spev;
  int64_t time = now();
  int i = 0;
  char *data = malloc(50000);
  while (i < 300) {
    sparrow_wait(sp,&spev);
    if(spev.error == 1) {
      Dprintf("An error occured");
      break;
    }
    if(spev.event & 16) {
      sparrow_recv(sp, spev.sock, data,50000);
    }
    if(spev.event & 4) {
      if(spev.cur == 50000) {
        char * data_in = sparrow_socket_data_in(spev.sock);
        Dprintf("Received :\n%s\n",data_in);
        sparrow_recv(sp, spev.sock, data,50000);
        i++;
      }
    }
  }
  int64_t dif_time = (now() - time);
  float rate = ((float) (i+1) * 1000) / ((float) dif_time);
  printf("Rate: %f msgs per second.\n", rate);
  printf("Msgs received: %d\n", i);

  return 0;
}

