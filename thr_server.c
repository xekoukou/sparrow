#include "sparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9001");
  sparrow_event_t spev;


  char *data = malloc(50);


  sparrow_wait(sp,&spev);
  int64_t time = now();
    if(spev.event & 8) {
      printf("An error occured\n");
      return -1;
    }
    if(spev.event & 16) {
      sparrow_recv(sp, spev.sock, data,50);
    }



  int i = 0;
  while (i < 2000000) {
    sparrow_wait(sp,&spev);
    if(spev.event & 8) {
      printf("An error occured\n");
      break;
    }
    if(spev.event & 4) {
      if(spev.cur == 50) {
        char * data_in = sparrow_socket_data_in(spev.sock);
        Dprintf("Received :\n%s\n",data_in);
        sparrow_recv(sp, spev.sock, data,50);
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

