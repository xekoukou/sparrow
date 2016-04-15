#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9003");
  sparrow_event_t spev;
  int i;
  for(i = 0; i < 1000; i++) {
    sparrow_wait(sp,&spev);
    if(spev.error == 1)
      continue;
    if(spev.event & 16) {
      char *data = malloc(50);
      sparrow_recv(sp, spev.sock, data,50);
    }
    if(spev.event & 4) {
      char * data_out = sparrow_socket_data_in(spev.sock);
      printf("Received :\n%s\n",data_out);
      free(data_out);
    }
  }

  return 0;
}

