#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev, 0);


  if(spev.event & 16) {
    char *data = scalloc(1, 50);
    sparrow_recv(sp, spev.sock, data,50);
  }
  //New Msg
  sparrow_wait(sp,&spev, 0);
  if(spev.event & 4) {
    char * data_out = sparrow_socket_data_in(spev.sock);
    printf("Received :\n%s\n",data_out);
    free(data_out);
  }

  sparrow_close(&sp);
  return 0;
}

