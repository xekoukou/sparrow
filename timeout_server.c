#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev);

  if(spev.event & 16) {
    char *data = malloc(50);
    sparrow_socket_set_timeout(sp, 5000);
    sparrow_recv(sp, spev.sock, data,50);
  }

  sparrow_wait(sp,&spev);
  if(spev.event & 32) {
    printf("Recv timeout expired\n");
    return -1;
  }

  return 0;
}

