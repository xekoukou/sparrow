#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev, 0);

  if(spev.event & 16) {
    char *data = scalloc(1, 50);
    sparrow_set_timeout(sp, 5000);
    sparrow_recv(sp, spev.sock, data,50);
  }

  sparrow_wait(sp,&spev, 0);
  if(spev.event & 32) {
    printf("Recv timeout expired\n");
    return -1;
  }

  return 0;
}

