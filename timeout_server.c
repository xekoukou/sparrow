#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_bind(sp,"9003");
  sparrow_event_t spev;

  sparrow_wait(sp,&spev);
  if(spev.error == 1)
    return -1;
  if(spev.event & 16) {
    char *data = malloc(50);
    sparrow_socket_set_timeout(sp, spev.sock, now() + 5000);
    sparrow_recv(sp, spev.sock, data,50);
  }
  if(spev.event & 8) {
    printf("Recv timeout expired\n");
    return -1;
  }

  return 0;
}

