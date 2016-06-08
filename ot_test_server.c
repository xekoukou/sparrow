#include "sparrow.h"
#include <stdio.h>
#include <unistd.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_bind(sp,"9003");

  sparrow_event_t spev;
  sparrow_wait(sp,&spev);

  if(spev.event & 16) {
    printf("we connected and now we will wait for a period so that the client output timeout expires.\n");
    sleep(4);
  }

  sparrow_wait(sp,&spev);
  return 0;
}

