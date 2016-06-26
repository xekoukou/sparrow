#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(5000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  char *data = scalloc(1, 50);
  sprintf(data,"Hello there!");

  sparrow_event_t spev;
  sparrow_send(sp, sock, data, 50, &spev);

  sparrow_wait(sp,&spev, 0);
  printf("I sent : %s",data);
  
  sparrow_close(&sp);
  return 0;
}

