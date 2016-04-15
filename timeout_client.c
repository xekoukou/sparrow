#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");
  char *data = malloc(50);
  sprintf(data,"Hello there!");
  int error;
//Never send any data.
//  sparrow_send(sp, sock, data, 50, &error);
  sparrow_event_t spev;
  sparrow_wait(sp,&spev);
  printf("I sent : %s",data);
  sleep(4);

  return 0;
}

