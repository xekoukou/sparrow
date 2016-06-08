#include "sparrow.h"
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new(1000);
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");

  char *data = malloc(50);
  sprintf(data,"Hello there!");

  sparrow_event_t spev;
  sparrow_send(sp, sock, data, 50, &spev);

  sparrow_wait(sp,&spev);

  if(spev.event & 8) {
    printf("An error occured, in this case an output timeout expiry since the server crashed.\n");
  }
  
  sparrow_close(&sp);
  return 0;
}

