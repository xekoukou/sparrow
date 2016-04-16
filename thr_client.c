#include "sparrow.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
  sparrow_t *sp = sparrow_new();
  sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9001");
  int i = 0;
  sparrow_event_t spev;
  spev.event = 0;
  int sent = 1;
  char *data = malloc(50);
  while(i < 2000000) {
    if((spev.event & 2) || (sent == 1)) {

      sprintf(data,"Hello there!");
      sent = sparrow_send(sp, sock, data, 50, &spev);
      if(spev.event & 8) {
        Dprintf("An error occured");    
        break;
      }
    }
    if(sent == 0) {
      sparrow_wait(sp,&spev);
    }

    if((spev.event & 2) || (sent == 1)) {
      char * data_out = sparrow_socket_data_out(sock);
      Dprintf("Sent :\n%s\n",data_out);
      i++;
    }
  }

  sparrow_close(&sp);
  exit(0);
}

