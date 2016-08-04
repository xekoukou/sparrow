#ifndef _MSPARROW_H_
#define _MSPARROW_H_

#include "bsparrow.h"
#include<string.h> 
#include<stdint.h> 

struct sparrow_msg_t {
  char * data;
  int64_t len;
};

typedef struct sparrow_msg_t sparrow_msg_t;

void msparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock);

int msparrow_get_msg(bsparrow_t * bsp, bsparrow_event_t * bspev, sparrow_msg_t * msg);

void msparrow_print_msg(sparrow_msg_t *msg);
char * sparrow_msg_get_data(sparrow_msg_t * msg);
int64_t sparrow_msg_get_length(sparrow_msg_t * msg);
#endif
