#ifndef _MSPARROW_H_
#define _MSPARROW_H_

#include "bsparrow.h"
#include<string.h> 
#include<stdint.h> 

struct msparrow_msg_t {
  char * data;
  uint64_t len;
};

typedef struct msparrow_msg_t msparrow_msg_t;

void msparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock);

int msparrow_get_msg(bsparrow_t * bsp, bsparrow_event_t * bspev, msparrow_msg_t * msg);
#endif
