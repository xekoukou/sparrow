#ifndef _SPARROW_H_
#define _SPARROW_H_

#include <unistd.h>
#include <stdlib.h>

#if (defined DEBUG_LOG) 
  #define Dprintf(x, ...) printf(x, ##__VA_ARGS__)
#else 
  #define Dprintf(x, ...)
#endif  

typedef struct sparrow_t sparrow_t;
typedef struct sparrow_socket_t sparrow_socket_t;

struct sparrow_event_t {
  sparrow_socket_t * sock;
  size_t cur;
  int event;
};

typedef struct sparrow_event_t sparrow_event_t;

sparrow_t * sparrow_new(void);

void sparrow_socket_bind(sparrow_t * sp, char * port);

sparrow_socket_t * sparrow_socket_connect(sparrow_t * sp, char * address, char * port); 

void sparrow_wait(sparrow_t * sp, sparrow_event_t * spev);

void sparrow_socket_set_timeout(sparrow_t * sp, sparrow_socket_t *sock, int64_t expiry);

int sparrow_send( sparrow_t * sp, sparrow_socket_t *sock, void * data, size_t len, sparrow_event_t * spev);

//It doesn't remove the timeout. If present, you need to cancel it mannually.
void sparrow_cancel_send( sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_recv( sparrow_t * sp, sparrow_socket_t *sock, void *data, size_t len);

void sparrow_cancel_recv( sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_socket_close(sparrow_t * sp, sparrow_socket_t * sock);

void sparrow_close(sparrow_t ** sp);

//?TODO Remove these, the serializer/multiplexer is supposed to keep a pointer to its buffer.
void * sparrow_socket_data_in(sparrow_socket_t *sock);
void * sparrow_socket_data_out(sparrow_socket_t *sock);
int64_t now(void);

#endif
