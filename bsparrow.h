#ifndef _BSPARROW_H_
#define _BSPARROW_H_

#include<stdlib.h>

//TODO move these definitions into a different file.
#if (defined DEBUG_LOG) 
  #define Dprintf(x, ...) printf(x, ##__VA_ARGS__)
#else 
  #define Dprintf(x, ...)
#endif  

#define MIN_RETRY_INTERVAL 1000

typedef struct buffer_list_t buffer_list_t;

buffer_list_t * buffer_list_next(buffer_list_t * list, char ** data, size_t * length);

typedef struct bsparrow_socket_t bsparrow_socket_t;

struct bsparrow_event_t {
  int64_t id;
  int event;
  bsparrow_socket_t * bsock;
  char * first_buffer;
  size_t first_buffer_length;
  buffer_list_t * list;
  char * last_buffer;
  size_t last_buffer_length;
  size_t total_length;
};

typedef struct bsparrow_event_t bsparrow_event_t;

typedef struct bsparrow_t bsparrow_t;


bsparrow_t * bsparrow_new(size_t buffer_size, int64_t dtimeout, int max_output_queue, int max_output_sockets, int listening, char * port);

void bsparrow_destroy(bsparrow_t * bsp);

bsparrow_socket_t * bsparrow_socket_connect(bsparrow_t * bsp, int64_t id, char * address, char * port);

void bsparrow_socket_destroy(bsparrow_t * bsp, bsparrow_socket_t ** bsock);

void bsparrow_socket_assign_id(bsparrow_socket_t *bsock, int64_t id);

void bsparrow_socket_set_parent(bsparrow_socket_t * bsock, void * parent);

void * bsparrow_socket_get_parent(bsparrow_socket_t * bsock);

void bsparrow_set_timeout(bsparrow_t * bsp, int64_t timeout);

void bsparrow_wait(bsparrow_t * bsp, bsparrow_event_t * bspev, int only_output);

//The memory is owned by bsparrow. It will block if the queue becomes large. //TODO Is this the correct way to handle this?
void bsparrow_send(bsparrow_t * bsp, bsparrow_socket_t * bsock, char ** data, size_t len);

//Idris can give me a pointer , not a pointer of a pointer.
void bsparrow_send_idris(bsparrow_t * bsp, bsparrow_socket_t * bsock, char * data, size_t len);

//The len should never decrease.
void bsparrow_recv(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t len);

void bsparrow_got_some(bsparrow_t * bsp, bsparrow_socket_t * bsock, size_t that_much);

//Getters - Setters

int64_t bsparrow_event_get_id(bsparrow_event_t * bspev);

void bsparrow_event_set_id(bsparrow_event_t * bspev, int64_t id);

int bsparrow_event_get_event(bsparrow_event_t * bspev);

void bsparrow_event_set_event(bsparrow_event_t * bspev, int event);

bsparrow_socket_t * bsparrow_event_get_bsock(bsparrow_event_t * bspev);

void bsparrow_event_set_bsock(bsparrow_event_t * bspev, bsparrow_socket_t * bsock);


int64_t now(void);

void * scalloc(size_t num, size_t size);
//TODO check for errors.
void * srealloc(void * prev_pointer, size_t size);
#endif
