#include "sparrow.h"
//#include "sparrow_buff.h"
//#include "sparrow_multiplexer.h"
#include "tree.h"


struct buffer_t {
  void * data;
  int64_t len;
  struct buffer_t * next;
};

typedef struct buffer_t buffer_t;


struct input_timebuffer_t {
  int64_t expiry;
  int64_t cur[2]; 
  buffer_t * buffer;
  RB_ENTRY (input_timebuffer_t) field;
};

typedef struct input_timebuffer_t input_timebuffer_t;

struct output_timebuffer_t {
  int64_t expiry;
  buffer_t  * buffer;
  RB_ENTRY (output_timebuffer_t) field;
};

typedef struct output_timebuffer_t output_timebuffer_t;

int cmp_ot_timebuf(const void * ti1, const void * ti2) {
  const output_timebuffer_t * t1 = (const output_timebuffer_t *) ti1;
  const output_timebuffer_t * t2 = (const output_timebuffer_t *) ti2;
  return (t1->expiry > t2->expiry) - (t1->expiry < t2->expiry);
}

int cmp_it_timebuf(const void * ti1, const void * ti2) {
  const input_timebuffer_t * t1 = (const input_timebuffer_t *) ti1;
  const input_timebuffer_t * t2 = (const input_timebuffer_t *) ti2;
  return (t1->expiry > t2->expiry) - (t1->expiry < t2->expiry);
}

RB_HEAD (it_rb_t, input_timebuffer_t);
RB_HEAD (ot_rb_t, output_timebuffer_t);

RB_GENERATE (it_rb_t, input_timebuffer_t, field, cmp_it_timebuf);
RB_GENERATE (ot_rb_t, output_timebuffer_t, field, cmp_ot_timebuf);


struct sparrow_buff_socket_t {
  
  int fd;
  struct it_rb_t it_rb; // A tree container of input_timebuffers.  
  struct ot_rb_t ot_rb; // A tree container of input_timebuffers.
  void * in_buffer[2];
  void * out_buffer[2];
//  input buffers
//  freeable variable input buffers.
//  output timeouts plus dynamic array of buffers
//  freeable variable output buffers.
  size_t buff_size;
};


