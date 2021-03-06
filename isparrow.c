
#include"bsparrow.h"
#include"msparrow.h"
#include<sodium.h>
#include<assert.h>
#include"tree.h"

struct isparrow_timeout_t {
  int64_t expiry;
  int fd;
  unsigned char path_hash[crypto_generichash_BYTES];
  uint64_t counter;
  RB_ENTRY (isparrow_timeout_t) tm_field;
};

typedef struct isparrow_timeout_t isparrow_timeout_t;

int cmp_tm(const void * tm1_, const void * tm2_) {
  const isparrow_timeout_t * tm1 = (const isparrow_timeout_t *) tm1_;
  const isparrow_timeout_t * tm2 = (const isparrow_timeout_t *) tm2_;
  int64_t xp = (tm1->expiry > tm2->expiry) - (tm1->expiry < tm2->expiry);
  if(xp != 0) {
    return xp;
  } else {
    int fd = (tm1->fd > tm2->fd) - (tm1->fd < tm2->fd);
    if (fd != 0) {
      return fd;
    } else {
      return memcmp(tm1->path_hash, tm2->path_hash, crypto_generichash_BYTES);
    }
  }
}

RB_HEAD (tm_rb_t, isparrow_timeout_t);
RB_GENERATE (tm_rb_t, isparrow_timeout_t, tm_field, cmp_tm);

struct isparrow_t {
  struct tm_rb_t tm_rb;
};

typedef struct isparrow_t isparrow_t;
//4 bytes for the counter
//32 bytes for the path crypto_generichash


//TODO Should we return the path or just the hash?
isparrow_timeout_t * isparrow_add_path(isparrow_t * isp, int fd, unsigned char * prev_hash, uint64_t new_local_id) {
  isparrow_timeout_t * tm = scalloc(1, sizeof(isparrow_timeout_t));
  tm->fd = fd;
  tm->expiry = -1;
  tm->counter = 0;

  size_t all_together_length = crypto_generichash_BYTES + sizeof(int64_t);
  unsigned char all_together[all_together_length];
  if(prev_hash !=NULL) {
    memcpy(all_together, prev_hash, crypto_generichash_BYTES);
    memcpy(all_together + crypto_generichash_BYTES, (unsigned char *) &new_local_id, sizeof(new_local_id));
    crypto_generichash(tm->path_hash, crypto_generichash_BYTES, all_together, all_together_length, NULL, 0);
  } else {
    crypto_generichash(tm->path_hash, crypto_generichash_BYTES,(unsigned char *) &new_local_id, sizeof(uint64_t), NULL, 0);
  }

  void *rtsearch = RB_INSERT(tm_rb_t, &(isp->tm_rb), tm);
  assert(rtsearch == NULL);

  return tm;
}

int compare_hashes(const void *pointer1,const void *pointer2) {
  unsigned char * h1 = *((unsigned char **) pointer1);
  unsigned char * h2 = *((unsigned char **) pointer2);

  return memcmp(h1, h2, crypto_generichash_BYTES);
}


isparrow_timeout_t * isparrow_merge_paths(isparrow_t * isp,int fd, isparrow_timeout_t **tms, int length) {

  qsort(tms, length, sizeof(void *), &compare_hashes);

  isparrow_timeout_t * tm = scalloc(1, sizeof(isparrow_timeout_t));
  tm->fd = fd;
  tm->expiry = -1;
  tm->counter = 0;
  assert(tm->path_hash[0] == 0);

  size_t all_together_length = 2 * crypto_generichash_BYTES;
  unsigned char all_together[all_together_length];

  int i;
  for(i = 0; i < length; i++) {
    memcpy(all_together, tms[i], crypto_generichash_BYTES);
    memcpy(all_together + crypto_generichash_BYTES, tm->path_hash, crypto_generichash_BYTES);
    crypto_generichash(tm->path_hash, crypto_generichash_BYTES, all_together, all_together_length, NULL, 0);
  }

  void *rtsearch = RB_INSERT(tm_rb_t, &(isp->tm_rb), tm);
  assert(rtsearch == NULL);

  return tm;
}



void isparrow_prep_send(isparrow_t *isp, char * data, int64_t counter, unsigned char * prev_hash, uint64_t new_local_id) {
  size_t all_together_length = crypto_generichash_BYTES + sizeof(int64_t);
  unsigned char all_together[all_together_length];
  memcpy(all_together, prev_hash, crypto_generichash_BYTES);
  memcpy(all_together + crypto_generichash_BYTES, &new_local_id, sizeof(new_local_id));
  crypto_generichash((unsigned char *) data, crypto_generichash_BYTES, all_together, all_together_length, NULL, 0);

//  void *rtsearch = RB_INSERT(fd_rb_t, &(sp->fd_rb_socks), sock);
//  assert(rtsearch == NULL);
//  memcpy(data + crypto_generichash_BYTES, counter + 1
}


//It needs to either return a timeout event or return the hash of the path of the socket.
void isparrow_route_msg(isparrow_t * isp, int fd, sparrow_msg_t *msg) {
   
}



