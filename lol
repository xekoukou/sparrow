isparrow.c:10:3: error: expected specifier-qualifier-list before ‘RB_ENTRY’
   RB_ENTRY (isparrow_timeout_t) tm_field;
   ^
isparrow.c: In function ‘cmp_tm’:
isparrow.c:14:9: error: unknown type name ‘isparrow_timeout_t’
   const isparrow_timeout_t * tm1 = (const isparrow_timeout_t *) tm1_;
         ^
isparrow.c:14:43: error: unknown type name ‘isparrow_timeout_t’
   const isparrow_timeout_t * tm1 = (const isparrow_timeout_t *) tm1_;
                                           ^
isparrow.c:15:9: error: unknown type name ‘isparrow_timeout_t’
   const isparrow_timeout_t * tm2 = (const isparrow_timeout_t *) tm2_;
         ^
isparrow.c:15:43: error: unknown type name ‘isparrow_timeout_t’
   const isparrow_timeout_t * tm2 = (const isparrow_timeout_t *) tm2_;
                                           ^
isparrow.c:16:20: error: request for member ‘expiry’ in something not a structure or union
   int64_t xp = (tm1->expiry > tm2->expiry) - (tm1->expiry < tm2->expiry);
                    ^
isparrow.c:16:34: error: request for member ‘expiry’ in something not a structure or union
   int64_t xp = (tm1->expiry > tm2->expiry) - (tm1->expiry < tm2->expiry);
                                  ^
isparrow.c:16:50: error: request for member ‘expiry’ in something not a structure or union
   int64_t xp = (tm1->expiry > tm2->expiry) - (tm1->expiry < tm2->expiry);
                                                  ^
isparrow.c:16:64: error: request for member ‘expiry’ in something not a structure or union
   int64_t xp = (tm1->expiry > tm2->expiry) - (tm1->expiry < tm2->expiry);
                                                                ^
isparrow.c:20:18: error: request for member ‘fd’ in something not a structure or union
     int fd = (tm1->fd > tm2->fd) - (tm1->fd < tm2->fd);
                  ^
isparrow.c:20:28: error: request for member ‘fd’ in something not a structure or union
     int fd = (tm1->fd > tm2->fd) - (tm1->fd < tm2->fd);
                            ^
isparrow.c:20:40: error: request for member ‘fd’ in something not a structure or union
     int fd = (tm1->fd > tm2->fd) - (tm1->fd < tm2->fd);
                                        ^
isparrow.c:20:50: error: request for member ‘fd’ in something not a structure or union
     int fd = (tm1->fd > tm2->fd) - (tm1->fd < tm2->fd);
                                                  ^
isparrow.c:24:24: error: request for member ‘path_hash’ in something not a structure or union
       return memcmp(tm1->path_hash, tm2->path_hash, crypto_generichash_BYTES);
                        ^
isparrow.c:24:40: error: request for member ‘path_hash’ in something not a structure or union
       return memcmp(tm1->path_hash, tm2->path_hash, crypto_generichash_BYTES);
                                        ^
isparrow.c: At top level:
isparrow.c:29:1: warning: data definition has no type or storage class
 RB_HEAD (tm_rb_t, isparrow_timeout_t);
 ^
isparrow.c:29:1: warning: type defaults to ‘int’ in declaration of ‘RB_HEAD’ [-Wimplicit-int]
isparrow.c:29:1: warning: parameter names (without types) in function declaration
isparrow.c:30:1: warning: data definition has no type or storage class
 RB_GENERATE (tm_rb_t, isparrow_timeout_t, tm_field, cmp_tm);
 ^
isparrow.c:30:1: warning: type defaults to ‘int’ in declaration of ‘RB_GENERATE’ [-Wimplicit-int]
isparrow.c:30:1: warning: parameter names (without types) in function declaration
isparrow.c:33:18: error: field ‘timeout_tree’ has incomplete type
   struct tm_rb_t timeout_tree;
                  ^
isparrow.c: In function ‘cmp_tm’:
isparrow.c:27:1: warning: control reaches end of non-void function [-Wreturn-type]
 }
 ^
