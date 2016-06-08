thr_client.c: In function ‘main’:
thr_client.c:33:14: warning: unused variable ‘data_out’ [-Wunused-variable]
       char * data_out = sparrow_socket_data_out(sock);
              ^
thr_server.c: In function ‘main’:
thr_server.c:32:16: warning: unused variable ‘data_in’ [-Wunused-variable]
         char * data_in = sparrow_socket_data_in(spev.sock);
                ^
timeout_client.c: In function ‘main’:
timeout_client.c:6:22: warning: unused variable ‘sock’ [-Wunused-variable]
   sparrow_socket_t * sock = sparrow_socket_connect(sp,"127.0.0.1", "9003");
                      ^
In file included from sparrow_buffer.c:7:0:
sparrow_buffer.c: In function ‘bsparrow_event_list_add’:
sparrow_buffer.c:225:15: error: ‘bsparrow_event_t’ has no member named ‘operational’
   assert(bspev->operational == 0);
               ^
sparrow_buffer.c: In function ‘bsparrow_socket_initialize_internal’:
sparrow_buffer.c:281:8: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
     bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
        ^
sparrow_buffer.c:281:55: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
     bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
                                                       ^
sparrow_buffer.c: In function ‘bsparrow_socket_process_next_out_req’:
sparrow_buffer.c:433:53: error: ‘bsparrow_t’ has no member named ‘ibspev’
       bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev, bspev);
                                                     ^
sparrow_buffer.c:436:10: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
       bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
          ^
sparrow_buffer.c:436:57: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
       bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
                                                         ^
sparrow_buffer.c: In function ‘bsparrow_retry’:
sparrow_buffer.c:448:35: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
   non_op_bsock_list_t * list = bsp->non_op_bsock_list;
                                   ^
sparrow_buffer.c:449:35: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
   non_op_bsock_list_t * iter = bsp->non_op_bsock_list;
                                   ^
sparrow_buffer.c:454:5: warning: implicit declaration of function ‘bsparrow_retry_single’ [-Wimplicit-function-declaration]
     bsparrow_retry_single(bsp, iter->bsock, bspev);
     ^
sparrow_buffer.c:455:8: error: ‘bsock’ undeclared (first use in this function)
     if(bsock->operational == 1) {
        ^
sparrow_buffer.c:455:8: note: each undeclared identifier is reported only once for each function it appears in
sparrow_buffer.c:456:10: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
       bsp->non_op_bsock_list = non_op_block_list_rem_next(list, prev_iter);
          ^
sparrow_buffer.c:456:7: warning: implicit declaration of function ‘non_op_block_list_rem_next’ [-Wimplicit-function-declaration]
       bsp->non_op_bsock_list = non_op_block_list_rem_next(list, prev_iter);
       ^
sparrow_buffer.c:458:30: error: ‘bsparrow_t’ has no member named ‘max_retries’
       if(bsock->retries > bsp->max_retries) {
                              ^
sparrow_buffer.c:459:12: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
         bsp->non_op_bsock_list = non_op_block_list_rem_next(list, prev_iter);
            ^
sparrow_buffer.c: At top level:
sparrow_buffer.c:469:1: warning: return type defaults to ‘int’ [-Wreturn-type]
 bsparrow_retry_single(bsparrow_t * bsp, bsparrow_socket_t * bsock, bsparrow_event_t * bspev) {
 ^
sparrow_buffer.c: In function ‘bsparrow_retry_single’:
sparrow_buffer.c:478:7: error: unknown type name ‘sparrow_event’
       sparrow_event spev = {0};
       ^
sparrow_buffer.c:479:31: warning: passing argument 1 of ‘sparrow_send’ from incompatible pointer type
       int more = sparrow_send(bsp, bsock->sock, bsock->buff_out.allocated_memory, bsock->buff_out.len, spev);  
                               ^
sparrow.h:34:5: note: expected ‘struct sparrow_t *’ but argument is of type ‘struct bsparrow_t *’
 int sparrow_send( sparrow_t * sp, sparrow_socket_t *sock, void * data, size_t len, sparrow_event_t * spev);
     ^
sparrow_buffer.c:479:104: warning: passing argument 5 of ‘sparrow_send’ makes pointer from integer without a cast
       int more = sparrow_send(bsp, bsock->sock, bsock->buff_out.allocated_memory, bsock->buff_out.len, spev);  
                                                                                                        ^
sparrow.h:34:5: note: expected ‘struct sparrow_event_t *’ but argument is of type ‘int’
 int sparrow_send( sparrow_t * sp, sparrow_socket_t *sock, void * data, size_t len, sparrow_event_t * spev);
     ^
sparrow_buffer.c:481:14: error: request for member ‘event’ in something not a structure or union
       if(spev.event == 8) {
              ^
sparrow_buffer.c:483:9: warning: ‘return’ with no value, in function returning non-void [-Wreturn-type]
         return;
         ^
sparrow_buffer.c:488:42: error: ‘buffer’ undeclared (first use in this function)
       sparrow_recv(bsp->sp, bsock->sock, buffer->new_data + buffer->cur_length, buffer->new_data_len - buffer->cur_length); 
                                          ^
sparrow_buffer.c: In function ‘bsparrow_wait_’:
sparrow_buffer.c:501:23: error: invalid operands to binary != (have ‘bsparrow_event_list_t’ and ‘void *’)
   if(bsp->ibspev_list != NULL) {
                       ^
sparrow_buffer.c:502:35: error: invalid type argument of ‘->’ (have ‘bsparrow_event_list_t’)
     memcpy(bspev, bsp->ibspev_list->bspev, sizeof(bsparrow_event_t));
                                   ^
sparrow_buffer.c:503:26: error: invalid type argument of ‘->’ (have ‘bsparrow_event_list_t’)
     free(bsp->ibspev_list->bspev);
                          ^
sparrow_buffer.c:504:74: error: ‘bsparrow_event_t’ has no member named ‘ibspev_list’
     bsp->ibspev_list = non_op_block_list_rem_next(bsp->ibspev_list, bspev->ibspev_list);
                                                                          ^
sparrow_buffer.c:518:9: warning: unused variable ‘ev’ [-Wunused-variable]
     int ev = spev.event;
         ^
sparrow_buffer.c:523:7: error: ‘ev’ undeclared (first use in this function)
   if((ev >> 1) & 1) {
       ^
sparrow_buffer.c:544:10: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
       bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
          ^
sparrow_buffer.c:544:57: error: ‘bsparrow_t’ has no member named ‘non_op_bsock_list’
       bsp->non_op_bsock_list = non_op_bsock_list_add(bsp->non_op_bsock_list, bsock);
                                                         ^
sparrow_buffer.c:558:12: error: ‘bsparrow_event_t’ has no member named ‘residue_length’
       bspev->residue_length = 0;
            ^
sparrow_buffer.c:559:12: error: ‘bsparrow_event_t’ has no member named ‘residue’
       bspev->residue = NULL;
            ^
sparrow_buffer.c:562:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer’
     bspev->second_buffer = buffer->new_data;
          ^
sparrow_buffer.c:565:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer_length’
     bspev->second_buffer_length = buffer->cur_length;
          ^
sparrow_buffer.c: In function ‘bsparrow_recv’:
sparrow_buffer.c:608:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer_length’
     bspev->second_buffer_length = 0;
          ^
sparrow_buffer.c:609:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer’
     bspev->second_buffer = NULL;
          ^
sparrow_buffer.c:610:51: error: ‘bsparrow_t’ has no member named ‘ibspev’
     bsp->ibspev_list = bsparrow_event_list_add(bsp->ibspev, bspev);
                                                   ^
sparrow_buffer.c: In function ‘bsparrow_retry_single’:
sparrow_buffer.c:493:1: warning: control reaches end of non-void function [-Wreturn-type]
 }
 ^
