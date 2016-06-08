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
sparrow_buffer.c: In function ‘bsparrow_retry’:
sparrow_buffer.c:486:10: error: ‘bsock’ undeclared (first use in this function)
       if(bsock->retries > bsp->max_retries) {
          ^
sparrow_buffer.c:486:10: note: each undeclared identifier is reported only once for each function it appears in
sparrow_buffer.c: In function ‘bsparrow_wait_’:
sparrow_buffer.c:520:9: warning: unused variable ‘ev’ [-Wunused-variable]
     int ev = spev.event;
         ^
sparrow_buffer.c:525:7: error: ‘ev’ undeclared (first use in this function)
   if((ev >> 1) & 1) {
       ^
sparrow_buffer.c:560:12: error: ‘bsparrow_event_t’ has no member named ‘residue_length’
       bspev->residue_length = 0;
            ^
sparrow_buffer.c:561:12: error: ‘bsparrow_event_t’ has no member named ‘residue’
       bspev->residue = NULL;
            ^
sparrow_buffer.c:564:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer’
     bspev->second_buffer = buffer->new_data;
          ^
sparrow_buffer.c:567:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer_length’
     bspev->second_buffer_length = buffer->cur_length;
          ^
sparrow_buffer.c: In function ‘bsparrow_recv’:
sparrow_buffer.c:610:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer_length’
     bspev->second_buffer_length = 0;
          ^
sparrow_buffer.c:611:10: error: ‘bsparrow_event_t’ has no member named ‘second_buffer’
     bspev->second_buffer = NULL;
          ^
