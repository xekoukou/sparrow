==5745== Memcheck, a memory error detector
==5745== Copyright (C) 2002-2013, and GNU GPL'd, by Julian Seward et al.
==5745== Using Valgrind-3.10.0 and LibVEX; rerun with -h for copyright info
==5745== Command: ./bthr_client
==5745== 
==5745== Invalid read of size 4
==5745==    at 0x404FB4: bsparrow_socket_internal_destroy (bsparrow.c:371)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e03f8 is 8 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 8
==5745==    at 0x404FBF: bsparrow_socket_internal_destroy (bsparrow.c:372)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0400 is 16 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid free() / delete / delete[] / realloc()
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x404FCA: bsparrow_socket_internal_destroy (bsparrow.c:372)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0500 is 0 bytes inside a block of size 10 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x404FCA: bsparrow_socket_internal_destroy (bsparrow.c:372)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 8
==5745==    at 0x404FCF: bsparrow_socket_internal_destroy (bsparrow.c:373)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0408 is 24 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid free() / delete / delete[] / realloc()
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x404FDA: bsparrow_socket_internal_destroy (bsparrow.c:373)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0550 is 0 bytes inside a block of size 5 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x404FDA: bsparrow_socket_internal_destroy (bsparrow.c:373)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 4
==5745==    at 0x404FDF: bsparrow_socket_internal_destroy (bsparrow.c:375)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e04a8 is 184 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 8
==5745==    at 0x405007: bsparrow_socket_internal_destroy (bsparrow.c:378)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0470 is 128 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid free() / delete / delete[] / realloc()
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405015: bsparrow_socket_internal_destroy (bsparrow.c:378)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e05a0 is 0 bytes inside a block of size 100 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405015: bsparrow_socket_internal_destroy (bsparrow.c:378)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 8
==5745==    at 0x40501A: bsparrow_socket_internal_destroy (bsparrow.c:379)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0488 is 152 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid free() / delete / delete[] / realloc()
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405028: bsparrow_socket_internal_destroy (bsparrow.c:379)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0650 is 0 bytes inside a block of size 100 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405028: bsparrow_socket_internal_destroy (bsparrow.c:379)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 8
==5745==    at 0x404B49: bsparrow_socket_clean (bsparrow.c:270)
==5745==    by 0x40503B: bsparrow_socket_internal_destroy (bsparrow.c:381)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0418 is 40 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 4
==5745==    at 0x404B97: bsparrow_socket_clean (bsparrow.c:282)
==5745==    by 0x40503B: bsparrow_socket_internal_destroy (bsparrow.c:381)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0438 is 72 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 4
==5745==    at 0x404BB3: bsparrow_socket_clean (bsparrow.c:285)
==5745==    by 0x40503B: bsparrow_socket_internal_destroy (bsparrow.c:381)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0448 is 88 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 4
==5745==    at 0x4048EE: oqueue_oldest_req (bsparrow.c:143)
==5745==    by 0x404C0A: bsparrow_socket_clean (bsparrow.c:291)
==5745==    by 0x40503B: bsparrow_socket_internal_destroy (bsparrow.c:381)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e04a4 is 180 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 4
==5745==    at 0x404511: oqueue_destroy (bsparrow.c:75)
==5745==    by 0x40504D: bsparrow_socket_internal_destroy (bsparrow.c:382)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e04a4 is 180 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid read of size 8
==5745==    at 0x404535: oqueue_destroy (bsparrow.c:76)
==5745==    by 0x40504D: bsparrow_socket_internal_destroy (bsparrow.c:382)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0490 is 160 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid write of size 8
==5745==    at 0x404544: oqueue_destroy (bsparrow.c:77)
==5745==    by 0x40504D: bsparrow_socket_internal_destroy (bsparrow.c:382)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e0490 is 160 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== Invalid free() / delete / delete[] / realloc()
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x4052C4: bsparrow_destroy (bsparrow.c:445)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745==  Address 0x51e03f0 is 0 bytes inside a block of size 208 free'd
==5745==    at 0x4C29E90: free (vg_replace_malloc.c:473)
==5745==    by 0x405059: bsparrow_socket_internal_destroy (bsparrow.c:384)
==5745==    by 0x40525F: bsparrow_destroy (bsparrow.c:433)
==5745==    by 0x40641F: main (bthr_client.c:24)
==5745== 
==5745== 
==5745== HEAP SUMMARY:
==5745==     in use at exit: 0 bytes in 0 blocks
==5745==   total heap usage: 800,013 allocs, 800,018 frees, 40,003,031 bytes allocated
==5745== 
==5745== All heap blocks were freed -- no leaks are possible
==5745== 
==5745== For counts of detected and suppressed errors, rerun with: -v
==5745== ERROR SUMMARY: 18 errors from 18 contexts (suppressed: 0 from 0)
