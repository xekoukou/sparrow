#!/bin/bash
node convert.js

litprog -html index.html "c time.c" > time.c
litprog -html index.html "c sparrow.c.dna" > sparrow.c.dna
protein sparrow.c.dna > sparrow.c
litprog -html index.html "c sparrow.h" > sparrow.h
litprog -html index.html "c simple_test_server.c" > simple_test_server.c
litprog -html index.html "c simple_test_client.c" > simple_test_client.c
litprog -html index.html "c thr_client.c" > thr_client.c
litprog -html index.html "c thr_server.c" > thr_server.c
litprog -html index.html "c timeout_client.c" > timeout_client.c
litprog -html index.html "c timeout_server.c" > timeout_server.c
node convert_code.js sparrow.c sparrow.h simple_test_server.c simple_test_client.c thr_client.c thr_server.c timeout_client.c timeout_server.c time.c
gcc -c -Wall time.c sparrow.c sparrow.h
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h simple_test_server.c -o simple_test_server
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h simple_test_client.c -o simple_test_client
gcc -Wall -O3 time.c sparrow.c sparrow.h thr_client.c -o thr_client
gcc -Wall -O3 time.c sparrow.c sparrow.h thr_server.c -o thr_server
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h timeout_client.c -o timeout_client
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h timeout_server.c -o timeout_server
