#!/bin/bash
node convert.js

litprog -html index.html "c sparrow.c" > sparrow.c
litprog -html index.html "c sparrow.h" > sparrow.h
litprog -html index.html "c simple_test_server.c" > simple_test_server.c
litprog -html index.html "c simple_test_client.c" > simple_test_client.c
litprog -html index.html "c thr_client.c" > thr_client.c
litprog -html index.html "c thr_server.c" > thr_server.c
node convert_code.js sparrow.c sparrow.h simple_test_server.c simple_test_client.c thr_client.c thr_server.c
gcc -c -Wall sparrow.c sparrow.h
gcc -g -Wall -DDEBUG_LOG sparrow.c sparrow.h simple_test_server.c -o simple_test_server
gcc -g -Wall -DDEBUG_LOG sparrow.c sparrow.h simple_test_client.c -o simple_test_client
gcc -g -Wall -Wall -DDEBUG_LOG sparrow.c sparrow.h thr_client.c -o thr_client
gcc -g -Wall -Wall -DDEBUG_LOG sparrow.c sparrow.h thr_server.c -o thr_server
