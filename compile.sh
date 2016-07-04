#!/bin/bash
node convert.js

litprog -html index.html "c time.c" > time.c
litprog -html index.html "c sparrow.c.dna" > sparrow.c.dna
protein sparrow.c.dna > sparrow.c
litprog -html index.html "c sparrow.h" > sparrow.h
litprog -html index.html "c simple_test_server.c" > simple_test_server.c
litprog -html index.html "c simple_test_client.c" > simple_test_client.c
litprog -html index.html "c ot_test_server.c" > ot_test_server.c
litprog -html index.html "c ot_test_client.c" > ot_test_client.c
litprog -html index.html "c thr_client.c" > thr_client.c
litprog -html index.html "c thr_server.c" > thr_server.c
litprog -html index.html "c timeout_client.c" > timeout_client.c
litprog -html index.html "c timeout_server.c" > timeout_server.c

litprog -html index.html "c bsparrow.c.dna" > bsparrow.c.dna
protein bsparrow.c.dna > bsparrow.c
litprog -html index.html "c bsparrow.h" > bsparrow.h
litprog -html index.html "c bsimple_test_server.c" > bsimple_test_server.c
litprog -html index.html "c bsimple_test_client.c" > bsimple_test_client.c
litprog -html index.html "c bthr_server.c" > bthr_server.c
litprog -html index.html "c bthr_client.c" > bthr_client.c

litprog -html index.html "c msparrow.c.dna" > msparrow.c.dna
protein msparrow.c.dna > msparrow.c
litprog -html index.html "c msparrow.h" > msparrow.h
litprog -html index.html "c mthr_server.c" > mthr_server.c
litprog -html index.html "c mthr_client.c" > mthr_client.c

node convert_code.js sparrow.c sparrow.h ot_test_server.c ot_test_client.c simple_test_server.c simple_test_client.c thr_client.c thr_server.c timeout_client.c timeout_server.c time.c 
node convert_code.js bsparrow.c bsparrow.h bsimple_test_server.c bsimple_test_client.c bthr_server.c bthr_client.c
node convert_code.js msparrow.c msparrow.h mthr_server.c mthr_client.c

gcc -c -Wall time.c sparrow.c sparrow.h
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h simple_test_server.c -o simple_test_server
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h simple_test_client.c -o simple_test_client
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h ot_test_server.c -o ot_test_server
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h ot_test_client.c -o ot_test_client
gcc -Wall -O3 time.c sparrow.c sparrow.h thr_client.c -o thr_client
gcc -Wall -O3 time.c sparrow.c sparrow.h thr_server.c -o thr_server
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h timeout_client.c -o timeout_client
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c sparrow.h timeout_server.c -o timeout_server

gcc -c -Wall time.c sparrow.c bsparrow.c sparrow.h bsparrow.h
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c bsparrow.c sparrow.h bsparrow.h bsimple_test_server.c -o bsimple_test_server
gcc -g -Wall -DDEBUG_LOG time.c sparrow.c bsparrow.c sparrow.h bsparrow.h bsimple_test_client.c -o bsimple_test_client
gcc -Wall -O3 time.c sparrow.c bsparrow.c sparrow.h bsparrow.h bthr_client.c -o bthr_client
gcc -Wall -O3 time.c sparrow.c bsparrow.c sparrow.h bsparrow.h bthr_server.c -o bthr_server

gcc -c -Wall time.c sparrow.c bsparrow.c msparrow.c sparrow.h bsparrow.h msparrow.h
gcc -Wall -O3 time.c sparrow.c bsparrow.c msparrow.c sparrow.h bsparrow.h msparrow.h mthr_client.c -o mthr_client
gcc -Wall -O3 time.c sparrow.c bsparrow.c msparrow.c sparrow.h bsparrow.h msparrow.h mthr_server.c -o mthr_server

