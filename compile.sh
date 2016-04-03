node convert.js
litprog -html index.html c > code.c
node convert_code.js
gcc -c -Wall code.c
