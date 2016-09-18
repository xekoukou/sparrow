#ifndef _ARRAY_H_
#define _ARRAY_H_

#include<stdlib.h>
#include<stdbool.h>
#include<stddef.h>
#include<stdint.h>
#include"idris_rts.h"

CData array_alloc(int num, int size);

CData array_manage(void * data, int size);

void array_realloc(int size, CData array);

uint8_t array_peek8(int ofs, CData array);

void array_poke8(int ofs, uint8_t byte, CData array);

uint16_t array_peek16(int ofs, CData array);

void array_poke16(int ofs, uint16_t byte, CData array);

uint32_t array_peek32(int ofs, CData array);

void array_poke32(int ofs, uint32_t byte, CData array);

uint64_t array_peek64(int ofs, CData array);

void array_poke64(int ofs, uint64_t byte, CData array);

void* return_memory(CData array);

//Should turn it into Bits64
int return_size(CData array);

#endif
