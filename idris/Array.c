#include"Array.h"

CData array_alloc(int num, int size) {
  return cdata_allocate((size_t) num * size, free);
}

CData array_manage(void * data, int size) {
  return cdata_manage(data, size, free);
}

uint8_t array_peek8(int ofs, CData array)
{
    return ((uint8_t *) array->data)[ofs];
}

void array_poke8(int ofs, uint8_t byte, CData array)
{
    ((uint8_t *) array->data)[ofs] = byte;
}

uint16_t array_peek16(int ofs, CData array)
{
    return ((uint16_t *) array->data)[ofs];
}

void array_poke16(int ofs, uint16_t byte, CData array)
{
    ((uint16_t *) array->data)[ofs] = byte;
}

uint32_t array_peek32(int ofs, CData array)
{
    return ((uint32_t *) array->data)[ofs];
}

void array_poke32(int ofs, uint32_t byte, CData array)
{
    ((uint32_t *) array->data)[ofs] = byte;
}

uint64_t array_peek64(int ofs, CData array)
{
    return ((uint64_t *) array->data)[ofs];
}

void array_poke64(int ofs, uint64_t byte, CData array)
{
    ((uint64_t *) array->data)[ofs] = byte;
}

void array_realloc(int size, CData array)
{
    array->data = realloc(array->data, (size_t) size);
}


void do_nothing (void * data) {

}

void * return_memory(CData array)
{
    array->finalizer = do_nothing;
    return array->data;
}

int return_size(CData array)
{
    return (int) array->size;
}
