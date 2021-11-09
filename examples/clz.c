#include <stdint.h>

int clz(uint64_t x){
  int count = 0;
  asm volatile("clz %[count], %[x]" : [count] "=r" (count) : [x] "r" (x));
  return count;
}
