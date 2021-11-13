#include <stdint.h>

int rbit(uint64_t x){
  int rev = 0;
  asm volatile("rbit %[rev], %[x]" : [rev] "=r" (rev) : [x] "r" (x));
  return rev;
}
