#include <stddef.h>
#include <stdbool.h>

// compiled with armv8-a clang 11.0.1
// options: -O2
// https://godbolt.org/z/rzaGjecGK

typedef bool (*comp_fn)(size_t, size_t);

size_t binary_search(comp_fn comp, size_t *xs, size_t n, size_t x) {
  size_t l = 0, r = n;
  while(l < r) {
    size_t k = l + (r - l) / 2;
    if (comp(xs[k], x)) {
      l = k + 1;
    } else {
      r = k;
    }
  }
  return l;
}


bool compare_int(size_t x, size_t y) {
  return x <= y;
}
