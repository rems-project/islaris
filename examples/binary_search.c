#include <stddef.h>
#include <stdbool.h>

// compiled with armv8-a clang 11.0.1
// options: -O2
// https://godbolt.org/z/sEGvPoPox

typedef bool (*comp_fn)(void *, void *);

size_t binary_search(comp_fn comp, void **xs, size_t n, void *x) {
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

bool compare_int(void *x, void *y) {
  size_t *xi = x, *yi = y;
  return *xi <= *yi;
}
