#include <stdio.h>
#include <time.h>
double kernel(double);
int main(void) {
  double s = 0, x = 0.9999999;
  struct timespec a, b;
  for (int i = 0; i < 20000; i++) s += kernel(x); /* warmup */
  clock_gettime(CLOCK_MONOTONIC, &a);
  for (int i = 0; i < 200000; i++) { s += kernel(x); x += 1e-12; }
  clock_gettime(CLOCK_MONOTONIC, &b);
  double ns = (b.tv_sec - a.tv_sec) * 1e9 + (b.tv_nsec - a.tv_nsec);
  printf("%8.1f ns/call  %.3f ns/step  (sum=%g)\n", ns / 200000, ns / 200000 / 12800, s);
  return 0;
}
