/* check.c -- independent check of the main theorem on small odd antiholes.
 *
 * The odd antihole on n = 2l - 1 vertices is the complement of the cycle 0, 1, ..., n - 1.
 * Its colour classes are single vertices and pairs of consecutive vertices of the cycle, so
 * it is colourable from lists L exactly when some matching M of the cycle admits distinct
 * colours: one from L(u) and L(v) for each pair uv in M and one from L(w) for each vertex w
 * outside M. The program decides this by running through the matchings of the cycle and
 * solving a bipartite matching problem for each.
 *
 * For l = 3 and l = 4 it runs through every assignment of lists of size l - 1, up to renaming
 * the colours (each list is a set of colours, and new colours enter in increasing order), and
 * checks that the antihole is colourable exactly when the lists are not all equal. For
 * l = 5, ..., 8 it checks the constant assignments and random ones, half of them close to a
 * constant assignment.
 *
 * Usage: check [maxcolours]
 * The bound applies to l = 4 (default 8). With 21 or more there is no bound: every assignment
 * of lists of size 3 on seven vertices is checked, which takes about fifteen minutes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int n, k;
static uint32_t L[16];

static int nmatch;                  /* matchings of the cycle */
static uint32_t match_edges[4096];  /* bit i: the edge {i, i+1 mod n} */
static int match_size[4096];

static void list_matchings(void) {
  nmatch = 0;
  for (int size = 0; 2 * size <= n; size++)
    for (uint32_t m = 0; m < (1u << n); m++) {
      if (__builtin_popcount(m) != size) continue;
      uint32_t rot = (m << 1 | m >> (n - 1)) & ((1u << n) - 1u);
      if (m & rot) continue;        /* two edges share a vertex */
      match_edges[nmatch] = m;
      match_size[nmatch] = size;
      nmatch++;
    }
}

static uint32_t cls[16];
static int ncls, owner[32];
static uint32_t seen;

static int augment(int j) {
  uint32_t m = cls[j] & ~seen;
  while (m) {
    int c = __builtin_ctz(m);
    m &= m - 1;
    seen |= 1u << c;
    if (owner[c] < 0 || augment(owner[c])) { owner[c] = j; return 1; }
  }
  return 0;
}

static int colourable(void) {
  uint32_t all = 0;
  for (int v = 0; v < n; v++) all |= L[v];
  int colours = __builtin_popcount(all);
  for (int t = 0; t < nmatch; t++) {
    uint32_t m = match_edges[t];
    if (n - match_size[t] > colours) continue;  /* more classes than colours */
    ncls = 0;
    uint32_t covered = 0;
    for (int i = 0; i < n; i++)
      if ((m >> i) & 1u) {
        int j = (i + 1) % n;
        cls[ncls++] = L[i] & L[j];
        covered |= (1u << i) | (1u << j);
      }
    for (int v = 0; v < n; v++)
      if (!((covered >> v) & 1u)) cls[ncls++] = L[v];
    for (int c = 0; c < 32; c++) owner[c] = -1;
    int ok = 1;
    for (int j = 0; j < ncls && ok; j++) { seen = 0; ok = augment(j); }
    if (ok) return 1;
  }
  return 0;
}

static int all_equal(void) {
  for (int v = 1; v < n; v++) if (L[v] != L[0]) return 0;
  return 1;
}

static long long leaves, failures, equal_cases;
static int maxpal;

static void report(void) {
  failures++;
  if (failures <= 5) {
    printf("  counterexample:");
    for (int u = 0; u < n; u++) printf(" %x", L[u]);
    printf("\n");
  }
}

/* Enumerate the lists of vertices v, ..., n - 1, with m colours used so far. */
static void enumerate(int v, int m) {
  if (v == n) {
    leaves++;
    int eq = all_equal();
    equal_cases += eq;
    if (colourable() == eq) report();
    return;
  }
  /* j new colours m, ..., m + j - 1 and a (k - j)-subset of the old colours 0, ..., m - 1 */
  for (int j = 0; j <= k; j++) {
    if (m + j > maxpal || k - j > m) continue;
    uint32_t fresh = ((1u << j) - 1u) << m;
    int r = k - j;
    if (r == 0) { L[v] = fresh; enumerate(v + 1, m + j); continue; }
    uint32_t s = (1u << r) - 1u, lim = 1u << m;
    while (s < lim) {
      L[v] = s | fresh;
      enumerate(v + 1, m + j);
      uint32_t c = s & -s, t = s + c;
      s = (((t ^ s) >> 2) / c) | t;  /* next subset with the same number of elements */
    }
  }
}

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next_rand(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng;
}

int main(int argc, char **argv) {
  int cap = argc > 1 ? atoi(argv[1]) : 8;
  int ok = 1;
  for (int l = 3; l <= 4; l++) {
    n = 2 * l - 1; k = l - 1;
    list_matchings();
    maxpal = l == 3 ? n * k : (cap < n * k ? cap : n * k);
    leaves = failures = equal_cases = 0;
    enumerate(0, 0);
    printf("l = %d: %lld assignments with at most %d colours, %lld constant, %lld failures\n",
           l, leaves, maxpal, equal_cases, failures);
    fflush(stdout);
    if (failures || equal_cases != 1) ok = 0;
  }
  for (int l = 5; l <= 8; l++) {
    n = 2 * l - 1; k = l - 1;
    list_matchings();
    /* the constant assignments: lists of size l - 1 fail and lists of size l succeed */
    for (int v = 0; v < n; v++) L[v] = (1u << k) - 1u;
    int c1 = colourable();
    for (int v = 0; v < n; v++) L[v] = (1u << l) - 1u;
    int c2 = colourable();
    long long trials = 100000;
    failures = 0;
    for (long long t = 0; t < trials; t++) {
      int pal = k + 1 + (int)(next_rand() % (uint64_t)(k + 2));
      if (t % 2 == 0) {
        /* close to the constant assignment {0, ..., k - 1}: replace one to three colours */
        do {
          for (int v = 0; v < n; v++) L[v] = (1u << k) - 1u;
          int swaps = 1 + (int)(next_rand() % 3);
          for (int s = 0; s < swaps; s++) {
            int v = (int)(next_rand() % (uint64_t)n);
            int out = (int)(next_rand() % (uint64_t)k), in = (int)(next_rand() % (uint64_t)pal);
            uint32_t m = L[v];
            int idx = 0, c = -1;
            for (int b = 0; b < 32; b++)
              if ((m >> b) & 1u) { if (idx == out) { c = b; break; } idx++; }
            if (!((m >> in) & 1u)) L[v] = (m & ~(1u << c)) | (1u << in);
          }
        } while (all_equal());
      } else {
        /* uniform lists of size k from pal colours */
        for (int v = 0; v < n; v++) {
          uint32_t m = 0;
          while (__builtin_popcount(m) < k) m |= 1u << (next_rand() % (uint64_t)pal);
          L[v] = m;
        }
      }
      if (colourable() == all_equal()) report();
    }
    printf("l = %d: constant lists of size %d %s, of size %d %s; %lld random assignments, "
           "%lld failures\n", l, k, c1 ? "colourable" : "not colourable", l,
           c2 ? "colourable" : "not colourable", trials, failures);
    fflush(stdout);
    if (failures || c1 || !c2) ok = 0;
  }
  printf(ok ? "C check passed\n" : "C check FAILED\n");
  return ok ? 0 : 1;
}
