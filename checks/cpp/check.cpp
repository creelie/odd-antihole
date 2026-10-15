// check.cpp -- independent check of the main theorem on small odd antiholes, by a search
// different from the C check.
//
// A colouring of the odd antihole on n = 2l - 1 vertices (the complement of the cycle
// 0, 1, ..., n - 1) gives two vertices the same colour only if they are consecutive on the
// cycle, and gives no colour to three vertices. The program colours the vertices in the order
// 0, 1, ..., n - 1 by depth-first search, where a colour may be reused once, by the next
// vertex or by vertex n - 1 after vertex 0. As every colour class has at most two vertices, at
// least (n + 1) / 2 colours are needed; this bound cuts the search.
//
// For l = 3 every assignment of lists of size 2 is checked, and for l = 4 every assignment of
// lists of size 3 drawn from at most 7 colours, each up to renaming the colours. For l = 5 and
// l = 6 random assignments are checked. The statement checked is that the antihole is
// colourable from the lists exactly when the lists are not all equal.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <random>
#include <vector>

namespace {

int n = 0, k = 0;
std::array<std::uint32_t, 16> lists{};
std::array<int, 32> user{};   // -1: unused; v >= 0: used by v alone; -2: used by two vertices

bool search(int v, int fresh_left) {
  if (v == n) return true;
  // the vertices v, ..., n - 1 need at least (n - v - 1) / 2 colours besides any reused one
  if (2 * fresh_left + 2 < n - v) return false;
  for (std::uint32_t m = lists[v]; m != 0; m &= m - 1) {
    int c = std::countr_zero(m);
    int u = user[c];
    if (u == -1) {
      user[c] = v;
      bool ok = search(v + 1, fresh_left - 1);
      user[c] = -1;
      if (ok) return true;
    } else if (u >= 0 && (u == v - 1 || (u == 0 && v == n - 1))) {
      user[c] = -2;
      bool ok = search(v + 1, fresh_left);
      user[c] = u;
      if (ok) return true;
    }
  }
  return false;
}

bool colourable() {
  std::uint32_t all = 0;
  for (int v = 0; v < n; ++v) all |= lists[v];
  int colours = std::popcount(all);
  if (2 * colours < n + 1) return false;
  user.fill(-1);
  return search(0, colours);
}

bool all_equal() {
  for (int v = 1; v < n; ++v)
    if (lists[v] != lists[0]) return false;
  return true;
}

long long leaves = 0, failures = 0, constant = 0;
int max_colours = 0;

void check_leaf() {
  ++leaves;
  bool eq = all_equal();
  constant += eq;
  if (colourable() == eq) {
    if (++failures <= 5) {
      std::printf("  counterexample:");
      for (int v = 0; v < n; ++v) std::printf(" %x", lists[v]);
      std::printf("\n");
    }
  }
}

// the k-subsets of {0, ..., m - 1}
std::vector<std::vector<std::uint32_t>> subsets_by_size(int m) {
  std::vector<std::vector<std::uint32_t>> out(static_cast<std::size_t>(k) + 1);
  for (std::uint32_t s = 0; s < (1u << m); ++s) {
    int p = std::popcount(s);
    if (p <= k) out[static_cast<std::size_t>(p)].push_back(s);
  }
  return out;
}

std::vector<std::vector<std::vector<std::uint32_t>>> table;

void enumerate(int v, int used) {
  if (v == n) { check_leaf(); return; }
  for (int fresh = 0; fresh <= k; ++fresh) {
    int old = k - fresh;
    if (used + fresh > max_colours || old > used) continue;
    std::uint32_t added = ((1u << fresh) - 1u) << used;
    for (std::uint32_t s : table[static_cast<std::size_t>(used)][static_cast<std::size_t>(old)]) {
      lists[v] = s | added;
      enumerate(v + 1, used + fresh);
    }
  }
}

}  // namespace

int main() {
  bool ok = true;
  for (int l = 3; l <= 4; ++l) {
    n = 2 * l - 1;
    k = l - 1;
    max_colours = l == 3 ? n * k : 7;
    table.clear();
    for (int m = 0; m <= max_colours; ++m) table.push_back(subsets_by_size(m));
    leaves = failures = constant = 0;
    enumerate(0, 0);
    std::printf("l = %d: %lld assignments with at most %d colours, %lld constant, %lld failures\n",
                l, leaves, max_colours, constant, failures);
    std::fflush(stdout);
    if (failures != 0 || constant != 1) ok = false;
  }
  std::mt19937_64 rng(20261015);
  for (int l = 5; l <= 6; ++l) {
    n = 2 * l - 1;
    k = l - 1;
    for (int v = 0; v < n; ++v) lists[v] = (1u << k) - 1u;
    bool c1 = colourable();
    for (int v = 0; v < n; ++v) lists[v] = (1u << l) - 1u;
    bool c2 = colourable();
    failures = 0;
    const long long trials = 50000;
    for (long long t = 0; t < trials; ++t) {
      int pal = k + 1 + static_cast<int>(rng() % static_cast<unsigned>(k + 2));
      if (t % 2 == 0) {
        do {
          for (int v = 0; v < n; ++v) lists[v] = (1u << k) - 1u;
          int changes = 1 + static_cast<int>(rng() % 3u);
          for (int s = 0; s < changes; ++s) {
            int v = static_cast<int>(rng() % static_cast<unsigned>(n));
            int in = static_cast<int>(rng() % static_cast<unsigned>(pal));
            int out = static_cast<int>(rng() % static_cast<unsigned>(k));
            if ((lists[v] >> in) & 1u) continue;
            std::uint32_t m = lists[v];
            for (int i = 0; i < out; ++i) m &= m - 1;
            lists[v] = (lists[v] & ~(m & -m)) | (1u << in);
          }
        } while (all_equal());
      } else {
        for (int v = 0; v < n; ++v) {
          std::uint32_t m = 0;
          while (std::popcount(m) < k) m |= 1u << (rng() % static_cast<unsigned>(pal));
          lists[v] = m;
        }
      }
      if (colourable() == all_equal()) ++failures;
    }
    std::printf("l = %d: constant lists of size %d %s, of size %d %s; %lld random assignments, "
                "%lld failures\n", l, k, c1 ? "colourable" : "not colourable", l,
                c2 ? "colourable" : "not colourable", trials, failures);
    if (failures != 0 || c1 || !c2) ok = false;
  }
  std::printf(ok ? "C++ check passed\n" : "C++ check FAILED\n");
  return ok ? 0 : 1;
}
