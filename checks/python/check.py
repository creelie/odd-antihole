"""Independent check of the main theorem on small odd antiholes, by generic list colouring.

The odd antihole on n = 2l - 1 vertices is built as a graph: u and v are adjacent when they are
distinct and not consecutive on the cycle 0, 1, ..., n - 1. A list colouring is searched for by
colouring the vertices one at a time and checking every edge, with no use of the structure of
the colour classes.

Checked: the chromatic number of the odd antihole is l for l = 3, 4, 5; for l = 3 every
assignment of lists of size 2, and for l = 4 every assignment of lists of size 3 from at most 5
colours, up to renaming the colours, is colourable exactly when the lists are not all equal.
"""
from itertools import combinations, product
import sys


def antihole(n):
    return [[u != v and (u - v) % n not in (1, n - 1) for v in range(n)] for u in range(n)]


def colourable(adj, lists):
    n = len(lists)
    colour = [None] * n

    def go(v):
        if v == n:
            return True
        for c in lists[v]:
            if all(not adj[v][u] or colour[u] != c for u in range(v)):
                colour[v] = c
                if go(v + 1):
                    return True
        colour[v] = None
        return False

    return go(0)


def k_colourable(adj, k):
    n = len(adj)
    return any(all(not adj[u][v] or f[u] != f[v] for u in range(n) for v in range(u))
               for f in product(range(k), repeat=n) if f[0] == 0)


def assignments(n, k, max_colours):
    """Lists of size k for vertices 0, ..., n - 1, up to renaming: new colours enter in order."""
    def rec(v, used, acc):
        if v == n:
            yield acc
            return
        for fresh in range(k + 1):
            old = k - fresh
            if used + fresh > max_colours or old > used:
                continue
            new = frozenset(range(used, used + fresh))
            for s in combinations(range(used), old):
                yield from rec(v + 1, used + fresh, acc + [new | frozenset(s)])
    yield from rec(0, 0, [])


def main():
    ok = True
    for l in (3, 4, 5):
        n = 2 * l - 1
        adj = antihole(n)
        chi_ok = k_colourable(adj, l) and not k_colourable(adj, l - 1)
        print(f"l = {l}: chromatic number of the odd antihole on {n} vertices is "
              f"{l if chi_ok else 'not ' + str(l)}")
        ok &= chi_ok
    for l, max_colours in ((3, 10), (4, 5)):
        n, k = 2 * l - 1, l - 1
        adj = antihole(n)
        count = failures = constant = 0
        for lists in assignments(n, k, max_colours):
            count += 1
            eq = all(x == lists[0] for x in lists)
            constant += eq
            if colourable(adj, [sorted(x) for x in lists]) == eq:
                failures += 1
                if failures <= 5:
                    print("  counterexample:", [sorted(x) for x in lists])
        print(f"l = {l}: {count} assignments with at most {max_colours} colours, "
              f"{constant} constant, {failures} failures")
        ok &= failures == 0 and constant == 1
    print("Python check passed" if ok else "Python check FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
