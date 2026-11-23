#!/usr/bin/env python3
"""Reproducibility script for Section 6 of
"Prescribed Edges and Three-Part Two-Factors in Regular Bipartite Multigraphs" (D. Tague).

Checks:
  1. Proposition 6.1: for k = 3..7, the multigraph G_k with multiplicity matrix A_k has
     2-factors containing T, and none with T on one cycle.
  2. Proposition 6.2: the 12-vertex simple cubic graph has exactly four perfect matchings
     avoiding T; every complementary 2-factor splits T; the stated 10-cycle is conformal.
  3. Computation 6.3: no simple cubic bipartite graph on 6, 8 or 10 vertices has a 3-edge
     matching that lies in some 2-factor but on no common cycle of any 2-factor.

Method for 3: every simple cubic bipartite graph on 2n vertices is, after relabelling Y,
the union of the identity matching and two further perfect matchings p2, p3 that are
pairwise disjoint from it and from each other. Enumerating all such (p2, p3) therefore
covers every simple cubic bipartite graph up to relabelling Y, so the search is exhaustive.
The ordered (p2, p3) pairs count representations, not distinct graphs;
we also report the number of unique labeled edge sets with an identity matching.

Pure Python 3, no dependencies. Runtime: under a minute.
"""
import itertools


def perfect_matchings(n, edges, avail):
    """All perfect matchings (as frozensets of edge indices) using only edges in avail.
    Left vertices 0..n-1, right vertices 0..n-1; edges[i] = (left, right)."""
    by_left = [[] for _ in range(n)]
    for i in avail:
        by_left[edges[i][0]].append(i)
    out = []

    def rec(l, used, cur):
        if l == n:
            out.append(frozenset(cur))
            return
        for i in by_left[l]:
            r = edges[i][1]
            if not (used >> r) & 1:
                cur.append(i)
                rec(l + 1, used | (1 << r), cur)
                cur.pop()

    rec(0, 0, [])
    return out


def two_factors(n, edges):
    """All spanning 2-factors: each is the union of two disjoint perfect matchings."""
    all_ids = set(range(len(edges)))
    seen = set()
    for m1 in perfect_matchings(n, edges, all_ids):
        for m2 in perfect_matchings(n, edges, all_ids - m1):
            f = m1 | m2
            if f not in seen:
                seen.add(f)
                yield f


def component_of(n, edges, f):
    """Map each edge index in f to a label of its component (vertices: L=0..n-1, R=n..2n-1)."""
    parent = list(range(2 * n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in f:
        l, r = edges[i]
        parent[find(l)] = find(n + r)
    return {i: find(edges[i][0]) for i in f}


def connected(n, edges):
    parent = list(range(2 * n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for l, r in edges:
        parent[find(l)] = find(n + r)
    return len({find(x) for x in range(2 * n)}) == 1


def status(n, edges, t):
    """Return (number of 2-factors containing t, number with t on one cycle)."""
    ext = same = 0
    for f in two_factors(n, edges):
        if all(i in f for i in t):
            ext += 1
            c = component_of(n, edges, f)
            if len({c[i] for i in t}) == 1:
                same += 1
    return ext, same


def check_prop_61():
    print("Proposition 6.1 (A_k family)")
    for k in range(3, 8):
        a = [[0, 1, k - 1], [1, k - 2, 1], [k - 1, 1, 0]]
        edges, first = [], {}
        for x in range(3):
            for y in range(3):
                for c in range(a[x][y]):
                    if c == 0:
                        first[(x, y)] = len(edges)
                    edges.append((x, y))
        t = [first[(0, 2)], first[(1, 1)], first[(2, 0)]]
        ext, same = status(3, edges, t)
        ok = connected(3, edges) and ext > 0 and same == 0
        print(f"  k={k}: 2-factors containing T = {ext}, with T on one cycle = {same}  [{'OK' if ok else 'FAIL'}]")
        assert ok


def check_prop_62():
    print("Proposition 6.2 (12-vertex simple cubic graph)")
    nbr = {0: [0, 2, 3], 1: [0, 1, 5], 2: [1, 2, 4], 3: [1, 2, 3], 4: [3, 4, 5], 5: [0, 4, 5]}
    edges = [(x, y) for x in nbr for y in nbr[x]]
    assert len(set(edges)) == 18 and all(sum(1 for e in edges if e[1] == y) == 3 for y in range(6))
    t = [edges.index(e) for e in [(0, 3), (2, 1), (5, 5)]]
    avoid = perfect_matchings(6, edges, set(range(18)) - set(t))
    print(f"  perfect matchings avoiding T: {len(avoid)}")
    assert len(avoid) == 4
    ext, same = status(6, edges, t)
    print(f"  2-factors containing T = {ext}, with T on one cycle = {same}")
    assert ext == 4 and same == 0
    cyc = [("x", 0), ("y", 0), ("x", 1), ("y", 1), ("x", 2), ("y", 4), ("x", 5), ("y", 5), ("x", 4), ("y", 3)]
    pairs = list(zip(cyc, cyc[1:] + cyc[:1]))
    on_cycle = all(((a[1], b[1]) if a[0] == "x" else (b[1], a[1])) in edges for a, b in pairs)
    t_on = all(any({a, b} == {("x", e[0]), ("y", e[1])} for a, b in pairs) for e in [(0, 3), (2, 1), (5, 5)])
    conformal = (3, 2) in edges  # remaining vertices x3, y2 are adjacent
    print(f"  10-cycle valid: {on_cycle}, contains T: {t_on}, conformal: {conformal}")
    assert on_cycle and t_on and conformal


def check_comp_63():
    print("Computation 6.3 (exhaustive search, simple cubic bipartite, 6, 8 and 10 vertices)")
    for n in (3, 4, 5):
        representations = instances = bad = 0
        distinct_graphs = set()
        for p2 in itertools.permutations(range(n)):
            if any(p2[i] == i for i in range(n)):
                continue
            for p3 in itertools.permutations(range(n)):
                if any(p3[i] == i or p3[i] == p2[i] for i in range(n)):
                    continue
                edges = [(i, i) for i in range(n)] + [(i, p2[i]) for i in range(n)] + [(i, p3[i]) for i in range(n)]
                if not connected(n, edges):
                    continue
                representations += 1
                distinct_graphs.add(frozenset(edges))
                factors = [(f, component_of(n, edges, f)) for f in two_factors(n, edges)]
                for t in itertools.combinations(range(3 * n), 3):
                    if len({edges[i][0] for i in t}) < 3 or len({edges[i][1] for i in t}) < 3:
                        continue
                    instances += 1
                    ext = [c for f, c in factors if all(i in f for i in t)]
                    if ext and all(len({c[i] for i in t}) > 1 for c in ext):
                        bad += 1
        print(f"  {2*n} vertices: ordered factorizations {representations}, "
              f"distinct edge sets with fixed identity matching {len(distinct_graphs)}, "
              f"3-edge matching instances {instances}, examples found {bad}")
        assert bad == 0


if __name__ == "__main__":
    check_prop_61()
    check_prop_62()
    check_comp_63()
    print("All checks passed.")