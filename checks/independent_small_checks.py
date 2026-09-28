"""Independent small exact-count checks for the accompanying paper.

This script verifies:
- the chain-family examples R_(3,2) and R_(3,3);
- the cycle trace used in the chain count;
- Example 3.1 and the right-regularity warning example;
- the crown correspondence at n=3,4;
- randomized one-step uncrossing monotonicity on small multigraphs.

These checks are supplementary evidence only; no proof in the paper depends on
this script.
"""
import itertools
import random
from math import factorial


def count(edges, left_vertices, lists):
    """Count admissible exact-list edge labelings."""
    incident = {
        x: [i for i, (a, _) in enumerate(edges) if a == x]
        for x in left_vertices
    }
    right_labels = {}
    order = list(left_vertices)

    def rec(position):
        if position == len(order):
            return 1
        x = order[position]
        edge_ids = incident[x]
        total = 0
        for perm in itertools.permutations(lists[x]):
            ok = True
            used = []
            for edge_id, colour in zip(edge_ids, perm):
                y = edges[edge_id][1]
                seen = right_labels.setdefault(y, set())
                if colour in seen:
                    ok = False
                    break
                seen.add(colour)
                used.append((y, colour))
            if ok:
                total += rec(position + 1)
            for y, colour in used:
                right_labels[y].discard(colour)
        return total

    return rec(0)


def chain(k, t):
    edges = []
    for i in range(t):
        for a in range(k):
            for b in range(k):
                edges.append((("x", i, a), ("y", i, b)))
    for i in range(t - 1):
        edges.remove((("x", i, 1), ("y", i, 1)))
        edges.remove((("x", i + 1, 0), ("y", i + 1, 0)))
        edges += [
            (("x", i, 1), ("y", i + 1, 0)),
            (("x", i + 1, 0), ("y", i, 1)),
        ]
    left = [("x", i, a) for i in range(t) for a in range(k)]
    return edges, left


for t in (2, 3):
    k = 3
    edges, left = chain(k, t)
    A = {("x", 0, k - 1)}
    B = {("x", t - 1, k - 1)}
    core = list(range(k - 2))
    lists = {}
    for x in left:
        if x in A:
            lists[x] = core + ["b", "g"]
        elif x in B:
            lists[x] = core + ["a", "g"]
        else:
            lists[x] = core + ["a", "b"]
    ordinary = count(edges, left, {x: list(range(k)) for x in left})
    exact = count(edges, left, lists)
    print(
        f"R_(3,{t}): c3={ordinary} (paper {12 * 4 ** (t - 1)}), "
        f"N={exact} (paper {12 * 4 ** (t - 1) + 64 * 3 ** (t - 2)})"
    )


def cycle_count(word):
    m = len(word)
    edges = []
    for i in range(m):
        edges += [(i, i), (i, (i - 1) % m)]
    lists = {"A": ["b", "g"], "B": ["a", "g"], "C": ["a", "b"]}
    return count(edges, list(range(m)), {i: lists[w] for i, w in enumerate(word)})


for word in ["ACBC", "ACCBC", "ACBCC", "ACCBCC", "AB", "ABC", "ACAC", "AABB"]:
    print("cycle", word, "->", cycle_count(word))

print(
    "Ex 3.1:",
    count([(1, "p"), (1, "q"), (2, "p"), (2, "q")], [1, 2],
          {1: ["a", "b"], 2: ["c", "d"]}),
    count([(1, "p"), (1, "q"), (2, "p"), (2, "q")], [1, 2],
          {1: ["b", "u"], 2: ["d", "u"]}),
)
print(
    "path u x1 y x2 v:",
    count([(1, "u"), (1, "y"), (2, "y"), (2, "v")], [1, 2],
          {1: ["a", "b"], 2: ["a", "c"]}),
    count([(1, "u"), (1, "y"), (2, "y"), (2, "v")], [1, 2],
          {1: [1, 2], 2: [1, 2]}),
)

rho = {1: 1, 2: 1, 3: 1, 4: 4, 5: 56}
for n in (3, 4):
    edges = [(i, j) for i in range(n) for j in range(n) if i != j]
    left = list(range(n))
    ordinary = count(edges, left, {i: list(range(n - 1)) for i in left})
    residual = count(
        edges,
        left,
        {i: [symbol for symbol in range(n) if symbol != i] for i in left},
    )
    print(
        f"crown n={n}: c={ordinary} V_n=(n-1)!rho_n={factorial(n-1) * rho[n]}, "
        f"N={residual} rho_(n+1)={rho[n+1]}"
    )

random.seed(1)
violations = 0
trials = 0
for _ in range(400):
    nx = random.randint(2, 4)
    ny = random.randint(2, 4)
    left = list(range(nx))
    edges = [
        (x, random.randrange(ny))
        for x in left
        for _ in range(random.randint(1, 3))
    ]
    labels = list("abcdef")
    lists = {
        x: random.sample(labels, sum(1 for edge in edges if edge[0] == x))
        for x in left
    }
    supports = {c: {x for x in left if c in lists[x]} for c in labels}
    a, b = random.sample(labels, 2)
    union = supports[a] | supports[b]
    intersection = supports[a] & supports[b]
    uncrossed = {
        x: [c for c in lists[x] if c not in (a, b)]
        + (["U"] if x in union else [])
        + (["V"] if x in intersection else [])
        for x in left
    }
    before = count(edges, left, lists)
    after = count(edges, left, uncrossed)
    trials += 1
    violations += after > before

print("random uncrossing trials:", trials, "violations:", violations)
