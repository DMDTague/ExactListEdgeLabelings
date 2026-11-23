# Sharpness checks for prescribed-edge two-factors

This folder supplies the finite computational checks for Section 6 of
*Prescribed Edges and Three-Part Two-Factors in Regular Bipartite Multigraphs*
(D. Tague, 2026).

## Reproduce

Run from this folder with Python 3 (standard library only):

```bash
python3 sharpness_checks_audited.py
```

The expected transcript is in `sharpness_checks_audited_output.txt`.

## Scope

- Proposition 6.1: checks the six-vertex multigraph family for degrees 3 through 7.
- Proposition 6.2: enumerates qualifying factors of the twelve-vertex simple cubic graph and checks the displayed conformal cycle.
- Computation 6.3: exhaustive small-order search for simple cubic bipartite graphs with 6, 8, or 10 vertices and three-edge matchings that extend to a spanning 2-factor but never occupy one component cycle.

The search fixes a perfect matching as the identity and enumerates ordered pairs of the other two disjoint perfect matchings. Counts of ordered factorizations and matching instances can include duplicate representations. The reported distinct edge sets are deduplicated while retaining a fixed identity matching.

These computations support the minimum-order observation in Section 6; the structural propositions have independent mathematical proofs. They do not establish a general theorem beyond the finite search range.
