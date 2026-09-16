# Exact list-edge labelings on bipartite multigraphs

This repository contains the Lean 4 formalization accompanying my undergraduate mathematics thesis on exact list-edge labelings of finite bipartite multigraphs.

The main result is an exact-list lower bound obtained by uncrossing. I also formalize the associated nested-minimizer and surplus identities, a Latin-square specialization, and the cubic structural theory developed around the remaining 2-factor problem.

## Exact-list theorem

Let `R` be a finite left-regular bipartite multigraph, with parallel edges treated as distinct edge copies. If every left vertex receives an exact list of `k` labels, I prove

\[
N(L,R) \ge c_k(R),
\]

where `N(L,R)` is the number of admissible exact-list edge labelings and `c_k(R)` is the number of ordinary proper edge-colorings from a fixed labelled `k`-palette.

The Lean theorem is

`exactListLowerBound_machineChecked`

in `BachThesisLean/Uncrossing/MainBound.lean`.

I also prove a stronger nonregular canonical nested-minimizer theorem,

`nested_minimizer`,

and the exact one-step uncrossing surplus identity

\[
N(S,R)-N(S',R)
 = \sum_{\psi\in\Psi^*} 2^{q(F_\psi)+r(F_\psi)}.
\]

The latter is formalized as `uncross_surplus_eq_sum_contributors_pow_q_add_r` in `BachThesisLean/Uncrossing/ManuscriptSurplus.lean`.

## Latin squares

The Latin-square part of the development formalizes the normalization identities for the canonical, constant-diagonal, reduced, and unrestricted counting classes; the crown identity; and the residual/canonical correspondence used in the thesis.

Combining these results with the exact-list theorem gives

\[
L_{n+1} \ge (n+1)!L_n,
\]

formalized in the theorem `latin_superfactorial_lowerBound`.

## Cubic bipartite graphs

A second part of the repository studies the cubic case behind the thesis's 2-factor frontier. I formalize matching-coveredness, edge-root and vertex-root masks, EEP characterizations, star-product composition and projection, tight-cut contractions and reconstruction, brace and amplification reductions, square smoothing, small-shore and Heawood certificates, TF3 probe reductions, and an internal Pfaffian witness/sign theory.

Within Lean, the unconditional implication direction is

`TF3 -> EVP -> EEP`.

I also prove Pfaffian descent through an oriented cubic tight cut to both explicit contractions in `BachThesisLean/Cubic/TightCutPfaffianSet.lean`.

Some results used in the mathematical discussion remain external literature inputs rather than Lean theorems. In particular, the reverse brace implication `EVP -> TF3` is taken from Häggkvist, while the prescribed-edge result attributed to Diwan and the nonplanar Pfaffian-brace result attributed to Gorsky--Johanni--Wiederrecht are not formalized here. The converse direction of the stronger literature-level Pfaffian tight-cut equivalence is also outside the formalized scope.

The exact theorem-by-theorem boundary is recorded in [`docs/FORMALIZATION_SCOPE.md`](docs/FORMALIZATION_SCOPE.md) and [`KNOWN_GAPS.md`](KNOWN_GAPS.md).

## Open problems

The formalization does not claim to settle every conjecture developed in the thesis. The Latin floor, the common-core equality criterion, the universal `TF_k` / cubic rainbow-component conjecture, and the per-edge enumerative Galvin problem remain open research directions. Finite computational certificates in the repository are treated only as finite evidence, not as universal proofs.

## Building the formalization

The project is pinned to Lean 4.19.0 and Mathlib v4.19.0. With `elan` installed, the complete formalization can be checked from the repository root with:

```bash
lake exe cache get
python scripts/check_formalization.py
lake build
lake env lean Verification.lean
```

The Python audit checks source hygiene, proof placeholders, proposition-target registration, and import coverage. `Verification.lean` performs a transitive kernel-axiom audit of the public theorem and definition layer. The verification policy permits only Lean's standard logical axioms used by the development.

More detail on the checking contract is in [`docs/VERIFICATION.md`](docs/VERIFICATION.md).

## Thesis and mathematical report

The public mathematical report included with the repository is [`docs/capstone/EXACT_LIST_EDGE_LABELINGS_FINAL_REPORT.md`](docs/capstone/EXACT_LIST_EDGE_LABELINGS_FINAL_REPORT.md).

I use the Lean development as the authority for the formalized claims when reconciling the final thesis text: statements proved in Lean are matched to their declarations, while literature inputs, finite evidence, interpretive terminology, and open conjectures are kept separate.
