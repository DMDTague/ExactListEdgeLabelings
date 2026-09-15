# BachThesisLean

`BachThesisLean` is the Lean 4 verification companion to Dylan Tague's undergraduate mathematics thesis on exact list-edge labelings of finite bipartite multigraphs.

The repository is organized as a finished mathematical verification artifact. Its purpose is to make the formalized claims, their hypotheses, their proof dependencies, and the boundary of the machine-checked development explicit.

## Mathematical object

For a finite left-regular bipartite multigraph `R`, with parallel edges treated as distinct edge copies, the central exact-list theorem proves

\[
N(L,R) \ge c_k(R),
\]

when every left vertex receives an exact list of `k` labels. Here `N(L,R)` counts admissible exact-list edge labelings and `c_k(R)` counts ordinary proper edge-colorings from a fixed labelled `k`-palette.

The machine-checked theorem is `exactListLowerBound_machineChecked` in `BachThesisLean/Uncrossing/MainBound.lean`. The stronger nonregular canonical nested-minimizer theorem is `nested_minimizer` in `BachThesisLean/Uncrossing/NestedMinimizer.lean`.

The formalization also proves the exact one-step uncrossing surplus identity

\[
N(S,R)-N(S',R)
 = \sum_{\psi\in\Psi^*}2^{q(F_\psi)+r(F_\psi)},
\]

as `uncross_surplus_eq_sum_contributors_pow_q_add_r` in `BachThesisLean/Uncrossing/ManuscriptSurplus.lean`. The finite contributor set `Ψ*` is represented by `frozenPairContributors`.

## Verified scope

The rooted Lean library contains the formal proof chain for the exact-list lower bound, the canonical nested minimizer, the exact uncrossing surplus identity, the Latin/crown/residual specialization and growth bound, and the edge-copy-aware cubic structural theory developed for the thesis.

The cubic layer includes matching-coveredness, edge-root and vertex-root port masks, EEP characterizations, star-product composition and projection, explicit tight-cut contractions and reconstruction, brace and amplification reductions, square smoothing, small-shore and Heawood certificates, TF3 probe reductions, an internal Pfaffian witness/sign formalism, and Pfaffian descent through an oriented cubic tight cut to both explicit contractions.

The exact frozen scope is documented in [`docs/FORMALIZATION_SCOPE.md`](docs/FORMALIZATION_SCOPE.md). Statements outside the machine-checked scope, including open conjectures and external literature inputs, are recorded in [`KNOWN_GAPS.md`](KNOWN_GAPS.md).

## Latin specialization

The Latin modules formalize the normalization identities for the canonical class `U`, constant-diagonal class `V`, reduced count `rho`, and unrestricted count `L`; the crown identity `c_(n-1)(R_n) = V_n`; and the residual/canonical equivalence yielding `N_(n-1)(R_n) = U_(n+1)`.

Combined with the exact-list theorem, these results give the one-step growth inequality `L_(n+1) >= (n+1)! L_n` and the theorem `latin_superfactorial_lowerBound`.

## Cubic and Pfaffian boundary

The project distinguishes internal Lean theorems from literature results. The unconditional implication direction formalized internally is `TF3 -> EVP -> EEP`. The reverse brace implication `EVP -> TF3` used in the manuscript relies on Häggkvist and is not introduced as a Lean axiom. The prescribed-edge result attributed to Diwan and the nonplanar Pfaffian-brace result attributed to Gorsky--Johanni--Wiederrecht likewise remain external literature inputs unless separately formalized.

The Pfaffian tight-cut package in `BachThesisLean/Cubic/TightCutPfaffianSet.lean` proves descent from a Pfaffian witness on the original graph to witnesses on both explicit contractions. The converse implication from the stronger literature-level equivalence is outside the frozen verified scope.

## Open research boundary

The Latin floor, common-core equality criterion, universal `TF_k` / cubic rainbow-component conjecture, and per-edge enumerative Galvin problem remain research statements rather than Lean theorems. Finite regression checks are retained only as finite certificates and are not treated as universal proofs.

## Verification

The project is pinned to Lean 4.19.0 and Mathlib v4.19.0 by `lean-toolchain` and `lake-manifest.json`.

The verification layer consists of three complementary checks:

1. `python scripts/check_formalization.py` audits source hygiene, rejects proof placeholders and user axioms, checks proposition-target registration, and verifies that every local Lean module is rooted in the default import graph.
2. `lake build` elaborates and compiles the complete rooted `BachThesisLean` library.
3. `lake env lean Verification.lean` performs the transitive kernel-axiom audit over the public theorem/definition layer and enforces the repository's non-vacuity checks.

Only Lean's standard logical axioms admitted by the verification policy are permitted.

See [`docs/VERIFICATION.md`](docs/VERIFICATION.md) for the verification contract.

## Thesis correspondence

The final thesis-to-Lean correspondence is established claim by claim: each manuscript theorem or lemma is matched to its Lean declaration when formalized, while external results, finite evidence, terminology-only interpretations, and open conjectures are marked separately. This correspondence is the authority for the final manuscript revision.

The public mathematical report currently included with the repository is [`docs/capstone/EXACT_LIST_EDGE_LABELINGS_FINAL_REPORT.md`](docs/capstone/EXACT_LIST_EDGE_LABELINGS_FINAL_REPORT.md). The final thesis text should be read together with the frozen formalization boundary once manuscript reconciliation is complete.

## Reproducing verification

From the repository root:

```text
python scripts/check_formalization.py
lake build
lake env lean Verification.lean
```
