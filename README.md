# ExactListEdgeLabelings

Formalization and reproducibility materials for

> **Dylan Tague, _Exact list-edge labelings of bipartite multigraphs: uncrossing, nested minimizers, and a 2-factor criterion for equality_.**

This repository contains the Lean 4 development accompanying the paper, together with source-level verification scripts and documentation of the exact boundary between machine-checked results, external literature inputs, finite computational evidence, and open conjectures.

## Main mathematical results represented in Lean

For a finite left-`k`-regular bipartite multigraph `R` with parallel edges treated as distinct edge copies, an exact left-list assignment gives every edge at a left vertex the same `k`-element list and requires every list entry to be used exactly once there.

The formalized exact-list lower bound is

```text
exactListLowerBound_machineChecked
```

in `BachThesisLean/Uncrossing/MainBound.lean`. It proves the exact-list analogue

$$
N(L,R) \ge c_k(R),
$$

where `N(L,R)` is the number of admissible exact-list edge labelings and `c_k(R)` is the number of ordinary proper `k`-edge-colourings from a fixed labelled palette.

The repository also contains Lean proofs of:

- the stronger nonregular canonical nested-minimizer theorem `nested_minimizer`;
- the exact one-step uncrossing surplus identity
  $$
  N(S,R)-N(S',R)
  = \sum_{\psi\in\Psi^*}2^{q(F_\psi)+r(F_\psi)};
  $$
- the crown/Latin correspondence and the growth inequality
  $$
  L_{n+1}\ge (n+1)!L_n;
  $$
- a substantial cubic bipartite matching and reduction library, including rooted EEP/EVP/TF3 infrastructure, star products, tight-cut contractions, square smoothing, finite Heawood checks, and Pfaffian witness transport.

The exact formalization boundary is documented in `docs/FORMALIZATION_SCOPE.md` and `KNOWN_GAPS.md`. In particular, external literature inputs and open conjectures are not silently promoted to Lean theorems.

## Repository layout

- `BachThesisLean/` — Lean library.
- `BachThesisLean.lean` — root import for the complete formalized library.
- `Verification.lean` — transitive kernel-axiom audit of the public theorem/definition layer.
- `scripts/check_formalization.py` — source-hygiene, proposition-target, and import-coverage audit.
- `checks/independent_small_checks.py` — representative exact-count and uncrossing sanity checks; none is used in a proof.
- `outputs/independent_small_checks.txt` — recorded output of those supplementary checks.
- `docs/FORMALIZATION_SCOPE.md` — theorem-by-theorem scope of the formalization.
- `docs/VERIFICATION.md` — verification contract and trust boundary.
- `KNOWN_GAPS.md` — explicit boundaries, external inputs, helper proposition targets, and open conjectures.
- `.github/workflows/lean.yml` — complete staged CI build and kernel audit.

The historical Lean namespace `BachThesisLean` is retained for source stability; the publication repository and manuscript are identified as **ExactListEdgeLabelings**.

## Toolchain

The project is pinned to Lean 4.19.0 and Mathlib v4.19.0.

With `elan` installed:

```bash
lake exe cache get
python3 scripts/check_formalization.py
lake build
lake env lean Verification.lean
```

The source audit rejects proof placeholders and trust-bypass tokens, checks registered proposition targets against `KNOWN_GAPS.md`, and verifies that every local library module is reachable from the root import. `Verification.lean` then audits the transitive axioms of the public source-visible declaration layer. The permitted logical axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

For convenience:

```bash
make verify
```

runs the source audit, the complete Lean build, and the kernel audit.

For the supplementary finite sanity checks:

```bash
make small-checks
```

## Formalization scope

The repository distinguishes four categories deliberately:

1. **Machine-checked theorems** — proved in the Lean library.
2. **External literature inputs** — cited mathematical results not re-proved in Lean.
3. **Finite computational evidence** — useful checks that are not universal proofs.
4. **Open conjectures and questions** — explicitly marked as unresolved.

The manuscript's core exact-list inequality, nested minimizer, exact surplus identity, and Latin-square growth step are represented by Lean proofs. The cubic structural material has a larger boundary: some directions and reductions are formalized, while identified literature-dependent implications remain external.

See `docs/FORMALIZATION_SCOPE.md` and `KNOWN_GAPS.md` for the precise statement-level boundary.

## Continuous verification

Every push to `main` triggers the staged GitHub Actions workflow in `.github/workflows/lean.yml`. The workflow:

- installs the pinned Lean toolchain;
- verifies the pinned Lake dependency graph;
- runs the source formalization audit;
- compiles the full rooted Lean library in stages;
- builds the Heawood certificate modules;
- builds the root library;
- runs `Verification.lean` as a transitive kernel-axiom audit.

The staged workflow is used because the complete rooted library is large.

## Archival release

A versioned release of this repository is intended to be archived on Zenodo. The release DOI and the paper's arXiv identifier will be added here and to the manuscript once minted.

## License

The Lean/Python/build code is licensed under the MIT License; see `LICENSE-CODE`.

Repository documentation and other authored textual material are licensed under Creative Commons Attribution 4.0 International (CC BY 4.0); see `LICENSE-TEXT`.

The root `LICENSE` file summarizes the split licensing.
