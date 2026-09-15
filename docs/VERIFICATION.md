# Verification contract

This document states what repository-level verification means for `BachThesisLean` and records the certification procedure and trust boundary.

## Pinned environment

The repository is pinned to Lean 4.19.0 and Mathlib v4.19.0 through `lean-toolchain` and `lake-manifest.json`.

## Required checks

A repository snapshot is certified only when all of the following succeed on that same snapshot:

```text
python scripts/check_formalization.py
lake build
lake env lean Verification.lean
```

The first command performs the source-level audit. It rejects forbidden placeholder/trust-bypass tokens, checks formatting invariants used by the audit, verifies that registered bare proposition targets are documented in `KNOWN_GAPS.md`, and confirms that every local library module is reachable from the root `BachThesisLean` import.

The second command elaborates and compiles the complete rooted Lean library under the pinned dependency graph.

The third command performs the transitive kernel-axiom audit over the public `BachThesisLean` theorem and definition layer and enforces the theorem-floor/non-vacuity checks encoded in `Verification.lean`.

## Trust boundary

The verification policy permits only Lean's standard logical axioms used by the formal development: `propext`, `Classical.choice`, and `Quot.sound`. Source-level placeholder proofs, user-introduced axioms, unchecked opaque proof shortcuts, and unrooted local Lean modules are rejected by the combined checks.

A successful certification establishes that the declarations imported by the root library elaborate under the pinned toolchain and satisfy the repository's source and kernel-audit policy. It does not turn external literature results, finite computations, or explicitly open conjectures into Lean theorems.

## Frozen mathematical scope

The mathematical content to which this verification contract applies is described in [`FORMALIZATION_SCOPE.md`](FORMALIZATION_SCOPE.md). The explicit boundary between machine-checked results and non-formalized statements is documented in [`../KNOWN_GAPS.md`](../KNOWN_GAPS.md).

