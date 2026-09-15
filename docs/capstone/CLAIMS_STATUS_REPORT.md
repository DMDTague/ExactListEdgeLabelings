# Claims status report

This document records the current boundary between Lean-certified mathematics, finite evidence, external literature, and open research claims in `BachThesisLean`.

A statement is called **Lean-proved** here when it has an explicit proof term in the rooted library. Repository-wide clean-tree certification is recorded separately in `docs/VERIFICATION.md` only after a complete `lake build` and `lake env lean Verification.lean` pass.

## Lean-proved internal mathematics

The rooted source now contains explicit proofs for:

- the exact-list model on literal edge-copy bipartite multigraphs;
- indexed support/list conversion and union/intersection uncrossing;
- the local two-label inequality and frozen-label global lift;
- monotonicity, finite termination, nested normal form, and common-palette normalization;
- the regular exact-list lower bound `exactListLowerBound_machineChecked` and the stronger nonregular nested-minimizer theorem;
- the corrected manuscript one-step surplus identity `uncross_surplus_eq_sum_contributors_pow_q_add_r`, with an actual finite contributor set and exact exponent `q+r`;
- the Latin residual/canonical equivalences, one-step growth inequality, and `latin_superfactorial_lowerBound`;
- cubic perfect-matching, port-mask, star-product, tight-cut, brace/simple-brace, amplification, smoothing, small-shore, Heawood, and TF3-probe machinery;
- the unconditional internal implication chain `TF3 -> EVP -> EEP`;
- Pfaffian reference/relative sign theory, isomorphism and smoothing transport, A- and B-side star-product factorization and normalization, and Pfaffian witness descent through both explicit tight-cut contractions.

## Surplus topology wording

The numerical surplus theorem is complete. `FibreQR.lean` proves the exact free-component degree-profile split used by the exponent. `FibreTopology.lean` additionally proves that represented right endpoints are literal leaves of the edge-copy line graph and that the exceptional no-right-endpoint degree-one case produces an actual distinct parallel mate. This isolates the genuine two-parallel-edge multigraph cycle that a simple line graph represents only as `K₂`.

A final global witness theorem packaging every `q` component literally as an even multigraph cycle and every `r` component literally as a right--right path remains an expository strengthening. It is not a missing counting theorem.

## External or open boundaries

The following are not claimed as internally proved universal results:

- the common-core equality converse;
- universal `TF_k` or universal cubic `TF3`;
- the full matroid Latin-floor conjecture;
- arbitrary per-edge list-counting analogues;
- the Häggkvist theorem used for the reverse brace implication `EVP -> TF3`;
- the planar prescribed-edge result attributed to Diwan;
- the nonplanar Pfaffian-brace result attributed to Gorsky--Johanni--Wiederrecht.

The named literature inputs are not introduced as Lean axioms.

## Corrected historical claims

- The explicit six-by-six graph statistic is `18` full perfect matchings, `12` after the selected deletion, `8` witnesses, hence `2/3`, not `1/17`.
- Connected cubic bipartite multigraphs need not be three-edge-connected.
- The corrected surplus expression requires the formal residual hypotheses now present in the Lean theorem.
- The historical unrestricted identity-minimizer assertion is not used; the proof proceeds by indexed supports and nested minimizers.
- Higher parallel multiplicity does not hide an unbounded connected cubic search family: multiplicity above three is impossible, while three parallel copies isolate a two-vertex cubic component.

## Trust boundary

The source audit rejects placeholder proof devices including `sorry`, `admit`, user `axiom`, unchecked `opaque`, `native_decide`, and `sorryAx`, checks the formalization inventory, and verifies that local modules are rooted. `Verification.lean` imports the complete library and rejects transitive theorem axioms outside `propext`, `Classical.choice`, and `Quot.sound`.

Finite searches remain evidence only for the domains actually enumerated; they are never promoted to universal theorem inputs.
