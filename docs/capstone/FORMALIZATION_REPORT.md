# BachThesisLean — formalization report

`BachThesisLean` formalizes the internal mathematical content of *Exact List-Edge Labelings on Bipartite Multigraphs: Uncrossing, Nested Minimizers, Equality, and Cubic Two-Factors*. Parallel edges are literal distinct edge copies throughout the development.

## Exact-list theorem

The exact-list lower bound is Lean-proved. For a finite bipartite multigraph whose left vertices all have degree `k`, every exact left-list assignment of size `k` has at least as many admissible labelings as the graph has proper edge-colorings by the fixed labelled palette `Fin k`.

The proof is implemented through indexed supports, union/intersection uncrossing, the local two-label comparison, the frozen-label global lift, monotonicity, finite termination, nested normal form, and common-palette normalization. The regular theorem is `exactListLowerBound_machineChecked`; the source also proves a stronger nonregular nested-minimizer statement.

## Exact surplus

The corrected one-step manuscript surplus is Lean-proved as

`uncross_surplus_eq_sum_contributors_pow_q_add_r`.

The contributor set is a genuine finite Lean object, and the exponent is the exact component statistic proved in `FibreQR.lean`. `FibreTopology.lean` additionally connects the degree profiles to literal local topology, including the two-parallel-edge cycle obstruction. A final global theorem packaging every profile as a spanning multigraph cycle or right--right path remains an exposition-level strengthening, not a missing numerical step.

## Latin specialization

The crown correspondence, normalization equivalences, residual/canonical bijection, one-step growth inequality, and `latin_superfactorial_lowerBound` are Lean-proved for the graph/purely-parallel specialization. This does not settle the corresponding counting statement for arbitrary matroids.

## Cubic and Pfaffian theory

The cubic source proves matching-coveredness, prescribed-edge-copy extension, port-mask and two-port results, star-product matching/factor decomposition, EEP/2EP composition and projection, explicit tight-cut contraction/reconstruction, brace and simple-brace reductions, amplification, square smoothing/lifting, small-shore cases, Heawood regression, and the TF3 probe chain. The unconditional internal implication direction is `TF3 -> EVP -> EEP`.

The Pfaffian layer defines actual `PfaffianWitness` values and proves reference/relative sign theory, isomorphism transport, odd-path and square-smoothing transport, A- and B-side star-product relative/product factorization, same-port identities, three-port normalization, and tight-cut descent. `TightCutPfaffianSet.lean` constructs Pfaffian witnesses for both `contractSet` and `contractComplement` under its stated connected/cubic/oriented-tight-cut hypotheses.

## Boundaries that remain external or open

The project does not claim internal proofs of the common-core equality converse, universal `TF_k`, universal cubic `TF3`, the general matroid Latin-floor conjecture, or arbitrary per-edge list-counting analogues. The Häggkvist, Diwan, and Gorsky--Johanni--Wiederrecht literature inputs remain external unless separately formalized; they are not smuggled into the source as axioms.

## Mechanical trust boundary

The source audit rejects placeholder proof devices and checks that local modules are rooted. `Verification.lean` imports the full library and audits the transitive axioms of public `BachThesisLean` theorem constants, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

A focused module compile is not described as whole-repository certification. The exact current clean-tree build and kernel-audit state is recorded separately in `docs/VERIFICATION.md` after those checks actually complete.
