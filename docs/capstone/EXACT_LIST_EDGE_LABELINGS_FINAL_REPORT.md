# Exact List-Edge Labelings on Finite Bipartite Multigraphs

## Current research and formalization report

The project works with finite bipartite multigraphs in the literal edge-copy sense: parallel edges are distinct elements of the edge type and remain distinct in every matching, labeling, residual graph, and count.

## Main exact-list result

For a left-`k`-regular finite bipartite multigraph and an exact left-list assignment of size `k`, the principal inequality

\[
N(L,R) \ge c_k(R)
\]

is Lean-proved. The formal proof uses indexed supports, union/intersection uncrossing, an exact two-label fibre comparison, a frozen-label global lift, monotonicity, a strictly increasing finite potential, termination at a nested support family, and common-palette normalization. The regular theorem is `exactListLowerBound_machineChecked`, and the source also contains the stronger nonregular nested-minimizer theorem.

The theorem concerns lists attached to left vertices and shared by their incident edge copies. Arbitrary per-edge list assignments form a broader problem and are not covered automatically.

## Exact surplus identity

The corrected manuscript one-step surplus is Lean-proved. `ManuscriptSurplus.lean` constructs the finite contributor set and proves

\[
N(S,R)-N(S',R)=\sum_{\psi\in\Psi^*}2^{q(F_\psi)+r(F_\psi)}.
\]

The theorem is `uncross_surplus_eq_sum_contributors_pow_q_add_r`. The chain through `GlobalSurplus`, the `PairResidual*` modules, `ResidualSurplus`, and `FibreQR` proves the exact numerical identity and exponent.

`FibreTopology.lean` additionally proves literal local topological consequences of the component profiles: represented right endpoints are genuine leaves of the edge-copy line graph, while the exceptional no-right-endpoint degree-one case produces a distinct parallel mate with the same endpoints. This isolates the genuine two-parallel-edge multigraph cycle, whose simple line graph is only `K₂`.

A final global witness theorem packaging every `q` component literally as an even multigraph cycle and every `r` component literally as a right--right path remains an expository strengthening. It is not a missing counting theorem.

## Latin specialization

The graph/purely-parallel specialization is formalized through the crown correspondence, canonical normalization equivalences, the residual/canonical bijection, the one-step growth inequality, and `latin_superfactorial_lowerBound`. This does not establish the analogous statement for arbitrary matroids.

## Cubic theory

The rooted source contains proofs for cubic perfect-matching existence and prescribed-edge-copy extension, port masks and two-port structure, star-product matching and factor decomposition, EEP/2EP composition and projection, explicit tight-cut contractions and reconstruction, brace/simple-brace reductions, amplification, square smoothing and lifting, small-shore cases, Heawood regression, and the TF3 probe chain.

The unconditional internal implication direction is

\[
TF3 \Longrightarrow EVP \Longrightarrow EEP.
\]

Universal cubic `TF3` remains open in the project.

## Pfaffian descent

The internal Pfaffian layer defines signed matching terms and actual `PfaffianWitness` values. It proves reference and relative-sign theory, isomorphism transport, odd-path and square-smoothing witness transfer, A- and B-side star-product relative/product factorizations, same-port identities, and three-port normalization.

`Cubic/TightCutPfaffianSet.lean` packages the endpoint of that internal chain: under its explicit connected, cubic, and oriented tight-cut hypotheses, a Pfaffian witness on the original graph yields witnesses on both explicit contractions. This is the descent direction only. The converse implication from Pfaffian witnesses on the contractions back to a witness on the original graph, which appears as part of a stronger literature-level tight-cut equivalence, is not currently formalized here.

This does not erase the manuscript's external literature boundary. The Häggkvist theorem used for the reverse brace implication `EVP -> TF3`, the planar prescribed-edge result attributed to Diwan, and the nonplanar Pfaffian-brace result attributed to Gorsky--Johanni--Wiederrecht remain external unless separately formalized. They are not introduced as Lean axioms.

## Finite evidence

Finite searches are retained as evidence and regression checks only inside their stated domains. For the explicit six-by-six graph examined in the project, the corrected counts are 18 full perfect matchings, 12 after the selected deletion, 8 witnesses, and therefore a witness fraction of `2/3`, not `1/17`.

## Open research boundary

The present theorem layer does not claim solutions to:

- the common-core equality converse in full generality;
- universal `TF_k` or universal cubic `TF3`;
- the Latin-floor conjecture for arbitrary matroids;
- arbitrary per-edge enumerative list-coloring analogues;
- the converse tight-cut Pfaffian implication just described;
- the named external Häggkvist, Diwan, or Gorsky--Johanni--Wiederrecht results without explicit hypotheses or separate formalization.

## Lean trust and certification

The source audit rejects `sorry`, `admit`, user `axiom`, unchecked `opaque`, `native_decide`, `sorryAx`, and related placeholder devices; it also checks the inventory and rooted import coverage. `Verification.lean` imports the complete library and checks the transitive axioms of public theorems and definitions in the `BachThesisLean` namespace, allowing only `propext`, `Classical.choice`, and `Quot.sound`. It also enforces a conservative lower bound on the number of theorem constants audited so an accidentally empty or severely truncated import environment cannot pass vacuously.

Whole-repository certification therefore means a successful source audit, complete root `lake build`, and `lake env lean Verification.lean`. The repository-level certification contract is recorded in `docs/VERIFICATION.md`; focused theorem builds are not silently upgraded to that stronger claim.
