# Formalization scope

This document records the frozen mathematical scope of the `BachThesisLean` library. It describes theorem-bearing content and explicit boundaries, rather than the chronology by which the formalization was developed.

## Main exact-list theorem, nested minimizer, and exact surplus

The regular exact-list lower bound, the stronger nonregular nested minimizer, and the exact one-step uncrossing surplus formula are represented by Lean proofs.

- `Uncrossing/Support.lean` formalizes labelled support families, exact incidence, union/intersection uncrossing, preservation of exact incidence, and the strict support-potential increase.
- `Uncrossing/Termination.lean` proves existence of a finite uncrossing chain to a nested exact support family.
- `Uncrossing/Fibre.lean` through `Uncrossing/FibreFlip.lean` prove the full two-label local inequality `twoLabel_local`, including the degree-at-least-three zero case, the degree-at-most-two alternating path argument, parallel edge copies, and an explicit componentwise injection.
- `GlobalPairGraph.lean`, `GlobalPairParity.lean`, and `GlobalPairFlip.lean` freeze all other labels and lift the same component mechanism to a full admissible labeling. `GlobalUncrossing.lean` proves the global one-step inequality and `Monotonicity.lean` propagates it through every finite uncrossing chain.
- `CommonPalette.lean` gives the common-palette/ordinary-colouring equivalence. `MainBound.lean` proves `exactListLowerBound_machineChecked`.
- `Reindex.lean`, `SortedNormalForm.lean`, `Canonical.lean`, and `CanonicalPalette.lean` identify the canonical degree-threshold terminal family. `NestedMinimizer.lean` proves `exactList_count_ge_canonical` and the manuscript specialization `nested_minimizer`.

The exact manuscript surplus layer is also formalized:

- `GlobalSurplus.lean` partitions the global difference into frozen-pair completion fibres.
- `PairResidual.lean`, `PairResidualEquiv.lean`, and `PairResidualUncrossed.lean` identify those fibres with the corresponding residual edge-copy multigraphs before and after uncrossing.
- `ResidualSurplus.lean` expresses each fibre contribution by the exact two-label component count.
- `FibreQR.lean` proves the degree-profile split `freeTwoLabelComponentCount_eq_cycle_add_rightPath`.
- `ManuscriptSurplus.lean` packages the finite contributor set `frozenPairContributors` (the formal `Ψ*`) and proves `uncross_surplus_eq_sum_contributors_pow_q_add_r`, namely

  `N(S,R) - N(S',R) = Σ_{ψ∈Ψ*} 2^(q(Fψ)+r(Fψ))`.

The frozen scope certifies `q` and `r` through the exact finite degree profiles used by the count. `FibreTopology.lean` supplies the corresponding local topology and explicitly handles the two-parallel-edge cycle obstruction. A separate global theorem producing literal spanning multigraph cycle/right--right-path witnesses is not part of the frozen verified scope; this does not weaken the proved surplus identity.

## Latin-square chain

The canonical Latin specialization and growth chain are formalized.

- `Latin/Defs.lean` defines the canonical class `U`, constant-diagonal class `V`, reduced class `rho`, and unrestricted count `L` as finite cardinalities.
- The normalization modules construct explicit equivalences proving `V_m = (m-1)! U_m`, `U_m = rho_m`, and `L_m = m! (m-1)! rho_m`.
- `Latin/Crown.lean` proves the crown ordinary-colouring identity `c_(n-1)(R_n) = V_n`.
- `Residual.lean`, `ResidualColumns.lean`, `ResidualFinalRow.lean`, `ResidualCanonical.lean`, and `ResidualEquiv.lean` construct both directions of the residual/canonical correspondence and prove `CrownResidualLabeling n ≃ CanonicalClass (n+1)`, hence `crownResidual_count_eq_U`.
- `GrowthFromMain.lean` combines that equivalence with the exact-list theorem to obtain the one-step Latin growth inequality and `latin_superfactorial_lowerBound`.

Higher numerical Latin-square values are treated as certified only where explicit Lean certificates are present. The Latin-floor statement remains an open research conjecture.

## Cubic matching and star-product theory

The edge-copy-aware cubic layer includes the following formalized results.

- `RegularMatching.lean`, `ForcedHall.lean`, and `MatchingCovered.lean` prove perfect-matching existence and extension of every prescribed edge copy in a finite cubic bipartite multigraph.
- `PortMasks.lean` and `PortMaskCharacterization.lean` prove `hasEEP_iff_edgeRootMask_card_ge_two`; `TwoPorts.lean` supplies the vertex-root two-port result used later.
- The `StarProduct*.lean` sequence formalizes the explicit star product, degree preservation, perfect-matching construction and decomposition, source restrictions, bridge selection, complementary-factor transport, exact port criteria, and EEP/2EP composition and projection.
- The tight-cut files formalize oriented three-edge tight cuts, both explicit contractions, their degree/connectivity/size properties, reconstruction as a star product, matching extension through the contractions, and the EEP correspondence used by the structural reduction.

## Cubic reduction hierarchy

The rooted library also contains theorem-bearing modules for the later structural reductions.

- `UniversalAmplification.lean` packages the four-vertex amplification reduction.
- `BraceReduction.lean`, `UniversalBraceReduction.lean`, `BraceSimplicity.lean`, and the strict-Hall/two-extendability files establish the brace/simple-brace reductions used by the minimal-counterexample chain.
- The square modules formalize square frames, bad-pair coverage, smoothing, factor transport, connectivity/size control, EEP lifting, and the associated reduction steps.
- The three-, four-, and five-vertex shore modules and `HeawoodCase.lean` provide the included small-case and finite certificates without promoting finite evidence to a universal theorem.
- The TF3 probe modules implement the probe construction, matching and connectivity properties, collapse/separation arguments, and the resulting reduction chain. The unconditional internal implication direction is `TF3 -> EVP -> EEP`.

## Pfaffian layer

The internal Pfaffian witness theory and its structural transport are formalized through tight-cut descent.

- `PfaffianCore.lean`, `PfaffianReference.lean`, `PfaffianRelative.lean`, `PfaffianSpanning.lean`, and `PfaffianIsomorphism.lean` define signed terms, relative permutation signs, reference normalization, witness transport, and graph-isomorphism transport.
- The odd-path-smoothing and square-smoothing Pfaffian modules construct and transport actual `PfaffianWitness` values.
- `TightCutMatchingCommon.lean` supplies common completions for two source matchings using the same boundary port.
- `StarProductPfaffianRelative.lean` and `StarProductPfaffianRelativeB.lean` factor the relative permutation sign on the two source sides.
- `StarProductPfaffianProduct.lean` and `StarProductPfaffianProductB.lean` factor and cancel the edge-sign products.
- `StarProductPfaffianSamePort.lean` and its B-side mirror establish the same-port relative equations.
- `StarProductPfaffianNormalizeA.lean` and `StarProductPfaffianNormalizeB.lean` normalize the three boundary-port classes and construct Pfaffian witnesses for each source factor.
- `TightCutPfaffianSet.lean` proves `pfaffianWitness_contractSet`, `pfaffianWitness_contractComplement`, and the proposition-level theorem returning witnesses for both contractions.

The final result in this layer is the descent direction from a witness on the original graph to witnesses on both explicit contractions. The converse tight-cut Pfaffian implication from the stronger literature-level equivalence is outside the frozen verified scope.

## External literature and research boundary

The formalization does not silently internalize external literature. The reverse brace implication `EVP -> TF3` used in the manuscript relies on Häggkvist; the prescribed-edge theorem attributed to Diwan and the nonplanar Pfaffian-brace result attributed to Gorsky--Johanni--Wiederrecht remain external inputs rather than Lean axioms.

The Latin floor, common-core equality criterion, universal `TF_k` / cubic rainbow-component conjecture, per-edge enumerative Galvin problem, and universal cubic EEP/EVP/TF3 statements not otherwise proved by the rooted modules remain outside the theorem layer. Finite searches do not promote such statements to universal proofs.

The precise proposition-level boundary is recorded in [`../KNOWN_GAPS.md`](../KNOWN_GAPS.md).
