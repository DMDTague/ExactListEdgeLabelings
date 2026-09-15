# Formalization boundary

This file records the frozen boundary between theorem declarations accepted by Lean's
kernel and manuscript statements, terminology, helper proposition aliases, or
external inputs that are not part of the machine-checked theorem layer. It is also consumed by
`scripts/check_formalization.py`: a bare zero-argument `def ... : Prop` or
`abbrev ... : Prop` target is permitted only when its declaration name is
listed here. Registration in this file is not by itself a claim that the
registered proposition is an open conjecture; proved targets and explicit
helper hypotheses are also recorded so they cannot be mistaken for silently
asserted results.

## Main uncrossing chain

- `ExactListLowerBound` remains a named proposition target for stable use by
  later reductions, but it is not an open formalization gap:
  `Uncrossing/MainBound.lean` proves it as
  `exactListLowerBound_machineChecked`.
- The local two-label completion inequality `lem:local` is kernel-checked.
  `Uncrossing/Fibre.lean` supplies the exact two-label fibre and support facts;
  `FibreGraph.lean`, `FibreStructure.lean`, `FibreAlternation.lean`, and
  `FibrePathParity.lean` formalize the edge-copy line graph, alternating
  path structure, and parity arguments without identifying parallel edge
  copies. `FibreComponents.lean` and `FibreFlip.lean` construct the canonical
  componentwise flip and prove `twoLabel_local`.
- The local construction is lifted to arbitrary full list assignments by
  `GlobalPairGraph.lean`, `GlobalPairParity.lean`, and `GlobalPairFlip.lean`.
  `GlobalUncrossing.lean` proves the one-step global inequality and
  `Monotonicity.lean` propagates it through finite uncrossing chains.
- Finite termination, exact-incidence preservation, the nested terminal form,
  the common-palette reduction, and the regular exact-list lower bound are
  kernel-checked. `Reindex.lean`, `SortedNormalForm.lean`, `Canonical.lean`,
  `CanonicalPalette.lean`, and `NestedMinimizer.lean` also prove the stronger
  nonregular degree-sequence nested minimizer `nested_minimizer`.
- The manuscript's exact one-step surplus identity is now formalized.
  `GlobalSurplus.lean` decomposes the count difference into frozen-pair fibres;
  `PairResidual*.lean` and `ResidualSurplus.lean` identify those fibres with
  the actual residual multigraphs; `FibreQR.lean` splits every free binary
  component into the two degree profiles contributing the exponent; and
  `ManuscriptSurplus.lean` defines the finite contributor set
  `frozenPairContributors` (the formal `Ψ*`) and proves

  `N(S,R) - N(S',R) = Σ_{ψ∈Ψ*} 2^(q(Fψ)+r(Fψ))`

  as `uncross_surplus_eq_sum_contributors_pow_q_add_r`.
- One semantic strengthening is outside the frozen scope around the names `q` and `r`.
  `FibreQR.lean` proves the exact degree-profile classification used by the
  count: a free component has either no represented right degree-one endpoint
  or at least one. The first profile has represented left and right degrees
  all equal to two; the second has a represented right endpoint.
  `FibreTopology.lean` proves the corresponding local graph facts, including
  the genuine two-parallel-edge cycle obstruction. A separate global witness
  theorem identifying every first-profile component literally with an even
  multigraph cycle and every second-profile component literally with a
  right--right path is not yet packaged. This does not leave the surplus count
  or exponent identity open.

## Latin/residual chain

- The crown correspondence proves `c_(n-1)(R_n) = V_n`. The standard Latin
  normalization chain is kernel-checked: `V_m = (m-1)! U_m`, `U_m = rho_m`,
  and `L_m = m! (m-1)! rho_m` are represented by explicit equivalences and
  counting theorems in the `Latin` modules.
- `Residual.lean`, `ResidualColumns.lean`, `ResidualFinalRow.lean`,
  `ResidualCanonical.lean`, and `ResidualEquiv.lean` prove the residual
  exact-list correspondence and the finite equivalence
  `CrownResidualLabeling n ≃ CanonicalClass (n+1)`, yielding
  `crownResidual_count_eq_U`.
- `GrowthFromMain.lean` combines that bijection with the machine-checked
  exact-list bound and proves the manuscript one-step growth inequality and
  `latin_superfactorial_lowerBound` without importing an external one-step
  hypothesis.
- Higher numerical Latin-square values printed in the manuscript are not
  promoted to theorems without kernel-checkable enumeration certificates.
  The current regression layer includes only the explicitly certified small
  orders. The Latin-floor statement remains an open research conjecture, not
  a gap in the proved growth chain.

## Cubic theory

The edge-copy cubic infrastructure is now substantially formalized rather than
merely defined. In particular:

- `RegularMatching.lean`, `ForcedHall.lean`, and `MatchingCovered.lean` prove
  Hall-type matching existence and extension of every prescribed cubic edge
  copy to a perfect matching.
- `PortMasks.lean`, `PortMaskCharacterization.lean`, and `TwoPorts.lean` prove
  the connected-cubic EEP/root-mask characterization and the two-port bound.
- The `StarProduct*.lean` modules formalize star-product degrees, perfect
  matching construction and decomposition, factor transport, the exact port
  criteria used by the reduction, and EEP/2EP composition and projection.
- The `TightCut*.lean` modules formalize the oriented three-edge tight-cut
  contractions, their degree/connectivity/size properties, reconstruction as
  a star product, matching extension, and the EEP correspondence needed by the
  structural reduction.
- `UniversalAmplification.lean`, `UniversalBraceReduction.lean`, the
  small-shore brace/minimal-counterexample modules, the square-smoothing
  modules, and the TF3 probe modules formalize the corresponding reduction
  layers. Finite checks remain evidence only where no universal theorem is
  proved.
- `SurvivorCoreConnected` in `SquareSmoothingConnectivity.lean` is a
  registered zero-argument helper proposition alias, not an open conjecture.
  `survivorCoreConnected_of_minCut_three` proves it from the explicit global
  three-edge-cut lower bound used by the square-smoothing reduction.
- `PfaffianCore.lean`, `PfaffianReference.lean`, `PfaffianRelative.lean`,
  `PfaffianSpanning.lean`, and `PfaffianIsomorphism.lean` give the internal
  Pfaffian witness/sign formalism and transport. Odd-path smoothing and square
  smoothing have machine-checked Pfaffian witness transfer modules.
- Tight-cut Pfaffian descent is now formalized to both explicit contractions.
  The `StarProductPfaffianRelative*`, `StarProductPfaffianProduct*`,
  `StarProductPfaffianSamePort*`, and `StarProductPfaffianNormalize*` modules
  prove the same-port relative identities and three-port normalization for
  both source factors. `TightCutPfaffianSet.lean` packages
  `pfaffianWitness_contractSet`, `pfaffianWitness_contractComplement`, and the
  proposition-level theorem returning witnesses for both contractions.
  This is the descent direction: a witness on the original graph yields
  witnesses on both contractions. The converse tight-cut Pfaffian implication,
  which is part of the stronger literature-level equivalence, is not currently
  formalized in this repository.

The following boundaries are intentionally not filled by assumptions:

- the manuscript's reverse brace implication from EVP to TF3 uses the external
  Häggkvist theorem; internally the unconditional direction is
  `TF3 -> EVP -> EEP`;
- the planar prescribed-edge input attributed to Diwan and the nonplanar
  Pfaffian-brace input attributed to Gorsky--Johanni--Wiederrecht remain
  external literature boundaries unless separately formalized from first
  principles;
- the converse tight-cut Pfaffian direction is not asserted merely because a
  literature theorem gives an equivalence at a more general structural level;
- finite regression searches, including Heawood and small cubic instances,
  are not universal proofs by themselves.

## Open manuscript conjectures

The Latin floor, common-core equality criterion, universal `TF_k` / cubic
rainbow-component conjecture, and per-edge enumerative Galvin problem remain
research conjectures. They must not be introduced as axioms or theorem
constants. Universal cubic EEP/EVP/TF3 is likewise not inferred merely from
finite regression evidence or from one direction of the implication chain.
