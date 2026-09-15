import BachThesisLean.Uncrossing.FibreQR

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical BigOperators

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E] [DecidableEq Λ]

/-!
# Manuscript form of the exact uncrossing surplus

This file repackages the already proved all-frozen-fibres exact identity as the
manuscript's restricted sum over the genuinely contributing frozen assignments
`Ψ*`, with exponent written as `q(F_ψ) + r(F_ψ)`.
-/

/-- A frozen assignment belongs to the manuscript contributor set `Ψ*` exactly
when its original completion fibre is nonempty and its fixed residual graph
satisfies the two local conditions that make the exact surplus positive. -/
def IsFrozenPairContributor
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ) : Prop :=
  Nonempty (PairCompletionFiber (exactListsOfSupports S hS) a b ψ) ∧
    (∀ y, (frozenPairResidualGraph G ψ).rightDegree y ≤ 2) ∧
    HasMixedEndpointComponent (frozenPairResidualGraph G ψ) (S a) (S b)

/-- The finite contributor set `Ψ*`. -/
noncomputable def frozenPairContributors
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (hS : ExactSupportIncidence G S) : Finset (E → Option Λ) := by
  classical
  exact Finset.univ.filter (IsFrozenPairContributor G S a b hS)

@[simp] theorem mem_frozenPairContributors
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ) :
    ψ ∈ frozenPairContributors G S a b hS ↔
      IsFrozenPairContributor G S a b hS ψ := by
  classical
  simp [frozenPairContributors]

/-- Manuscript `q(F_ψ)`: the number of free residual components on the
cycle side of the `q+r` partition. Impossible frozen fibres contribute zero. -/
noncomputable def frozenPairCycleCount
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ) : ℕ := by
  classical
  by_cases hbase : Nonempty
      (PairCompletionFiber (exactListsOfSupports S hS) a b ψ)
  · let base := Classical.choice hbase
    let H := frozenPairResidualGraph G ψ
    let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
    exact freeEvenCycleComponentCount H (twoLabelLists H (S a) (S b) hdeg)
  · exact 0

/-- Manuscript `r(F_ψ)`: the number of free residual components on the
right--right-path side of the `q+r` partition. Impossible fibres contribute
zero. -/
noncomputable def frozenPairRightPathCount
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ) : ℕ := by
  classical
  by_cases hbase : Nonempty
      (PairCompletionFiber (exactListsOfSupports S hS) a b ψ)
  · let base := Classical.choice hbase
    let H := frozenPairResidualGraph G ψ
    let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
    exact freeRightRightPathComponentCount H (twoLabelLists H (S a) (S b) hdeg)
  · exact 0

/-- One frozen surplus term in literal manuscript notation: contributors give
`2^(q+r)` and every other frozen assignment gives zero. -/
theorem frozenPairSurplusTerm_eq_if_contributor_pow_q_add_r
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ) :
    frozenPairSurplusTerm G S hab hS ψ =
      if IsFrozenPairContributor G S a b hS ψ then
        2 ^ (frozenPairCycleCount G S hab hS ψ +
          frozenPairRightPathCount G S hab hS ψ)
      else 0 := by
  classical
  by_cases hbase : Nonempty
      (PairCompletionFiber (exactListsOfSupports S hS) a b ψ)
  · let base := Classical.choice hbase
    let H := frozenPairResidualGraph G ψ
    let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
    have hqr := freeTwoLabelComponentCount_eq_cycle_add_rightPath
      H (twoLabelLists H (S a) (S b) hdeg)
    by_cases hguard : (∀ y, H.rightDegree y ≤ 2) ∧
        HasMixedEndpointComponent H (S a) (S b)
    · have hcontrib : IsFrozenPairContributor G S a b hS ψ := by
        exact ⟨hbase, hguard.1, hguard.2⟩
      simp [frozenPairSurplusTerm, frozenPairCycleCount,
        frozenPairRightPathCount, hbase, base, H, hdeg, hguard, hcontrib, hqr]
    · have hcontrib : ¬ IsFrozenPairContributor G S a b hS ψ := by
        intro hc
        exact hguard ⟨hc.2.1, hc.2.2⟩
      simp [frozenPairSurplusTerm, frozenPairCycleCount,
        frozenPairRightPathCount, hbase, base, H, hdeg, hguard, hcontrib]
  · have hcontrib : ¬ IsFrozenPairContributor G S a b hS ψ := by
      intro hc
      exact hbase hc.1
    simp [frozenPairSurplusTerm, frozenPairCycleCount,
      frozenPairRightPathCount, hbase, hcontrib]

/-- Literal restricted-sum form of the manuscript surplus proposition:

`N(S,R) - N(S',R) = ∑_{ψ ∈ Ψ*} 2^(q(F_ψ)+r(F_ψ))`.

The separate topology layer identifies the two component-count definitions
with actual even cycles and right--right paths. -/
theorem uncross_surplus_eq_sum_contributors_pow_q_add_r
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    (exactListsOfSupports S hS).count -
        (exactListsOfSupports (uncross S a b) hinc).count =
      ∑ ψ ∈ frozenPairContributors G S a b hS,
        2 ^ (frozenPairCycleCount G S hab hS ψ +
          frozenPairRightPathCount G S hab hS ψ) := by
  classical
  rw [uncross_surplus_eq_sum_frozenPairSurplusTerm G S hab hS hinc]
  let C := frozenPairContributors G S a b hS
  let f : (E → Option Λ) → ℕ := fun ψ =>
    2 ^ (frozenPairCycleCount G S hab hS ψ +
      frozenPairRightPathCount G S hab hS ψ)
  calc
    (∑ ψ, frozenPairSurplusTerm G S hab hS ψ) =
        ∑ ψ, if ψ ∈ C then f ψ else 0 := by
          apply Finset.sum_congr rfl
          intro ψ hψ
          rw [frozenPairSurplusTerm_eq_if_contributor_pow_q_add_r
            G S hab hS ψ]
          simp [C, f]
    _ = ∑ ψ ∈ C, f ψ := Fintype.sum_extend_by_zero C f
    _ = ∑ ψ ∈ frozenPairContributors G S a b hS,
          2 ^ (frozenPairCycleCount G S hab hS ψ +
            frozenPairRightPathCount G S hab hS ψ) := rfl

end BachThesisLean
