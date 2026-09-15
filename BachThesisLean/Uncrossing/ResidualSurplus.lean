import BachThesisLean.Uncrossing.PairResidualUncrossed

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical BigOperators

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E] [DecidableEq Λ]

/-- The exact contribution of one frozen pair assignment to a one-step
uncrossing surplus. Impossible original fibres contribute zero. For a
nonempty fibre, the residual graph is fixed by `ψ`; a positive contribution
occurs exactly in the degree-two mixed-endpoint case. -/
noncomputable def frozenPairSurplusTerm
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ) : ℕ := by
  classical
  by_cases hbase : Nonempty
      (PairCompletionFiber (exactListsOfSupports S hS) a b ψ)
  · let base := Classical.choice hbase
    let H := frozenPairResidualGraph G ψ
    let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
    exact if (∀ y, H.rightDegree y ≤ 2) ∧
        HasMixedEndpointComponent H (S a) (S b)
      then 2 ^ freeTwoLabelComponentCount (twoLabelLists H (S a) (S b) hdeg)
      else 0
  · exact 0

/-- Fibrewise form of the manuscript surplus identity. The global frozen
completion loss is exactly the guarded binary residual contribution. -/
theorem pairCompletion_surplus_eq_frozenPairSurplusTerm
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b))
    (ψ : E → Option Λ) :
    pairCompletionCount (exactListsOfSupports S hS) a b ψ -
        pairCompletionCount (exactListsOfSupports (uncross S a b) hinc) a b ψ =
      frozenPairSurplusTerm G S hab hS ψ := by
  classical
  by_cases hbase : Nonempty
      (PairCompletionFiber (exactListsOfSupports S hS) a b ψ)
  · let base := Classical.choice hbase
    let H := frozenPairResidualGraph G ψ
    let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
    have horig := pairCompletionCount_eq_twoLabelCount G S hab hS ψ base
    have hunc := pairCompletionCount_uncross_eq_twoLabelUncrossedCount
      G S hab hS hinc ψ base
    rw [horig, hunc]
    change twoLabelOriginalCount H (S a) (S b) hdeg -
        twoLabelUncrossedCount H (S a) (S b) hdeg = _
    rw [twoLabel_surplus_eq H (S a) (S b) hdeg]
    have hex : ∃ σ, (twoLabelLists H (S a) (S b) hdeg).IsAdmissible σ := by
      refine ⟨(pairFiberToResidual G S hab hS ψ base base).val, ?_⟩
      exact (pairFiberToResidual G S hab hS ψ base base).property
    simp [frozenPairSurplusTerm, hbase, base, H, hdeg, hex]
  · have hzero : pairCompletionCount
        (exactListsOfSupports S hS) a b ψ = 0 := by
      unfold pairCompletionCount
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun u => hbase ⟨u⟩⟩
    have hle := pairCompletionCount_uncross_le G S hab hS hinc ψ
    have hzeroU : pairCompletionCount
        (exactListsOfSupports (uncross S a b) hinc) a b ψ = 0 := by
      omega
    simp [hzero, hzeroU, frozenPairSurplusTerm, hbase]

/-- Exact one-step surplus as a sum of guarded powers of two over frozen
assignments. This is the all-fibres form of the manuscript formula; the
`Ψ*` restricted-sum presentation is a subsequent reindexing of its nonzero
terms. -/
theorem uncross_surplus_eq_sum_frozenPairSurplusTerm
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    (exactListsOfSupports S hS).count -
        (exactListsOfSupports (uncross S a b) hinc).count =
      ∑ ψ : E → Option Λ, frozenPairSurplusTerm G S hab hS ψ := by
  classical
  rw [uncross_surplus_eq_sum_fiber_surplus G S hab hS hinc]
  apply Finset.sum_congr rfl
  intro ψ hψ
  exact pairCompletion_surplus_eq_frozenPairSurplusTerm
    G S hab hS hinc ψ

end BachThesisLean
