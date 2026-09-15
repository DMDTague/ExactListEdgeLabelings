import BachThesisLean.Uncrossing.GlobalUncrossing
import BachThesisLean.Uncrossing.MainBound
import Mathlib.Data.Fintype.BigOperators

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped BigOperators

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-- Freeze exactly the labels outside the selected pair. `none` marks an
active actual edge copy, including each parallel copy separately. -/
def freezePair (a b : Λ) (σ : E → Λ) : E → Option Λ :=
  fun e => if σ e = a ∨ σ e = b then none else some (σ e)

/-- The global uncrossing injection fixes its frozen partial labeling. -/
theorem freezePair_globalPairFlip
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (σ : E → Λ) :
    freezePair a b (globalPairFlip G S a b σ) = freezePair a b σ := by
  classical
  funext e
  by_cases hm : reachesRightSdiffGlobal G S a b σ e
  · have hp := (mem_pairEdges σ a b e).1 hm.1
    have hflip := (globalPairFlip_mem_pair_iff G S hab σ e).2 hp
    simp only [freezePair, hp, hflip, ite_true]
  · simp [freezePair, globalPairFlip, hm]

/-- Completions of one frozen partial labeling. -/
abbrev PairCompletionFiber
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ)
    (a b : Λ) (ψ : E → Option Λ) :=
  {σ : L.AdmissibleLabeling // freezePair a b σ.val = ψ}

/-- Number of completions of a frozen partial labeling, with impossible
partial labelings contributing zero. -/
noncomputable def pairCompletionCount
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ)
    (a b : Λ) (ψ : E → Option Λ) : ℕ := by
  classical
  exact Fintype.card (PairCompletionFiber L a b ψ)

/-- The full completion set is the disjoint union of its frozen fibres. -/
theorem count_eq_sum_pairCompletionCount
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ)
    (a b : Λ) :
    L.count = ∑ ψ : E → Option Λ, pairCompletionCount L a b ψ := by
  classical
  rw [count_eq_card,
    ← Fintype.card_congr
      (Equiv.sigmaFiberEquiv (fun σ : L.AdmissibleLabeling => freezePair a b σ.val))]
  simp [Fintype.card_sigma, pairCompletionCount, PairCompletionFiber]

/-- One-step monotonicity holds separately on every frozen fibre. -/
theorem pairCompletionCount_uncross_le
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b))
    (ψ : E → Option Λ) :
    pairCompletionCount (exactListsOfSupports (uncross S a b) hinc) a b ψ ≤
      pairCompletionCount (exactListsOfSupports S hS) a b ψ := by
  classical
  let f : PairCompletionFiber
      (exactListsOfSupports (uncross S a b) hinc) a b ψ →
      PairCompletionFiber (exactListsOfSupports S hS) a b ψ :=
    fun σ => ⟨globalUncrossedToOriginal G S hab hS hinc σ.val, by
      change freezePair a b (globalPairFlip G S a b σ.val.val) = ψ
      rw [freezePair_globalPairFlip G S hab]
      exact σ.property⟩
  apply Fintype.card_le_of_injective f
  intro σ τ h
  apply Subtype.ext
  exact globalUncrossedToOriginal_injective G S hab hS hinc
    (congrArg Subtype.val h)

/-- Exact global decomposition of the surplus into nonnegative frozen-fibre
surpluses. This identity uses the explicit fibre-preserving injection, so
natural-number subtraction never hides a negative summand. -/
theorem uncross_surplus_eq_sum_fiber_surplus
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    (exactListsOfSupports S hS).count -
        (exactListsOfSupports (uncross S a b) hinc).count =
      ∑ ψ : E → Option Λ,
        (pairCompletionCount (exactListsOfSupports S hS) a b ψ -
          pairCompletionCount (exactListsOfSupports (uncross S a b) hinc) a b ψ) := by
  classical
  rw [count_eq_sum_pairCompletionCount (exactListsOfSupports S hS) a b,
    count_eq_sum_pairCompletionCount (exactListsOfSupports (uncross S a b) hinc) a b]
  exact (Finset.sum_tsub_distrib _
    (fun ψ _ => pairCompletionCount_uncross_le G S hab hS hinc ψ)).symm

/-- The manuscript's surplus envelope: every one-step loss is bounded by the
total excess over the ordinary-coloring minimum. -/
theorem uncross_surplus_le_excess
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (S : SupportFamily X Λ) (a b : Λ)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    (exactListsOfSupports S hS).count -
        (exactListsOfSupports (uncross S a b) hinc).count ≤
      (exactListsOfSupports S hS).count - ordinaryCount G k hG := by
  have hbound := exactListLowerBound_machineChecked G k hG
    (exactListsOfSupports (uncross S a b) hinc)
  exact Nat.sub_le_sub_left hbound _

end BachThesisLean
