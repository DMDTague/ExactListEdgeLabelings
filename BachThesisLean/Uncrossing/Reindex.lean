import BachThesisLean.Uncrossing.Monotonicity

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z z'

variable {X : Type u} {Y : Type v} {E : Type w}
variable {Λ : Type z} {Γ : Type z'}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [Fintype Λ] [Fintype Γ]
variable [DecidableEq X] [DecidableEq E]
variable [DecidableEq Λ] [DecidableEq Γ]

/-!
# Reindexing labelled support families

Uncrossing keeps labels as indexed slots.  To identify a terminal nested
family with its canonical form we need to reorder those slots without changing
any completion count.  This file packages that transport for an arbitrary
finite label equivalence.
-/

/-- Reindex a support family along an equivalence of label types. -/
def reindexSupport (S : SupportFamily X Λ) (e : Γ ≃ Λ) :
    SupportFamily X Γ :=
  fun c => S (e c)

@[simp] theorem mem_listsOfSupports_reindex
    (S : SupportFamily X Λ) (e : Γ ≃ Λ) (x : X) (c : Γ) :
    c ∈ listsOfSupports (reindexSupport S e) x ↔
      e c ∈ listsOfSupports S x := by
  simp [reindexSupport]

/-- Reindexing preserves the number of support slots containing each vertex. -/
theorem listsOfSupports_reindex_card
    (S : SupportFamily X Λ) (e : Γ ≃ Λ) (x : X) :
    (listsOfSupports (reindexSupport S e) x).card =
      (listsOfSupports S x).card := by
  classical
  refine Finset.card_bij
    (s := listsOfSupports (reindexSupport S e) x)
    (t := listsOfSupports S x)
    (fun c _ => e c) ?_ ?_ ?_
  · intro c hc
    exact (mem_listsOfSupports_reindex S e x c).1 hc
  · intro c hc d hd hcd
    exact e.injective hcd
  · intro d hd
    refine ⟨e.symm d, ?_, ?_⟩
    · exact (mem_listsOfSupports_reindex S e x (e.symm d)).2 (by simpa using hd)
    · simp

/-- Exact incidence is invariant under relabelling the support slots. -/
theorem exactSupportIncidence_reindex
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (e : Γ ≃ Λ) (hS : ExactSupportIncidence G S) :
    ExactSupportIncidence G (reindexSupport S e) := by
  intro x
  rw [listsOfSupports_reindex_card S e x, hS x]

/-- The admissible labelings before and after a support reindexing are
canonically equivalent. -/
noncomputable def reindexAdmissibleEquiv
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (e : Γ ≃ Λ) (hS : ExactSupportIncidence G S) :
    (exactListsOfSupports (reindexSupport S e)
      (exactSupportIncidence_reindex G S e hS)).AdmissibleLabeling ≃
      (exactListsOfSupports S hS).AdmissibleLabeling := by
  classical
  let forward :
      (exactListsOfSupports (reindexSupport S e)
        (exactSupportIncidence_reindex G S e hS)).AdmissibleLabeling →
        (exactListsOfSupports S hS).AdmissibleLabeling := fun s => by
    let τ : E → Λ := fun edge => e (s.1 edge)
    refine ⟨τ, ?_⟩
    apply isAdmissible_of_label_mem_of_injOn
    · intro edge
      have hm := s.2.label_mem edge
      change s.1 edge ∈ listsOfSupports (reindexSupport S e) (G.left edge) at hm
      change e (s.1 edge) ∈ listsOfSupports S (G.left edge)
      exact (mem_listsOfSupports_reindex S e (G.left edge) (s.1 edge)).1 hm
    · intro x edge hedge f hf hEq
      apply s.2.left_injOn x hedge hf
      exact e.injective hEq
    · intro y edge hedge f hf hEq
      apply s.2.right_injOn y hedge hf
      exact e.injective hEq
  let backward :
      (exactListsOfSupports S hS).AdmissibleLabeling →
        (exactListsOfSupports (reindexSupport S e)
          (exactSupportIncidence_reindex G S e hS)).AdmissibleLabeling := fun s => by
    let τ : E → Γ := fun edge => e.symm (s.1 edge)
    refine ⟨τ, ?_⟩
    apply isAdmissible_of_label_mem_of_injOn
    · intro edge
      have hm := s.2.label_mem edge
      change s.1 edge ∈ listsOfSupports S (G.left edge) at hm
      change e.symm (s.1 edge) ∈
        listsOfSupports (reindexSupport S e) (G.left edge)
      apply (mem_listsOfSupports_reindex S e (G.left edge) (e.symm (s.1 edge))).2
      simpa using hm
    · intro x edge hedge f hf hEq
      apply s.2.left_injOn x hedge hf
      exact e.symm.injective hEq
    · intro y edge hedge f hf hEq
      apply s.2.right_injOn y hedge hf
      exact e.symm.injective hEq
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    apply Subtype.ext
    funext edge
    simp [forward, backward]
  · intro s
    apply Subtype.ext
    funext edge
    simp [forward, backward]

/-- Reindexing a support family does not change its completion count. -/
theorem exactListsOfSupports_reindex_count
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (e : Γ ≃ Λ) (hS : ExactSupportIncidence G S) :
    (exactListsOfSupports (reindexSupport S e)
      (exactSupportIncidence_reindex G S e hS)).count =
      (exactListsOfSupports S hS).count := by
  exact count_eq_of_equiv _ _ (reindexAdmissibleEquiv G S e hS)

end BachThesisLean
