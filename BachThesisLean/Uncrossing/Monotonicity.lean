import BachThesisLean.Uncrossing.GlobalUncrossing
import BachThesisLean.Uncrossing.Termination

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# Count monotonicity along finite uncrossing chains

`GlobalUncrossing` proves the one-step inequality.  Here it is propagated
through `Relation.ReflTransGen UncrossStep`, matching the termination argument.
The exact-incidence proofs carried by `exactListsOfSupports` are propositions,
so their choice has no effect on the resulting count.
-/

/-- The count attached to a support family is independent of the proof used
to certify exact incidence. -/
theorem exactListsOfSupports_count_proof_irrel
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (h₁ h₂ : ExactSupportIncidence G S) :
    (exactListsOfSupports S h₁).count = (exactListsOfSupports S h₂).count := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- Propositionally equal support families have the same completion count,
independently of the exact-incidence certificates chosen on either side. -/
theorem exactListsOfSupports_count_eq_of_eq
    (G : BipartiteMultigraph X Y E) {S T : SupportFamily X Λ}
    (hS : ExactSupportIncidence G S) (hT : ExactSupportIncidence G T)
    (hST : S = T) :
    (exactListsOfSupports S hS).count = (exactListsOfSupports T hT).count := by
  subst T
  exact exactListsOfSupports_count_proof_irrel G S hS hT

/-- Every finite sequence of legal uncrossings weakly decreases the exact-list
completion count. -/
theorem exactListsOfSupports_reachable_count_le
    (G : BipartiteMultigraph X Y E) {S T : SupportFamily X Λ}
    (hS : ExactSupportIncidence G S) (hT : ExactSupportIncidence G T)
    (hST : Relation.ReflTransGen UncrossStep S T) :
    (exactListsOfSupports T hT).count ≤ (exactListsOfSupports S hS).count := by
  induction hST with
  | refl =>
      rw [exactListsOfSupports_count_proof_irrel G S hT hS]
  | @tail T U hST hstep ih =>
      have hT' : ExactSupportIncidence G T :=
        exactSupportIncidence_reachable G hS hST
      have hprefix :
          (exactListsOfSupports T hT').count ≤
            (exactListsOfSupports S hS).count := ih hT'
      obtain ⟨a, b, habInc, hUeq⟩ := hstep
      have hab : a ≠ b := by
        intro h
        subst b
        exact habInc.1 (Finset.Subset.refl _)
      subst U
      have hone :
          (exactListsOfSupports (uncross T a b) hT).count ≤
            (exactListsOfSupports T hT').count :=
        exactListsOfSupports_uncross_count_le G T hab hT' hT
      exact hone.trans hprefix

/-- Combining finite termination with monotonicity produces a nested exact
support family whose count is no larger than the starting count. -/
theorem exists_nested_exact_uncrossing_count_le
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) :
    ∃ (T : SupportFamily X Λ) (hT : ExactSupportIncidence G T),
      Relation.ReflTransGen UncrossStep S T ∧ IsNested T ∧
      (exactListsOfSupports T hT).count ≤ (exactListsOfSupports S hS).count := by
  obtain ⟨T, hST, hT, hnested⟩ := exists_nested_exact_uncrossing G S hS
  exact ⟨T, hT, hST, hnested,
    exactListsOfSupports_reachable_count_le G hS hT hST⟩

/-- The support family extracted from an exact list assignment satisfies the
same exact-incidence equations. -/
theorem supportFamilyOfLists_exact
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G Λ) :
    ExactSupportIncidence G (supportFamilyOfLists L) := by
  intro x
  rw [listsOfSupports_supportFamilyOfLists L x, L.card_labels x]

/-- Reconstructing lists from their labelled support family preserves the
completion count exactly. -/
theorem exactListsOfSupports_supportFamilyOfLists_count
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G Λ) :
    (exactListsOfSupports (supportFamilyOfLists L)
      (supportFamilyOfLists_exact G L)).count = L.count := by
  classical
  unfold ExactLeftLists.count ExactLeftLists.admissibleLabelings
  apply congrArg Finset.card
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold ExactLeftLists.IsAdmissible
  simp only [exactListsOfSupports, listsOfSupports_supportFamilyOfLists]

end BachThesisLean
