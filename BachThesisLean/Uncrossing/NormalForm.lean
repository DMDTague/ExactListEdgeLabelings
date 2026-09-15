import BachThesisLean.Uncrossing.Termination
import Mathlib.Order.Interval.Finset.Fin

namespace BachThesisLean

universe u v w

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- A chain of supports gives comparable lists at any two left vertices. -/
theorem listsOfSupports_comparable_of_nested
    {Λ : Type v} [Fintype Λ] [DecidableEq Λ]
    (S : SupportFamily X Λ) (hS : IsNested S) (x y : X) :
    listsOfSupports S x ⊆ listsOfSupports S y ∨
      listsOfSupports S y ⊆ listsOfSupports S x := by
  classical
  by_contra h
  obtain ⟨a, hax, hay⟩ := Finset.not_subset.mp (not_or.mp h).1
  obtain ⟨b, hby, hbx⟩ := Finset.not_subset.mp (not_or.mp h).2
  rcases hS a b with hab | hba
  · exact hbx ((mem_listsOfSupports S x b).mpr
      (hab ((mem_listsOfSupports S x a).mp hax)))
  · exact hay ((mem_listsOfSupports S y a).mpr
      (hba ((mem_listsOfSupports S y b).mp hby)))

/-- Equal list sizes in a nested family force one common list. This does
not require a chosen order on the label alphabet. -/
theorem listsOfSupports_eq_of_nested_of_card
    {Λ : Type v} [Fintype Λ] [DecidableEq Λ]
    (S : SupportFamily X Λ) (hS : IsNested S) (x y : X)
    (hcard : (listsOfSupports S x).card = (listsOfSupports S y).card) :
    listsOfSupports S x = listsOfSupports S y := by
  rcases listsOfSupports_comparable_of_nested S hS x y with hxy | hyx
  · exact Finset.eq_of_subset_of_card_le hxy hcard.ge
  · exact (Finset.eq_of_subset_of_card_le hyx hcard.le).symm

/-- The manuscript's nested terminal normal form, with zero-based indices.
The threshold `m - j.val` is `m - j + 1` in its one-based notation. -/
theorem mem_monotone_support_iff
    {m : ℕ} (S : SupportFamily X (Fin m)) (hS : Monotone S)
    (x : X) (j : Fin m) :
    x ∈ S j ↔ m - j.val ≤ (listsOfSupports S x).card := by
  classical
  constructor
  · intro hx
    have hsub : Finset.Ici j ⊆ listsOfSupports S x := by
      intro i hi
      apply (mem_listsOfSupports S x i).mpr
      exact hS (Finset.mem_Ici.mp hi) hx
    simpa using Finset.card_le_card hsub
  · intro hcard
    by_contra hx
    have hsub : listsOfSupports S x ⊆ Finset.Ioi j := by
      intro i hi
      apply Finset.mem_Ioi.mpr
      apply lt_of_not_ge
      intro hij
      exact hx (hS hij ((mem_listsOfSupports S x i).mp hi))
    have hbound := Finset.card_le_card hsub
    simp only [Fin.card_Ioi] at hbound
    have hj := j.isLt
    omega

/-- An exact chain of supports is determined by the left degree sequence. -/
theorem monotone_support_normalForm
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) {m : ℕ}
    (S : SupportFamily X (Fin m)) (hmono : Monotone S)
    (hexact : ExactSupportIncidence G S) (j : Fin m) :
    S j = Finset.univ.filter (fun x => m - j.val ≤ G.leftDegree x) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_monotone_support_iff S hmono x j, hexact x]

/-- In the regular case a nested slot is either full or empty, exactly at
the specified threshold. This statement also covers zero degree. -/
theorem monotone_regular_support
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) {m k : ℕ}
    (S : SupportFamily X (Fin m)) (hmono : Monotone S)
    (hexact : ExactSupportIncidence G S) (hregular : G.IsLeftRegular k)
    (j : Fin m) :
    S j = if m - j.val ≤ k then Finset.univ else ∅ := by
  rw [monotone_support_normalForm G S hmono hexact]
  have hreg (x : X) : G.leftDegree x = k := hregular x
  simp_rw [hreg]
  split_ifs <;> simp_all

end BachThesisLean
