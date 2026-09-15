import BachThesisLean.Uncrossing.FibreGraph
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X]

/-!
# Parity in the two-label fibre line graph

A proper coloring by `Fin 2` alternates along a walk. Thus an odd walk in the
edge-copy line graph has differently colored endpoint edge copies. This is
the parity mechanism used in the manuscript's left--left path row.
-/

/-- Endpoint colors of an odd walk in a properly two-colored graph differ. -/
theorem finTwoColoring_ne_of_odd_walk
    {V : Type*} {H : SimpleGraph V} (c : H.Coloring (Fin 2))
    {u v : V} (p : H.Walk u v) (hodd : Odd p.length) : c u ≠ c v := by
  let cBool : H.Coloring Bool := (H.recolorOfEquiv finTwoEquiv) c
  intro huv
  have hBool : cBool u = cBool v := by
    change finTwoEquiv (c u) = finTwoEquiv (c v)
    exact congrArg finTwoEquiv huv
  have heven : Even p.length := (cBool.even_length_iff_congr p).2 (by
    rw [hBool])
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- An admissible two-label fibre coloring alternates along every odd walk in
the edge-copy line graph. -/
theorem twoLabel_admissible_ne_of_odd_walk
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {σ : E → Fin 2} (hσ : (twoLabelLists G A B hdeg).IsAdmissible σ)
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hodd : Odd p.length) :
    σ e ≠ σ f := by
  exact finTwoColoring_ne_of_odd_walk
    (admissibleFibreColoring (twoLabelLists G A B hdeg) σ hσ) p hodd

/-- In the uncrossed fibre, opposite symmetric-difference left endpoints are
both forced to the union label. Hence they cannot be joined by an odd walk in
the edge-copy line graph. This is the coloring obstruction used for the
manuscript's left--left path component. -/
theorem no_uncrossed_admissible_of_odd_walk_between_opposite_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hodd : Odd p.length)
    (heA : G.left e ∈ A) (heB : G.left e ∉ B)
    (hfB : G.left f ∈ B) (hfA : G.left f ∉ A)
    {σ : E → Fin 2} :
    ¬ (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ := by
  intro hσ
  have hne := twoLabel_admissible_ne_of_odd_walk
    G (A ∪ B) (A ∩ B) (uncrossed_twoLabel_degree G A B hdeg) hσ p hodd
  have he0 := uncrossed_admissible_eq_zero_of_left_mem_sdiff_left
    G A B hdeg hσ e heA heB
  have hf0 := uncrossed_admissible_eq_zero_of_left_mem_sdiff_right
    G A B hdeg hσ f hfB hfA
  exact hne (he0.trans hf0.symm)

/-- Consequently, once an odd edge-copy walk joins opposite
symmetric-difference left endpoints, the uncrossed local completion count is
zero. -/
theorem twoLabelUncrossedCount_eq_zero_of_odd_walk_between_opposite_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hodd : Odd p.length)
    (heA : G.left e ∈ A) (heB : G.left e ∉ B)
    (hfB : G.left f ∈ B) (hfA : G.left f ∉ A) :
    twoLabelUncrossedCount G A B hdeg = 0 := by
  unfold twoLabelUncrossedCount
  apply (count_eq_zero_iff _).mpr
  intro σ hσ
  exact no_uncrossed_admissible_of_odd_walk_between_opposite_sdiff
    G A B hdeg p hodd heA heB hfB hfA hσ

/-- The analogous original-fibre obstruction: two `A \ B` endpoints cannot
be joined by an odd edge-copy walk, since both are forced to label `0`. -/
theorem no_original_admissible_of_odd_walk_between_left_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hodd : Odd p.length)
    (heA : G.left e ∈ A) (heB : G.left e ∉ B)
    (hfA : G.left f ∈ A) (hfB : G.left f ∉ B)
    {σ : E → Fin 2} : ¬ (twoLabelLists G A B hdeg).IsAdmissible σ := by
  intro hσ
  have hne := twoLabel_admissible_ne_of_odd_walk G A B hdeg hσ p hodd
  have he0 := twoLabel_admissible_eq_zero_of_left_mem_sdiff
    G A B hdeg hσ e heA heB
  have hf0 := twoLabel_admissible_eq_zero_of_left_mem_sdiff
    G A B hdeg hσ f hfA hfB
  exact hne (he0.trans hf0.symm)

/-- Likewise two `B \ A` endpoints cannot be joined by an odd edge-copy walk
in an original admissible fibre coloring, since both are forced to label `1`. -/
theorem no_original_admissible_of_odd_walk_between_right_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hodd : Odd p.length)
    (heB : G.left e ∈ B) (heA : G.left e ∉ A)
    (hfB : G.left f ∈ B) (hfA : G.left f ∉ A)
    {σ : E → Fin 2} : ¬ (twoLabelLists G A B hdeg).IsAdmissible σ := by
  intro hσ
  have hne := twoLabel_admissible_ne_of_odd_walk G A B hdeg hσ p hodd
  have he1 := twoLabel_admissible_eq_one_of_left_mem_sdiff
    G A B hdeg hσ e heB heA
  have hf1 := twoLabel_admissible_eq_one_of_left_mem_sdiff
    G A B hdeg hσ f hfB hfA
  exact hne (he1.trans hf1.symm)

end BachThesisLean
