import BachThesisLean.Basic.Counting

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X]

/-!
# The two-label fibre

This file begins the manuscript's local uncrossing lemma. After all labels
other than a chosen pair are frozen, the remaining graph has left degree

`1_A(x) + 1_B(x)`.

The original completion problem uses the two supports `A,B`; the uncrossed
problem uses `A ∪ B, A ∩ B`. The first branch of the manuscript proof is the
palette obstruction: if some right vertex has degree at least three, neither
two-label problem has a completion.
-/

/-- The exact two-label list assignment associated with supports `A` and `B`.
Label `0` has support `A` and label `1` has support `B`. -/
noncomputable def twoLabelLists
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) :
    ExactLeftLists G (Fin 2) where
  labels := fun x =>
    if x ∈ A then
      if x ∈ B then {0, 1} else {0}
    else
      if x ∈ B then {1} else ∅
  card_labels := by
    classical
    intro x
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B
    all_goals simp [hA, hB, hdeg x]

/-- Union/intersection preserves the required left degree in the two-label
fibre. This is the local incidence identity behind uncrossing. -/
theorem uncrossed_twoLabel_degree
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) :
    ∀ x, G.leftDegree x =
      (if x ∈ A ∪ B then 1 else 0) +
      (if x ∈ A ∩ B then 1 else 0) := by
  intro x
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B
  all_goals simpa [hA, hB] using hdeg x

/-- Every left degree in a two-label fibre is at most two. -/
theorem twoLabel_leftDegree_le_two
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (x : X) : G.leftDegree x ≤ 2 := by
  rw [hdeg x]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]

/-- The degree-one left vertices are exactly the symmetric-difference
endpoints from the manuscript's path analysis. -/
theorem twoLabel_leftDegree_eq_one_iff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (x : X) :
    G.leftDegree x = 1 ↔
      (x ∈ A ∧ x ∉ B) ∨ (x ∉ A ∧ x ∈ B) := by
  rw [hdeg x]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]

/-- The degree-two left vertices are precisely `A ∩ B`. -/
theorem twoLabel_leftDegree_eq_two_iff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (x : X) :
    G.leftDegree x = 2 ↔ x ∈ A ∧ x ∈ B := by
  rw [hdeg x]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]

@[simp] theorem zero_mem_twoLabelLists_labels
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (x : X) :
    (0 : Fin 2) ∈ (twoLabelLists G A B hdeg).labels x ↔ x ∈ A := by
  classical
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    simp [twoLabelLists, hA, hB]

@[simp] theorem one_mem_twoLabelLists_labels
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (x : X) :
    (1 : Fin 2) ∈ (twoLabelLists G A B hdeg).labels x ↔ x ∈ B := by
  classical
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    simp [twoLabelLists, hA, hB]

/-- At an `A \ B` left endpoint the original fibre forces label `0`. -/
theorem twoLabel_admissible_eq_zero_of_left_mem_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {σ : E → Fin 2} (hσ : (twoLabelLists G A B hdeg).IsAdmissible σ)
    (e : E) (hA : G.left e ∈ A) (hB : G.left e ∉ B) : σ e = 0 := by
  have hm := hσ.label_mem e
  simpa [twoLabelLists, hA, hB] using hm

/-- At a `B \ A` left endpoint the original fibre forces label `1`. -/
theorem twoLabel_admissible_eq_one_of_left_mem_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {σ : E → Fin 2} (hσ : (twoLabelLists G A B hdeg).IsAdmissible σ)
    (e : E) (hB : G.left e ∈ B) (hA : G.left e ∉ A) : σ e = 1 := by
  have hm := hσ.label_mem e
  simpa [twoLabelLists, hA, hB] using hm

/-- After uncrossing, an endpoint in `A \ B` lies in the union but not the
intersection, so its incident edge is forced to the union label `0`. -/
theorem uncrossed_admissible_eq_zero_of_left_mem_sdiff_left
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {σ : E → Fin 2}
    (hσ : (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ)
    (e : E) (hA : G.left e ∈ A) (hB : G.left e ∉ B) : σ e = 0 := by
  exact twoLabel_admissible_eq_zero_of_left_mem_sdiff
    G (A ∪ B) (A ∩ B) (uncrossed_twoLabel_degree G A B hdeg) hσ e
      (by simp [hA]) (by simp [hA, hB])

/-- After uncrossing, an endpoint in `B \ A` is likewise forced to the union
label `0`. This is the obstruction on left--left path components. -/
theorem uncrossed_admissible_eq_zero_of_left_mem_sdiff_right
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {σ : E → Fin 2}
    (hσ : (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ)
    (e : E) (hB : G.left e ∈ B) (hA : G.left e ∉ A) : σ e = 0 := by
  exact twoLabel_admissible_eq_zero_of_left_mem_sdiff
    G (A ∪ B) (A ∩ B) (uncrossed_twoLabel_degree G A B hdeg) hσ e
      (by simp [hB]) (by simp [hA, hB])

/-- The manuscript's original local completion count `α(F;A,B)`. -/
noncomputable def twoLabelOriginalCount
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) : ℕ :=
  (twoLabelLists G A B hdeg).count

/-- The manuscript's uncrossed local completion count
`β(F;A∪B,A∩B)`. -/
noncomputable def twoLabelUncrossedCount
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) : ℕ :=
  (twoLabelLists G (A ∪ B) (A ∩ B)
    (uncrossed_twoLabel_degree G A B hdeg)).count

/-- If a right vertex has degree at least three, the original two-label fibre
has no valid completion. -/
theorem twoLabelOriginalCount_eq_zero_of_rightDegree_ge_three
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (y : Y) (hy : 3 ≤ G.rightDegree y) :
    twoLabelOriginalCount G A B hdeg = 0 := by
  unfold twoLabelOriginalCount
  apply count_eq_zero_of_rightDegree_gt_card _ y
  simpa only [Fintype.card_fin] using
    (lt_of_lt_of_le (by decide : 2 < 3) hy)

/-- The same palette obstruction kills the uncrossed two-label fibre. -/
theorem twoLabelUncrossedCount_eq_zero_of_rightDegree_ge_three
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (y : Y) (hy : 3 ≤ G.rightDegree y) :
    twoLabelUncrossedCount G A B hdeg = 0 := by
  unfold twoLabelUncrossedCount
  apply count_eq_zero_of_rightDegree_gt_card _ y
  simpa only [Fintype.card_fin] using
    (lt_of_lt_of_le (by decide : 2 < 3) hy)

/-- First case of the manuscript's local uncrossing lemma: when a right
vertex has degree at least three, both sides vanish, hence the desired local
inequality holds with equality. -/
theorem twoLabel_local_of_rightDegree_ge_three
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (y : Y) (hy : 3 ≤ G.rightDegree y) :
    twoLabelUncrossedCount G A B hdeg ≤ twoLabelOriginalCount G A B hdeg := by
  rw [twoLabelUncrossedCount_eq_zero_of_rightDegree_ge_three G A B hdeg y hy,
    twoLabelOriginalCount_eq_zero_of_rightDegree_ge_three G A B hdeg y hy]

end BachThesisLean
