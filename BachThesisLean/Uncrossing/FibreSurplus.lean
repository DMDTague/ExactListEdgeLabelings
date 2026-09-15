import BachThesisLean.Uncrossing.FibreCount
import BachThesisLean.Uncrossing.FibreFlip

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq E]

/-- Exactness identifies a full two-label list with left degree two. -/
theorem twoLabel_labels_eq_univ_iff
    {G : BipartiteMultigraph X Y E}
    (L : ExactLeftLists G (Fin 2)) (x : X) :
    L.labels x = Finset.univ ↔ G.leftDegree x = 2 := by
  classical
  rw [← L.card_labels x]
  exact (Finset.card_eq_iff_eq_univ (L.labels x)).symm

/-- The free components depend only on the residual graph, not on the endpoint
labels. Thus the original and uncrossed systems have the same binary factors
whenever both are consistent. -/
theorem freeTwoLabelComponentCount_eq
    {G : BipartiteMultigraph X Y E}
    (L K : ExactLeftLists G (Fin 2)) :
    freeTwoLabelComponentCount L = freeTwoLabelComponentCount K := by
  classical
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro c
  simp only [IsFreeTwoLabelComponent, twoLabel_labels_eq_univ_iff]

/-- An edge-copy component joining opposite forced left endpoint types. In a
consistent degree-two fibre this is precisely a left--left path component. -/
def HasMixedEndpointComponent
    (G : BipartiteMultigraph X Y E) (A B : Finset X) : Prop :=
  ∃ e f : E,
    G.left e ∈ A ∧ G.left e ∉ B ∧
    G.left f ∈ B ∧ G.left f ∉ A ∧
    (fibreLineGraph G).Reachable e f

/-- When no opposite endpoint types share a component, the same canonical
flip converts an original completion to an uncrossed completion. -/
theorem flipRightComponents_isAdmissible_uncrossed
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hno : ¬ HasMixedEndpointComponent G A B)
    {σ : E → Fin 2} (hσ : (twoLabelLists G A B hdeg).IsAdmissible σ) :
    (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible
      (flipRightComponents G A B σ) := by
  classical
  apply isAdmissible_of_label_mem_of_injOn
  · intro e
    by_cases hA : G.left e ∈ A <;> by_cases hB : G.left e ∈ B
    · have hfull :
          (twoLabelLists G (A ∪ B) (A ∩ B)
            (uncrossed_twoLabel_degree G A B hdeg)).labels (G.left e) =
            Finset.univ := by
        apply (twoLabel_labels_eq_univ_iff _ _).2
        simp [hdeg, hA, hB]
      rw [hfull]
      exact Finset.mem_univ _
    · have hm : ¬ reachesRightSdiffEndpoint G A B e := by
        rintro ⟨f, hef, hfB, hfA⟩
        exact hno ⟨e, f, hA, hB, hfB, hfA, hef⟩
      have hs := twoLabel_admissible_eq_zero_of_left_mem_sdiff
        G A B hdeg hσ e hA hB
      simp [flipRightComponents, hm, hs, twoLabelLists, hA, hB]
    · have hm := reachesRightSdiffEndpoint_of_right_sdiff G A B hB hA
      have hs := twoLabel_admissible_eq_one_of_left_mem_sdiff
        G A B hdeg hσ e hB hA
      simp [flipRightComponents, hm, hs, twoLabelLists, hA, hB]
    · have hs := hσ.label_mem e
      simp [twoLabelLists, hA, hB] at hs
  · exact flipRightComponents_left_injOn G A B hσ.left_injOn
  · exact flipRightComponents_right_injOn G A B hσ.right_injOn

/-- An uncrossed completion rules out mixed endpoint components. -/
theorem not_mixedEndpointComponent_of_uncrossed_admissible
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    {σ : E → Fin 2}
    (hσ : (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ) :
    ¬ HasMixedEndpointComponent G A B := by
  rintro ⟨e, f, heA, heB, hfB, hfA, hef⟩
  have hright : ∀ y, G.rightDegree y ≤ 2 := by
    intro y
    simpa using hσ.rightDegree_le_card y
  exact no_reachable_opposite_sdiff_of_uncrossed_admissible
    G A B hdeg hright hσ heA heB hfB hfA hef

/-- Guarded exact local surplus. The existence guard retains all endpoint
compatibility requirements; the right-degree guard is explicit, so an
unrelated overfull right vertex can never create spurious positive surplus.
The exponent counts the free edge-copy components (cycles and right--right
paths), with isolated vertices contributing no binary choice. -/
theorem twoLabel_surplus_eq
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) :
    twoLabelOriginalCount G A B hdeg -
        twoLabelUncrossedCount G A B hdeg =
      if (∀ y, G.rightDegree y ≤ 2) ∧
          (∃ σ, (twoLabelLists G A B hdeg).IsAdmissible σ) ∧
          HasMixedEndpointComponent G A B
      then 2 ^ freeTwoLabelComponentCount (twoLabelLists G A B hdeg)
      else 0 := by
  classical
  let L := twoLabelLists G A B hdeg
  let K := twoLabelLists G (A ∪ B) (A ∩ B)
    (uncrossed_twoLabel_degree G A B hdeg)
  have hfree : freeTwoLabelComponentCount L = freeTwoLabelComponentCount K :=
    freeTwoLabelComponentCount_eq L K
  by_cases hL : ∃ σ, L.IsAdmissible σ
  · obtain ⟨σ, hσ⟩ := hL
    have hright : ∀ y, G.rightDegree y ≤ 2 := by
      intro y
      simpa using hσ.rightDegree_le_card y
    have hcountL := twoLabel_count_eq_pow_of_admissible L hσ
    by_cases hm : HasMixedEndpointComponent G A B
    · have hK : K.count = 0 := by
        apply (count_eq_zero_iff K).2
        intro τ hτ
        exact not_mixedEndpointComponent_of_uncrossed_admissible
          G A B hdeg hτ hm
      change L.count - K.count = _
      rw [if_pos ⟨hright, ⟨σ, hσ⟩, hm⟩]
      simpa [L, hK] using hcountL
    · have hτ := flipRightComponents_isAdmissible_uncrossed
        G A B hdeg hm hσ
      have hcountK := twoLabel_count_eq_pow_of_admissible K hτ
      change L.count - K.count = _
      rw [hcountL, hcountK, hfree, Nat.sub_self]
      simp [hm]
  · have hzero : L.count = 0 := by
      apply (count_eq_zero_iff L).2
      simpa only [not_exists] using hL
    change L.count - K.count = _
    rw [hzero, Nat.zero_sub]
    simp only [show ¬ (∃ σ, (twoLabelLists G A B hdeg).IsAdmissible σ) from hL,
      false_and, and_false, ite_false]

end BachThesisLean
