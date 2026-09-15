import BachThesisLean.Uncrossing.FibreComponents

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq E]

/-!
# Canonical component flip

When all right degrees are at most two, an admissible uncrossed labeling can
be converted to an admissible original labeling by swapping the two colors on
every edge-copy line-graph component that contains a `B \ A` left endpoint.
The path-parity obstruction proved earlier guarantees that such a component
cannot also contain an `A \ B` endpoint.
-/

/-- Every element of `Fin 2` is one of the two canonical labels. -/
theorem finTwo_eq_zero_or_one_flip (c : Fin 2) : c = 0 ∨ c = 1 := by
  by_cases h0 : c.val = 0
  · left
    apply Fin.ext
    exact h0
  · right
    apply Fin.ext
    omega

/-- Swap the two labels on components marked by `reachesRightSdiffEndpoint`.
The marking depends only on the graph and supports, not on the labeling. -/
noncomputable def flipRightComponents
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (σ : E → Fin 2) : E → Fin 2 := by
  classical
  exact fun e =>
    if reachesRightSdiffEndpoint G A B e then
      Equiv.swap (0 : Fin 2) 1 (σ e)
    else σ e

/-- Componentwise flipping is injective on the space of all edge labelings. -/
theorem flipRightComponents_injective
    (G : BipartiteMultigraph X Y E) (A B : Finset X) :
    Function.Injective (flipRightComponents G A B) := by
  intro σ τ hστ
  funext e
  by_cases he : reachesRightSdiffEndpoint G A B e
  · apply (Equiv.swap (0 : Fin 2) 1).injective
    have heq := congrFun hστ e
    simpa [flipRightComponents, he] using heq
  · have heq := congrFun hστ e
    simpa [flipRightComponents, he] using heq

/-- Flipping preserves injectivity on every left incidence set because the
component mark is constant among edges sharing a left endpoint. -/
theorem flipRightComponents_left_injOn
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    {σ : E → Fin 2}
    (hσ : ∀ x, Set.InjOn σ (G.leftIncident x)) :
    ∀ x, Set.InjOn (flipRightComponents G A B σ) (G.leftIncident x) := by
  intro x e he f hf hflip
  have hleft : G.left e = G.left f :=
    (G.mem_leftIncident x e).1 he |>.trans
      ((G.mem_leftIncident x f).1 hf).symm
  have hmark := reachesRightSdiffEndpoint_same_left_iff G A B hleft
  by_cases hme : reachesRightSdiffEndpoint G A B e
  · have hmf : reachesRightSdiffEndpoint G A B f := hmark.mp hme
    apply hσ x he hf
    apply (Equiv.swap (0 : Fin 2) 1).injective
    simpa [flipRightComponents, hme, hmf] using hflip
  · have hmf : ¬ reachesRightSdiffEndpoint G A B f := by
      intro hfmark
      exact hme (hmark.mpr hfmark)
    apply hσ x he hf
    simpa [flipRightComponents, hme, hmf] using hflip

/-- Flipping likewise preserves injectivity on every right incidence set. -/
theorem flipRightComponents_right_injOn
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    {σ : E → Fin 2}
    (hσ : ∀ y, Set.InjOn σ (G.rightIncident y)) :
    ∀ y, Set.InjOn (flipRightComponents G A B σ) (G.rightIncident y) := by
  intro y e he f hf hflip
  have hright : G.right e = G.right f :=
    (G.mem_rightIncident y e).1 he |>.trans
      ((G.mem_rightIncident y f).1 hf).symm
  have hmark := reachesRightSdiffEndpoint_same_right_iff G A B hright
  by_cases hme : reachesRightSdiffEndpoint G A B e
  · have hmf : reachesRightSdiffEndpoint G A B f := hmark.mp hme
    apply hσ y he hf
    apply (Equiv.swap (0 : Fin 2) 1).injective
    simpa [flipRightComponents, hme, hmf] using hflip
  · have hmf : ¬ reachesRightSdiffEndpoint G A B f := by
      intro hfmark
      exact hme (hmark.mpr hfmark)
    apply hσ y he hf
    simpa [flipRightComponents, hme, hmf] using hflip

/-- In the degree-two branch, the canonical component flip sends every
admissible uncrossed labeling to an admissible original labeling. -/
theorem flipRightComponents_isAdmissible_original
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {σ : E → Fin 2}
    (hσ : (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ) :
    (twoLabelLists G A B hdeg).IsAdmissible
      (flipRightComponents G A B σ) := by
  apply isAdmissible_of_label_mem_of_injOn
  · intro e
    by_cases hA : G.left e ∈ A <;> by_cases hB : G.left e ∈ B
    · rcases finTwo_eq_zero_or_one_flip (flipRightComponents G A B σ e) with h0 | h1
      · rw [h0]
        exact (zero_mem_twoLabelLists_labels G A B hdeg (G.left e)).2 hA
      · rw [h1]
        exact (one_mem_twoLabelLists_labels G A B hdeg (G.left e)).2 hB
    · have hmark := not_reachesRightSdiffEndpoint_of_left_sdiff
        G A B hdeg hright hσ hA hB
      have hσ0 := uncrossed_admissible_eq_zero_of_left_mem_sdiff_left
        G A B hdeg hσ e hA hB
      have hflip0 : flipRightComponents G A B σ e = 0 := by
        simp [flipRightComponents, hmark, hσ0]
      rw [hflip0]
      exact (zero_mem_twoLabelLists_labels G A B hdeg (G.left e)).2 hA
    · have hmark := reachesRightSdiffEndpoint_of_right_sdiff G A B hB hA
      have hσ0 := uncrossed_admissible_eq_zero_of_left_mem_sdiff_right
        G A B hdeg hσ e hB hA
      have hflip1 : flipRightComponents G A B σ e = 1 := by
        simp [flipRightComponents, hmark, hσ0]
      rw [hflip1]
      exact (one_mem_twoLabelLists_labels G A B hdeg (G.left e)).2 hB
    · exfalso
      have hzero : G.leftDegree (G.left e) = 0 := by
        simpa [hA, hB] using hdeg (G.left e)
      have heinc : e ∈ G.leftIncident (G.left e) :=
        (G.mem_leftIncident (G.left e) e).2 rfl
      have hpos : 0 < G.leftDegree (G.left e) := by
        rw [leftDegree]
        exact Finset.card_pos.mpr ⟨e, heinc⟩
      omega
  · exact flipRightComponents_left_injOn G A B hσ.left_injOn
  · exact flipRightComponents_right_injOn G A B hσ.right_injOn

/-- The canonical injection from the uncrossed completion set into the
original completion set in the max-degree-two branch. -/
noncomputable def uncrossedToOriginal
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2) :
    (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).AdmissibleLabeling →
    (twoLabelLists G A B hdeg).AdmissibleLabeling :=
  fun s => ⟨flipRightComponents G A B s.1,
    flipRightComponents_isAdmissible_original
      G A B hdeg hright s.2⟩

/-- The canonical component-flip map is injective. -/
theorem uncrossedToOriginal_injective
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2) :
    Function.Injective (uncrossedToOriginal G A B hdeg hright) := by
  intro s t hst
  apply Subtype.ext
  apply flipRightComponents_injective G A B
  exact congrArg Subtype.val hst

/-- Degree-at-most-two branch of the manuscript's local two-label
uncrossing inequality. -/
theorem twoLabel_local_of_rightDegree_le_two
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2) :
    twoLabelUncrossedCount G A B hdeg ≤ twoLabelOriginalCount G A B hdeg := by
  unfold twoLabelUncrossedCount twoLabelOriginalCount
  exact count_le_of_injective
    (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg))
    (twoLabelLists G A B hdeg)
    (uncrossedToOriginal G A B hdeg hright)
    (uncrossedToOriginal_injective G A B hdeg hright)

/-- The manuscript's local two-label uncrossing lemma. The proof splits into
its palette-obstruction case and the degree-at-most-two component-flip case. -/
theorem twoLabel_local
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) :
    twoLabelUncrossedCount G A B hdeg ≤ twoLabelOriginalCount G A B hdeg := by
  classical
  by_cases hhigh : ∃ y : Y, 3 ≤ G.rightDegree y
  · obtain ⟨y, hy⟩ := hhigh
    exact twoLabel_local_of_rightDegree_ge_three G A B hdeg y hy
  · apply twoLabel_local_of_rightDegree_le_two G A B hdeg
    intro y
    have hnot : ¬ 3 ≤ G.rightDegree y := by
      intro hy
      exact hhigh ⟨y, hy⟩
    omega

end BachThesisLean
