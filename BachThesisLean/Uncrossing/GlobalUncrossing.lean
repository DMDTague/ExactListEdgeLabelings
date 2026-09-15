import BachThesisLean.Uncrossing.GlobalPairFlip

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# Global one-step uncrossing monotonicity

The component flip built for the active pair is now applied inside the full
labeling space.  All labels outside `a,b` remain fixed.  Exactness plus
component parity shows that the transformed labeling satisfies the original
support family, while left- and right-incidence injectivity are preserved.
-/

/-- Pointwise list membership after the global component flip. -/
theorem globalPairFlip_label_mem_original
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    (e : E) :
    globalPairFlip G S a b σ e ∈ listsOfSupports S (G.left e) := by
  rw [mem_listsOfSupports]
  have hmem := hσ.label_mem e
  change σ e ∈ listsOfSupports (uncross S a b) (G.left e) at hmem
  rw [mem_listsOfSupports] at hmem
  by_cases hm : reachesRightSdiffGlobal G S a b σ e
  · have heP : e ∈ pairEdges σ a b := hm.1
    rcases (mem_pairEdges σ a b e).1 heP with hea | heb
    · have hU : G.left e ∈ S a ∪ S b := by
        rw [hea, uncross_at_left S hab] at hmem
        exact hmem
      have hB : G.left e ∈ S b := by
        by_contra hnotB
        have hA : G.left e ∈ S a := (Finset.mem_union.mp hU).resolve_right hnotB
        exact (not_reachesRightSdiffGlobal_of_left_sdiff
          G S hab hinc hσ heP hA hnotB) hm
      simpa [globalPairFlip, hm, hea] using hB
    · have hI : G.left e ∈ S a ∩ S b := by
        rw [heb, uncross_at_right S hab] at hmem
        exact hmem
      have hA : G.left e ∈ S a := (Finset.mem_inter.mp hI).1
      simpa [globalPairFlip, hm, heb] using hA
  · by_cases hea : σ e = a
    · have heP : e ∈ pairEdges σ a b :=
        (mem_pairEdges σ a b e).2 (Or.inl hea)
      have hU : G.left e ∈ S a ∪ S b := by
        rw [hea, uncross_at_left S hab] at hmem
        exact hmem
      have hA : G.left e ∈ S a := by
        by_contra hnotA
        have hB : G.left e ∈ S b := (Finset.mem_union.mp hU).resolve_left hnotA
        exact hm (reachesRightSdiffGlobal_of_right_sdiff
          G S a b σ heP hB hnotA)
      simpa [globalPairFlip, hm, hea] using hA
    · by_cases heb : σ e = b
      · have hI : G.left e ∈ S a ∩ S b := by
          rw [heb, uncross_at_right S hab] at hmem
          exact hmem
        have hB : G.left e ∈ S b := (Finset.mem_inter.mp hI).2
        simpa [globalPairFlip, hm, heb] using hB
      · rw [uncross_away S hea heb] at hmem
        simpa [globalPairFlip, hm] using hmem

/-- Equality after the flip forces the same active/inactive status before the
flip. -/
theorem pairEdges_iff_of_globalPairFlip_eq
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) {σ : E → Λ} {e f : E}
    (hflip : globalPairFlip G S a b σ e = globalPairFlip G S a b σ f) :
    e ∈ pairEdges σ a b ↔ f ∈ pairEdges σ a b := by
  rw [mem_pairEdges, mem_pairEdges]
  rw [← globalPairFlip_mem_pair_iff G S hab σ e]
  rw [← globalPairFlip_mem_pair_iff G S hab σ f]
  rw [hflip]

/-- The global component flip preserves injectivity at every left vertex. -/
theorem globalPairFlip_left_injOn
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) {σ : E → Λ}
    (hσ : ∀ x, Set.InjOn σ (G.leftIncident x)) :
    ∀ x, Set.InjOn (globalPairFlip G S a b σ) (G.leftIncident x) := by
  intro x e he f hf hflip
  have hleft : G.left e = G.left f :=
    (G.mem_leftIncident x e).1 he |>.trans
      ((G.mem_leftIncident x f).1 hf).symm
  have hactive := pairEdges_iff_of_globalPairFlip_eq G S hab hflip
  by_cases heP : e ∈ pairEdges σ a b
  · have hfP : f ∈ pairEdges σ a b := hactive.mp heP
    have hmark := reachesRightSdiffGlobal_same_left_iff
      G S a b σ heP hfP hleft
    by_cases hme : reachesRightSdiffGlobal G S a b σ e
    · have hmf : reachesRightSdiffGlobal G S a b σ f := hmark.mp hme
      apply hσ x he hf
      apply (Equiv.swap a b).injective
      simpa [globalPairFlip, hme, hmf] using hflip
    · have hmf : ¬ reachesRightSdiffGlobal G S a b σ f := by
        intro h
        exact hme (hmark.mpr h)
      apply hσ x he hf
      simpa [globalPairFlip, hme, hmf] using hflip
  · have hfP : f ∉ pairEdges σ a b := by
      intro h
      exact heP (hactive.mpr h)
    have hme : ¬ reachesRightSdiffGlobal G S a b σ e := fun h => heP h.1
    have hmf : ¬ reachesRightSdiffGlobal G S a b σ f := fun h => hfP h.1
    apply hσ x he hf
    simpa [globalPairFlip, hme, hmf] using hflip

/-- The global component flip likewise preserves injectivity at every right
vertex. -/
theorem globalPairFlip_right_injOn
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) {σ : E → Λ}
    (hσ : ∀ y, Set.InjOn σ (G.rightIncident y)) :
    ∀ y, Set.InjOn (globalPairFlip G S a b σ) (G.rightIncident y) := by
  intro y e he f hf hflip
  have hright : G.right e = G.right f :=
    (G.mem_rightIncident y e).1 he |>.trans
      ((G.mem_rightIncident y f).1 hf).symm
  have hactive := pairEdges_iff_of_globalPairFlip_eq G S hab hflip
  by_cases heP : e ∈ pairEdges σ a b
  · have hfP : f ∈ pairEdges σ a b := hactive.mp heP
    have hmark := reachesRightSdiffGlobal_same_right_iff
      G S a b σ heP hfP hright
    by_cases hme : reachesRightSdiffGlobal G S a b σ e
    · have hmf : reachesRightSdiffGlobal G S a b σ f := hmark.mp hme
      apply hσ y he hf
      apply (Equiv.swap a b).injective
      simpa [globalPairFlip, hme, hmf] using hflip
    · have hmf : ¬ reachesRightSdiffGlobal G S a b σ f := by
        intro h
        exact hme (hmark.mpr h)
      apply hσ y he hf
      simpa [globalPairFlip, hme, hmf] using hflip
  · have hfP : f ∉ pairEdges σ a b := by
      intro h
      exact heP (hactive.mpr h)
    have hme : ¬ reachesRightSdiffGlobal G S a b σ e := fun h => heP h.1
    have hmf : ¬ reachesRightSdiffGlobal G S a b σ f := fun h => hfP h.1
    apply hσ y he hf
    simpa [globalPairFlip, hme, hmf] using hflip

/-- Every admissible labeling of the uncrossed support family is sent to an
admissible labeling of the original support family. -/
theorem globalPairFlip_isAdmissible_original
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ) :
    (exactListsOfSupports S hS).IsAdmissible (globalPairFlip G S a b σ) := by
  apply isAdmissible_of_label_mem_of_injOn
  · exact globalPairFlip_label_mem_original G S hab hinc hσ
  · exact globalPairFlip_left_injOn G S hab hσ.left_injOn
  · exact globalPairFlip_right_injOn G S hab hσ.right_injOn

/-- The global injection associated with one support uncrossing. -/
noncomputable def globalUncrossedToOriginal
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    (exactListsOfSupports (uncross S a b) hinc).AdmissibleLabeling →
      (exactListsOfSupports S hS).AdmissibleLabeling :=
  fun s => ⟨globalPairFlip G S a b s.1,
    globalPairFlip_isAdmissible_original G S hab hS hinc s.2⟩

/-- The global one-step map is injective because the underlying component flip
is an involution. -/
theorem globalUncrossedToOriginal_injective
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    Function.Injective (globalUncrossedToOriginal G S hab hS hinc) := by
  intro s t hst
  apply Subtype.ext
  apply globalPairFlip_injective G S hab
  exact congrArg Subtype.val hst

/-- Global one-step uncrossing monotonicity: replacing two indexed supports by
their union and intersection cannot increase the exact-list completion count. -/
theorem exactListsOfSupports_uncross_count_le
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b)) :
    (exactListsOfSupports (uncross S a b) hinc).count ≤
      (exactListsOfSupports S hS).count := by
  exact count_le_of_injective
    (exactListsOfSupports (uncross S a b) hinc)
    (exactListsOfSupports S hS)
    (globalUncrossedToOriginal G S hab hS hinc)
    (globalUncrossedToOriginal_injective G S hab hS hinc)

end BachThesisLean
