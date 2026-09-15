import BachThesisLean.Cubic.TightCutBalance

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Orientation of tight cuts

This is the first structural step in the manuscript's tight-cut
correspondence.  Tightness plus matching-coveredness already forbids a
boundary from containing edge copies in both bipartite orientations.  For a
three-edge cut, the two orientation counts are therefore `(3,0)` or `(0,3)`.

The proof is deliberately edge-copy based, so repeated boundary endpoints and
parallel edges require no special cases.
-/

/-- The selected part of a cut is the union of its two selected oriented
pieces. -/
theorem matching_edgeCut_eq_oriented_union
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    (W : Finset (X ⊕ Y)) :
    P ∩ G.edgeCut W =
      (P ∩ G.cutFromLeft W) ∪ (P ∩ G.cutFromRight W) := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_union]
  rw [G.edgeCut_eq_oriented_union W]
  simp only [Finset.mem_union]
  tauto

/-- Intersecting with a selected edge set preserves disjointness of the two
cut orientations. -/
theorem matching_oriented_cut_disjoint
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    (W : Finset (X ⊕ Y)) :
    Disjoint (P ∩ G.cutFromLeft W) (P ∩ G.cutFromRight W) := by
  have hd := G.cutFromLeft_disjoint_cutFromRight W
  rw [Finset.disjoint_left] at hd ⊢
  intro e hL hR
  exact hd (Finset.mem_inter.mp hL).2 (Finset.mem_inter.mp hR).2

/-- Tightness says that the two selected orientation counts add to one. -/
theorem IsTightCut.selected_oriented_card_add
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (P : Finset E)
    (hP : G.IsPerfectMatching P) :
    (P ∩ G.cutFromLeft W).card +
      (P ∩ G.cutFromRight W).card = 1 := by
  have h := hT P hP
  rw [G.matching_edgeCut_eq_oriented_union P W,
    Finset.card_union_of_disjoint (G.matching_oriented_cut_disjoint P W)] at h
  exact h

/-- If a tight cut has a left-to-right boundary edge and the graph is
matching-covered, the left shore inside the cut has exactly one more vertex
than the right shore inside the cut. -/
theorem IsTightCut.left_card_eq_right_card_add_one_of_mem_cutFromLeft
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hMC : G.IsMatchingCovered)
    {e : E} (he : e ∈ G.cutFromLeft W) :
    (cutLeftVertices W).card = (cutRightVertices W).card + 1 := by
  obtain ⟨P, hP, heP⟩ := hMC.2.2 e
  have hpos : 0 < (P ∩ G.cutFromLeft W).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨heP, he⟩⟩
  have hsum := hT.selected_oriented_card_add P hP
  have hbal := hP.cut_orientation_balance W
  omega

/-- Symmetric shore-count consequence of a right-to-left boundary edge. -/
theorem IsTightCut.right_card_eq_left_card_add_one_of_mem_cutFromRight
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hMC : G.IsMatchingCovered)
    {e : E} (he : e ∈ G.cutFromRight W) :
    (cutRightVertices W).card = (cutLeftVertices W).card + 1 := by
  obtain ⟨P, hP, heP⟩ := hMC.2.2 e
  have hpos : 0 < (P ∩ G.cutFromRight W).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨heP, he⟩⟩
  have hsum := hT.selected_oriented_card_add P hP
  have hbal := hP.cut_orientation_balance W
  omega

/-- A tight cut in a matching-covered bipartite multigraph cannot contain
boundary edge copies of both orientations.  No simplicity assumption is used. -/
theorem IsTightCut.oriented
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hMC : G.IsMatchingCovered) :
    G.cutFromLeft W = ∅ ∨ G.cutFromRight W = ∅ := by
  by_cases hL : G.cutFromLeft W = ∅
  · exact Or.inl hL
  by_cases hR : G.cutFromRight W = ∅
  · exact Or.inr hR
  have hLn : (G.cutFromLeft W).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hL
  have hRn : (G.cutFromRight W).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hR
  obtain ⟨eL, heL⟩ := hLn
  obtain ⟨eR, heR⟩ := hRn
  have hleft :=
    hT.left_card_eq_right_card_add_one_of_mem_cutFromLeft hMC heL
  have hright :=
    hT.right_card_eq_left_card_add_one_of_mem_cutFromRight hMC heR
  omega

/-- Manuscript orientation dichotomy for a three-edge tight cut: all three
edge copies point through the cut in the same bipartite orientation. -/
theorem IsTightCut.oriented_three_of_edgeCut_card_three
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hMC : G.IsMatchingCovered)
    (hcard : (G.edgeCut W).card = 3) :
    ((G.cutFromLeft W).card = 3 ∧ (G.cutFromRight W).card = 0) ∨
      ((G.cutFromLeft W).card = 0 ∧ (G.cutFromRight W).card = 3) := by
  have hsum :
      (G.cutFromLeft W).card + (G.cutFromRight W).card = 3 := by
    rw [G.edgeCut_eq_oriented_union W,
      Finset.card_union_of_disjoint (G.cutFromLeft_disjoint_cutFromRight W)] at hcard
    exact hcard
  rcases hT.oriented hMC with hL | hR
  · right
    have hL0 : (G.cutFromLeft W).card = 0 := by simp [hL]
    exact ⟨hL0, by omega⟩
  · left
    have hR0 : (G.cutFromRight W).card = 0 := by simp [hR]
    exact ⟨by omega, hR0⟩

end BipartiteMultigraph
end BachThesisLean
