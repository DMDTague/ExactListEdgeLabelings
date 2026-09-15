import BachThesisLean.Cubic.TightCutCubic
import BachThesisLean.Cubic.TightCutOrientation

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Tight cuts of connected cubic bipartite multigraphs have size three

This closes the numerical first step of the manuscript's tight-cut
correspondence.  Tightness provides a selected boundary edge, matching-covered
extension forces a unique orientation, and cubic degree balance then forces
exactly three boundary edge copies.  No simplicity assumption is used.
-/

/-- A tight cut in a cubic graph is nonempty because cubicity supplies a
perfect matching and tightness makes that matching use one cut edge. -/
theorem IsTightCut.edgeCut_nonempty_of_cubic
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hG : G.IsCubic) :
    (G.edgeCut W).Nonempty := by
  classical
  let P : G.PerfectMatching := Classical.choice (G.exists_perfectMatching_of_cubic hG)
  have hcard : (P.val ∩ G.edgeCut W).card = 1 := hT P.val P.property
  have hpos : 0 < (G.edgeCut W).card := by
    have hle := Finset.card_le_card (Finset.inter_subset_right :
      P.val ∩ G.edgeCut W ⊆ G.edgeCut W)
    rw [hcard] at hle
    omega
  exact Finset.card_pos.mp hpos

/-- Every nontrivial tight cut of a connected cubic bipartite multigraph has
exactly three edge copies.  The proof itself does not need nontriviality; that
hypothesis belongs to the contraction theorem that follows. -/
theorem IsTightCut.edgeCut_card_eq_three_of_connected_cubic
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic) :
    (G.edgeCut W).card = 3 := by
  classical
  have hMC : G.IsMatchingCovered := G.isMatchingCovered_of_connected_cubic hconn hG
  have hcut := hT.edgeCut_nonempty_of_cubic hG
  have hbal := hG.cut_orientation_balance W
  rcases hT.oriented hMC with hL | hR
  · obtain ⟨e, heCut⟩ := hcut
    have heR : e ∈ G.cutFromRight W := by
      rw [G.edgeCut_eq_oriented_union W] at heCut
      simpa [hL] using heCut
    have hshore := hT.right_card_eq_left_card_add_one_of_mem_cutFromRight hMC heR
    have hLcard : (G.cutFromLeft W).card = 0 := by simp [hL]
    rw [hLcard] at hbal
    have hRcard : (G.cutFromRight W).card = 3 := by omega
    rw [G.edgeCut_eq_oriented_union W, hL]
    simpa [hRcard]
  · obtain ⟨e, heCut⟩ := hcut
    have heL : e ∈ G.cutFromLeft W := by
      rw [G.edgeCut_eq_oriented_union W] at heCut
      simpa [hR] using heCut
    have hshore := hT.left_card_eq_right_card_add_one_of_mem_cutFromLeft hMC heL
    have hRcard0 : (G.cutFromRight W).card = 0 := by simp [hR]
    rw [hRcard0] at hbal
    have hLcard : (G.cutFromLeft W).card = 3 := by omega
    rw [G.edgeCut_eq_oriented_union W, hR]
    simpa [hLcard]

/-- Full edge-copy orientation dichotomy for a connected cubic tight cut. -/
theorem IsTightCut.oriented_three_of_connected_cubic
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic) :
    ((G.cutFromLeft W).card = 3 ∧ (G.cutFromRight W).card = 0) ∨
      ((G.cutFromLeft W).card = 0 ∧ (G.cutFromRight W).card = 3) := by
  have hMC : G.IsMatchingCovered := G.isMatchingCovered_of_connected_cubic hconn hG
  exact hT.oriented_three_of_edgeCut_card_three hMC
    (hT.edgeCut_card_eq_three_of_connected_cubic hconn hG)

end BipartiteMultigraph
end BachThesisLean
