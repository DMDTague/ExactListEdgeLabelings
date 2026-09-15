import BachThesisLean.Cubic.TightCutBalance

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Cubic balance across an oriented cut

Counting all edge copies incident with the vertices of `W` from the two shores
produces the manuscript identity

`3 (|X ∩ W| - |Y ∩ W|) = e_X - e_Y`.

We keep it in subtraction-free natural-number form so that it composes cleanly
with the perfect-matching balance from `TightCutBalance`.
-/

/-- All edge copies incident with left vertices of `W` are precisely the
internal copies together with the boundary copies leaving from the left shore. -/
theorem biUnion_cutLeftVertices_eq_inside_union_cutFromLeft
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    (cutLeftVertices W).biUnion G.leftIncident =
      G.cutInsideEdges W ∪ G.cutFromLeft W := by
  classical
  ext e
  constructor
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨x, hxW, hex⟩ := he
    have hleft : G.left e = x := (G.mem_leftIncident x e).1 hex
    have hx : (Sum.inl (G.left e) : X ⊕ Y) ∈ W := by
      simpa [hleft] using (mem_cutLeftVertices W x).1 hxW
    by_cases hy : (Sum.inr (G.right e) : X ⊕ Y) ∈ W
    · exact Finset.mem_union_left _ ((G.mem_cutInsideEdges W e).2 ⟨hx, hy⟩)
    · exact Finset.mem_union_right _ ((G.mem_cutFromLeft W e).2 ⟨hx, hy⟩)
  · intro he
    rw [Finset.mem_union] at he
    rw [Finset.mem_biUnion]
    refine ⟨G.left e, ?_, (G.mem_leftIncident (G.left e) e).2 rfl⟩
    rcases he with he | he
    · exact (mem_cutLeftVertices W (G.left e)).2
        ((G.mem_cutInsideEdges W e).1 he).1
    · exact (mem_cutLeftVertices W (G.left e)).2
        ((G.mem_cutFromLeft W e).1 he).1

/-- Right-shore counterpart of the preceding decomposition. -/
theorem biUnion_cutRightVertices_eq_inside_union_cutFromRight
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    (cutRightVertices W).biUnion G.rightIncident =
      G.cutInsideEdges W ∪ G.cutFromRight W := by
  classical
  ext e
  constructor
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨y, hyW, hey⟩ := he
    have hright : G.right e = y := (G.mem_rightIncident y e).1 hey
    have hy : (Sum.inr (G.right e) : X ⊕ Y) ∈ W := by
      simpa [hright] using (mem_cutRightVertices W y).1 hyW
    by_cases hx : (Sum.inl (G.left e) : X ⊕ Y) ∈ W
    · exact Finset.mem_union_left _ ((G.mem_cutInsideEdges W e).2 ⟨hx, hy⟩)
    · exact Finset.mem_union_right _ ((G.mem_cutFromRight W e).2 ⟨hx, hy⟩)
  · intro he
    rw [Finset.mem_union] at he
    rw [Finset.mem_biUnion]
    refine ⟨G.right e, ?_, (G.mem_rightIncident (G.right e) e).2 rfl⟩
    rcases he with he | he
    · exact (mem_cutRightVertices W (G.right e)).2
        ((G.mem_cutInsideEdges W e).1 he).2
    · exact (mem_cutRightVertices W (G.right e)).2
        ((G.mem_cutFromRight W e).1 he).2

/-- Internal copies and left-oriented boundary copies are disjoint. -/
theorem cutInsideEdges_disjoint_cutFromLeft
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    Disjoint (G.cutInsideEdges W) (G.cutFromLeft W) := by
  rw [Finset.disjoint_left]
  intro e hI hL
  exact ((G.mem_cutFromLeft W e).1 hL).2
    ((G.mem_cutInsideEdges W e).1 hI).2

/-- Internal copies and right-oriented boundary copies are disjoint. -/
theorem cutInsideEdges_disjoint_cutFromRight
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    Disjoint (G.cutInsideEdges W) (G.cutFromRight W) := by
  rw [Finset.disjoint_left]
  intro e hI hR
  exact ((G.mem_cutFromRight W e).1 hR).1
    ((G.mem_cutInsideEdges W e).1 hI).1

/-- Cubic degree balance across the two oriented pieces of a vertex cut. -/
theorem IsCubic.cut_orientation_balance
    {G : BipartiteMultigraph X Y E} (hG : G.IsCubic)
    (W : Finset (X ⊕ Y)) :
    3 * (cutLeftVertices W).card + (G.cutFromRight W).card =
      3 * (cutRightVertices W).card + (G.cutFromLeft W).card := by
  have hreg := (G.isCubic_iff).1 hG
  have hL := G.card_biUnion_leftIncident_of_regular hreg.1 (cutLeftVertices W)
  have hR := G.card_biUnion_rightIncident_of_regular hreg.2 (cutRightVertices W)
  rw [G.biUnion_cutLeftVertices_eq_inside_union_cutFromLeft W,
    Finset.card_union_of_disjoint (G.cutInsideEdges_disjoint_cutFromLeft W)] at hL
  rw [G.biUnion_cutRightVertices_eq_inside_union_cutFromRight W,
    Finset.card_union_of_disjoint (G.cutInsideEdges_disjoint_cutFromRight W)] at hR
  omega

end BipartiteMultigraph
end BachThesisLean
