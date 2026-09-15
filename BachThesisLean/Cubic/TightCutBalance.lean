import BachThesisLean.Cubic.MatchingCovered
import BachThesisLean.Cubic.MatchingCardinality

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Oriented edge-cut balance

For a vertex set `W`, split the edge boundary into the copies directed from a
left vertex of `W` to a right vertex outside `W` and the copies with the
opposite orientation.  The manuscript's tight-cut decomposition begins by
showing that a tight cut in a cubic matching-covered bipartite graph has only
one of these orientations and exactly three edge copies.
-/

noncomputable def cutLeftVertices (W : Finset (X ⊕ Y)) : Finset X :=
  Finset.univ.filter (fun x => (Sum.inl x : X ⊕ Y) ∈ W)

noncomputable def cutRightVertices (W : Finset (X ⊕ Y)) : Finset Y :=
  Finset.univ.filter (fun y => (Sum.inr y : X ⊕ Y) ∈ W)

noncomputable def cutInsideEdges (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) : Finset E :=
  Finset.univ.filter (fun e =>
    (Sum.inl (G.left e) : X ⊕ Y) ∈ W ∧
      (Sum.inr (G.right e) : X ⊕ Y) ∈ W)

noncomputable def cutFromLeft (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) : Finset E :=
  Finset.univ.filter (fun e =>
    (Sum.inl (G.left e) : X ⊕ Y) ∈ W ∧
      (Sum.inr (G.right e) : X ⊕ Y) ∉ W)

noncomputable def cutFromRight (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) : Finset E :=
  Finset.univ.filter (fun e =>
    (Sum.inl (G.left e) : X ⊕ Y) ∉ W ∧
      (Sum.inr (G.right e) : X ⊕ Y) ∈ W)

noncomputable def matchingLeftInside (G : BipartiteMultigraph X Y E)
    (P : Finset E) (W : Finset (X ⊕ Y)) : Finset E :=
  P.filter (fun e => (Sum.inl (G.left e) : X ⊕ Y) ∈ W)

noncomputable def matchingRightInside (G : BipartiteMultigraph X Y E)
    (P : Finset E) (W : Finset (X ⊕ Y)) : Finset E :=
  P.filter (fun e => (Sum.inr (G.right e) : X ⊕ Y) ∈ W)

@[simp] theorem mem_cutLeftVertices (W : Finset (X ⊕ Y)) (x : X) :
    x ∈ cutLeftVertices W ↔ (Sum.inl x : X ⊕ Y) ∈ W := by
  simp [cutLeftVertices]

@[simp] theorem mem_cutRightVertices (W : Finset (X ⊕ Y)) (y : Y) :
    y ∈ cutRightVertices W ↔ (Sum.inr y : X ⊕ Y) ∈ W := by
  simp [cutRightVertices]

@[simp] theorem mem_cutInsideEdges (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) (e : E) :
    e ∈ G.cutInsideEdges W ↔
      (Sum.inl (G.left e) : X ⊕ Y) ∈ W ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∈ W := by
  simp [cutInsideEdges]

@[simp] theorem mem_cutFromLeft (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) (e : E) :
    e ∈ G.cutFromLeft W ↔
      (Sum.inl (G.left e) : X ⊕ Y) ∈ W ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∉ W := by
  simp [cutFromLeft]

@[simp] theorem mem_cutFromRight (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) (e : E) :
    e ∈ G.cutFromRight W ↔
      (Sum.inl (G.left e) : X ⊕ Y) ∉ W ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∈ W := by
  simp [cutFromRight]

@[simp] theorem mem_matchingLeftInside (G : BipartiteMultigraph X Y E)
    (P : Finset E) (W : Finset (X ⊕ Y)) (e : E) :
    e ∈ G.matchingLeftInside P W ↔
      e ∈ P ∧ (Sum.inl (G.left e) : X ⊕ Y) ∈ W := by
  simp [matchingLeftInside]

@[simp] theorem mem_matchingRightInside (G : BipartiteMultigraph X Y E)
    (P : Finset E) (W : Finset (X ⊕ Y)) (e : E) :
    e ∈ G.matchingRightInside P W ↔
      e ∈ P ∧ (Sum.inr (G.right e) : X ⊕ Y) ∈ W := by
  simp [matchingRightInside]

/-- The ordinary edge cut is the disjoint union of its two orientations. -/
theorem edgeCut_eq_oriented_union (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) :
    G.edgeCut W = G.cutFromLeft W ∪ G.cutFromRight W := by
  ext e
  simp [edgeCut]

/-- The two oriented pieces of a bipartite cut are disjoint. -/
theorem cutFromLeft_disjoint_cutFromRight
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    Disjoint (G.cutFromLeft W) (G.cutFromRight W) := by
  rw [Finset.disjoint_left]
  intro e hL hR
  have hL' := (G.mem_cutFromLeft W e).1 hL
  have hR' := (G.mem_cutFromRight W e).1 hR
  exact hR'.1 hL'.1

/-- A perfect matching contributes one selected edge copy for each left vertex
of `W`. -/
theorem IsPerfectMatching.card_matchingLeftInside
    {G : BipartiteMultigraph X Y E} {P : Finset E}
    (hP : G.IsPerfectMatching P) (W : Finset (X ⊕ Y)) :
    (G.matchingLeftInside P W).card = (cutLeftVertices W).card := by
  classical
  refine Finset.card_nbij G.left ?_ ?_ ?_
  · intro e he
    exact (mem_cutLeftVertices W (G.left e)).2
      ((G.mem_matchingLeftInside P W e).1 he).2
  · intro e he f hf hef
    have heP := ((G.mem_matchingLeftInside P W e).1 he).1
    have hfP := ((G.mem_matchingLeftInside P W f).1 hf).1
    exact (G.isMatching_iff P).1 hP.isMatching e heP f hfP (.inl (G.left e))
      rfl (by simpa [Incident] using hef.symm)
  · intro x hx
    obtain ⟨e, he, _⟩ := hP.existsUnique_incident (.inl x)
    have hleft : G.left e = x := by simpa [Incident] using he.2
    refine ⟨e, ?_, hleft⟩
    exact (G.mem_matchingLeftInside P W e).2
      ⟨he.1, by simpa [hleft] using (mem_cutLeftVertices W x).1 hx⟩

/-- Right-shore version of `card_matchingLeftInside`. -/
theorem IsPerfectMatching.card_matchingRightInside
    {G : BipartiteMultigraph X Y E} {P : Finset E}
    (hP : G.IsPerfectMatching P) (W : Finset (X ⊕ Y)) :
    (G.matchingRightInside P W).card = (cutRightVertices W).card := by
  classical
  refine Finset.card_nbij G.right ?_ ?_ ?_
  · intro e he
    exact (mem_cutRightVertices W (G.right e)).2
      ((G.mem_matchingRightInside P W e).1 he).2
  · intro e he f hf hef
    have heP := ((G.mem_matchingRightInside P W e).1 he).1
    have hfP := ((G.mem_matchingRightInside P W f).1 hf).1
    exact (G.isMatching_iff P).1 hP.isMatching e heP f hfP (.inr (G.right e))
      rfl (by simpa [Incident] using hef.symm)
  · intro y hy
    obtain ⟨e, he, _⟩ := hP.existsUnique_incident (.inr y)
    have hright : G.right e = y := by simpa [Incident] using he.2
    refine ⟨e, ?_, hright⟩
    exact (G.mem_matchingRightInside P W e).2
      ⟨he.1, by simpa [hright] using (mem_cutRightVertices W y).1 hy⟩

/-- Selected edges whose left endpoint lies in `W` split into internal edges
and the left-to-right oriented boundary. -/
theorem matchingLeftInside_eq_inside_union_cut
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    (W : Finset (X ⊕ Y)) :
    G.matchingLeftInside P W =
      (P ∩ G.cutInsideEdges W) ∪ (P ∩ G.cutFromLeft W) := by
  ext e
  simp only [mem_matchingLeftInside, Finset.mem_union, Finset.mem_inter,
    mem_cutInsideEdges, mem_cutFromLeft]
  tauto

/-- Selected edges whose right endpoint lies in `W` split into internal edges
and the right-to-left oriented boundary. -/
theorem matchingRightInside_eq_inside_union_cut
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    (W : Finset (X ⊕ Y)) :
    G.matchingRightInside P W =
      (P ∩ G.cutInsideEdges W) ∪ (P ∩ G.cutFromRight W) := by
  ext e
  simp only [mem_matchingRightInside, Finset.mem_union, Finset.mem_inter,
    mem_cutInsideEdges, mem_cutFromRight]
  tauto

/-- The two pieces in the left selected-edge decomposition are disjoint. -/
theorem matching_inside_disjoint_cutFromLeft
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    (W : Finset (X ⊕ Y)) :
    Disjoint (P ∩ G.cutInsideEdges W) (P ∩ G.cutFromLeft W) := by
  rw [Finset.disjoint_left]
  intro e hI hL
  have hI' := Finset.mem_inter.mp hI
  have hL' := Finset.mem_inter.mp hL
  exact ((G.mem_cutFromLeft W e).1 hL'.2).2
    ((G.mem_cutInsideEdges W e).1 hI'.2).2

/-- The two pieces in the right selected-edge decomposition are disjoint. -/
theorem matching_inside_disjoint_cutFromRight
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    (W : Finset (X ⊕ Y)) :
    Disjoint (P ∩ G.cutInsideEdges W) (P ∩ G.cutFromRight W) := by
  rw [Finset.disjoint_left]
  intro e hI hR
  have hI' := Finset.mem_inter.mp hI
  have hR' := Finset.mem_inter.mp hR
  exact ((G.mem_cutFromRight W e).1 hR'.2).1
    ((G.mem_cutInsideEdges W e).1 hI'.2).1

/-- Matching degree balance across an oriented cut. -/
theorem IsPerfectMatching.cut_orientation_balance
    {G : BipartiteMultigraph X Y E} {P : Finset E}
    (hP : G.IsPerfectMatching P) (W : Finset (X ⊕ Y)) :
    (cutLeftVertices W).card + (P ∩ G.cutFromRight W).card =
      (cutRightVertices W).card + (P ∩ G.cutFromLeft W).card := by
  have hL := hP.card_matchingLeftInside W
  have hR := hP.card_matchingRightInside W
  rw [G.matchingLeftInside_eq_inside_union_cut P W,
    Finset.card_union_of_disjoint (G.matching_inside_disjoint_cutFromLeft P W)] at hL
  rw [G.matchingRightInside_eq_inside_union_cut P W,
    Finset.card_union_of_disjoint (G.matching_inside_disjoint_cutFromRight P W)] at hR
  omega

end BipartiteMultigraph
end BachThesisLean
