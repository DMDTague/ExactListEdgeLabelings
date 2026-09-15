import BachThesisLean.Cubic.FiveVertexSquareCoverage
import BachThesisLean.Cubic.SquareFrameSupport
import BachThesisLean.Cubic.SquareBadPair

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Eliminating the five-vertex-per-shore minimal counterexample

The global five-shore double count supplies at least five unordered left pairs
that index displayed squares.  For a fixed bad edge pair, every displayed
square contains exactly one marked copy.  Reading square membership from
endpoints assigns each indexed left pair to one of the two marked edges, while
a fixed edge can cover at most two indexed pairs.  Hence at most four indexed
squares can be covered, contradicting the lower bound of five.
-/

/-- A square frame together with the unordered left pair that its two rows
represent. -/
structure IndexedSquareFrame
    (G : BipartiteMultigraph X Y E) (S : Finset X) where
  frame : SquareFrame G
  leftSupport :
    ({frame.leftVertex false, frame.leftVertex true} : Finset X) = S
  indexed : S ∈ G.squareLeftPairs

namespace SquareFrame

/-- Any left/right corner chosen from a displayed square determines an occupied
cell, hence an actual adjacency. -/
theorem right_mem_rightNeighborSet_of_mem_support
    (Q : SquareFrame G) {x : X} {y : Y}
    (hx : x ∈ ({Q.leftVertex false, Q.leftVertex true} : Finset X))
    (hy : y ∈ ({Q.rightVertex false, Q.rightVertex true} : Finset Y)) :
    y ∈ G.rightNeighborSet x := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · subst x
      subst y
      apply (G.mem_rightNeighborSet (Q.leftVertex false)
        (Q.rightVertex false)).2
      exact ⟨Q.square false false,
        (G.mem_leftIncident (Q.leftVertex false) (Q.square false false)).2
          (Q.square_left false false),
        Q.square_right false false⟩
    · subst x
      subst y
      apply (G.mem_rightNeighborSet (Q.leftVertex false)
        (Q.rightVertex true)).2
      exact ⟨Q.square false true,
        (G.mem_leftIncident (Q.leftVertex false) (Q.square false true)).2
          (Q.square_left false true),
        Q.square_right false true⟩
  · rcases hy with hy | hy
    · subst x
      subst y
      apply (G.mem_rightNeighborSet (Q.leftVertex true)
        (Q.rightVertex false)).2
      exact ⟨Q.square true false,
        (G.mem_leftIncident (Q.leftVertex true) (Q.square true false)).2
          (Q.square_left true false),
        Q.square_right true false⟩
    · subst x
      subst y
      apply (G.mem_rightNeighborSet (Q.leftVertex true)
        (Q.rightVertex true)).2
      exact ⟨Q.square true true,
        (G.mem_leftIncident (Q.leftVertex true) (Q.square true true)).2
          (Q.square_left true true),
        Q.square_right true true⟩

end SquareFrame

/-- Every left pair counted by `squareLeftPairs` has a displayed square frame
whose two left rows are exactly that unordered pair.  The result is
proposition-valued so the finite `card_eq_two` witnesses can be unpacked
without eliminating proof data into a structure. -/
theorem exists_indexedSquareFrameOfSquareLeftPair
    (G : BipartiteMultigraph X Y E)
    (hsimple : G.IsSimple) (hG : G.IsCubic)
    {S : Finset X} (hS : S ∈ G.squareLeftPairs) :
    ∃ W : IndexedSquareFrame G S, True := by
  classical
  have hScard : S.card = 2 := (G.mem_squareLeftPairs S).1 hS |>.1
  have hcommon : (G.pairCommonRightSet S).card = 2 :=
    (G.mem_squareLeftPairs S).1 hS |>.2
  obtain ⟨x0, x1, hx, hpair⟩ := Finset.card_eq_two.mp hScard
  subst S
  rw [G.pairCommonRightSet_pair x0 x1] at hcommon
  obtain ⟨y0, y1, hy, hset⟩ := Finset.card_eq_two.mp hcommon
  have hy0 : y0 ∈ G.commonRightSet x0 x1 := by simp [hset]
  have hy1 : y1 ∈ G.commonRightSet x0 x1 := by simp [hset]
  have h0 := (G.mem_commonRightSet x0 x1 y0).1 hy0
  have h1 := (G.mem_commonRightSet x0 x1 y1).1 hy1
  let C : SquareCorners G :=
    G.squareCornersOfCommonNeighbors x0 x1 hx y0 y1 hy
      h0.1 h1.1 h0.2 h1.2
  let Q : SquareFrame G := C.toSquareFrame hsimple hG
  refine ⟨{
      frame := Q
      leftSupport := ?_
      indexed := hS }, trivial⟩
  change ({C.leftVertex false, C.leftVertex true} : Finset X) = {x0, x1}
  simp [C, squareCornersOfCommonNeighbors]

namespace IndexedSquareFrame

/-- If an edge lies on the represented displayed square, then the represented
left pair belongs to that edge's endpoint-defined coverage set. -/
theorem mem_squareLeftPairsAtEdge_of_not_outside
    {S : Finset X} (W : IndexedSquareFrame G S)
    (hsimple : G.IsSimple) (e : E)
    (he : ¬ W.frame.OutsideSquare e) :
    S ∈ G.squareLeftPairsAtEdge e := by
  have hends :=
    (SquareFrame.not_outsideSquare_iff_endpoints W.frame hsimple e).1 he
  apply (G.mem_squareLeftPairsAtEdge e S).2
  refine ⟨W.indexed, ?_, ?_⟩
  · rw [← W.leftSupport]
    exact hends.1
  · intro x hxS
    have hxRows :
        x ∈ ({W.frame.leftVertex false, W.frame.leftVertex true} : Finset X) := by
      rw [W.leftSupport]
      exact hxS
    apply (G.mem_leftNeighborSet_iff_mem_rightNeighborSet x (G.right e)).2
    exact W.frame.right_mem_rightNeighborSet_of_mem_support hxRows hends.2

end IndexedSquareFrame

namespace IsMinimalEEPCounterexample

/-- A minimum EEP counterexample cannot have only five vertices on each shore. -/
theorem six_le_card_left (hmin : G.IsMinimalEEPCounterexample) :
    6 ≤ Fintype.card X := by
  classical
  by_contra hsix
  have hlt : Fintype.card X < 6 := Nat.lt_of_not_ge hsix
  have hX : Fintype.card X = 5 := by
    have hfive := hmin.five_le_card_left
    omega
  have hsimple : G.IsSimple :=
    hmin.isBrace.isSimple_of_three_le_card_left hmin.cubic (by omega)
  obtain ⟨e, f, hef, hbad⟩ :=
    SquareFrame.exists_badPair_of_not_hasEEP hmin.failsEEP
  let A : Finset (Finset X) := G.squareLeftPairsAtEdge e
  let B : Finset (Finset X) := G.squareLeftPairsAtEdge f
  have hcover : G.squareLeftPairs ⊆ A ∪ B := by
    intro S hS
    obtain ⟨W, -⟩ :=
      G.exists_indexedSquareFrameOfSquareLeftPair hsimple hmin.cubic hS
    have hmeet :=
      SquareFrame.IsMinimalEEPCounterexample.badPair_meets_square_exactly_one
        hmin W.frame hef hbad
    rcases hmeet with he | hf
    · have hSe : S ∈ G.squareLeftPairsAtEdge e :=
        W.mem_squareLeftPairsAtEdge_of_not_outside hsimple e he.1
      exact Finset.mem_union_left B (by simpa [A] using hSe)
    · have hSf : S ∈ G.squareLeftPairsAtEdge f :=
        W.mem_squareLeftPairsAtEdge_of_not_outside hsimple f hf.2
      exact Finset.mem_union_right A (by simpa [B] using hSf)
  have hfiveSquares : 5 ≤ G.squareLeftPairs.card :=
    hmin.isBrace.five_le_squareLeftPairs_card hmin.cubic hX
  have hcoverCard : G.squareLeftPairs.card ≤ (A ∪ B).card :=
    Finset.card_le_card hcover
  have hunion : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have hA : A.card ≤ 2 := by
    simpa [A] using G.squareLeftPairsAtEdge_card_le_two hsimple hmin.cubic e
  have hB : B.card ≤ 2 := by
    simpa [B] using G.squareLeftPairsAtEdge_card_le_two hsimple hmin.cubic f
  omega

/-- The same six-vertex lower bound holds on the right shore. -/
theorem six_le_card_right (hmin : G.IsMinimalEEPCounterexample) :
    6 ≤ Fintype.card Y := by
  rw [← G.card_left_eq_card_right_of_cubic hmin.cubic]
  exact hmin.six_le_card_left

/-- Thus a minimum EEP counterexample has at least twelve vertices. -/
theorem twelve_le_vertexCard (hmin : G.IsMinimalEEPCounterexample) :
    12 ≤ G.vertexCard := by
  rw [vertexCard, ← G.card_left_eq_card_right_of_cubic hmin.cubic]
  have hleft := hmin.six_le_card_left
  omega

/-- Thus a minimum EEP counterexample has at least eighteen actual edge
copies. -/
theorem eighteen_le_edgeCard (hmin : G.IsMinimalEEPCounterexample) :
    18 ≤ Fintype.card E := by
  rw [G.edgeCard_eq_three_mul_leftCard_of_cubic hmin.cubic]
  have hleft := hmin.six_le_card_left
  omega

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
