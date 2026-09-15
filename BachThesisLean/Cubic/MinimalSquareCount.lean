import BachThesisLean.Cubic.FiveVertexMinimalCounterexample

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# The global four-square restriction

The five-shore contradiction contains a size-independent covering argument.
Fix a bad pair in a minimum EEP counterexample.  Every displayed square meets
exactly one marked copy.  Index squares by their unordered pair of left rows.
A fixed marked edge can lie on at most two such indexed squares in a simple
cubic graph, so the two marked copies cover at most four indexed squares.
-/

namespace IsMinimalEEPCounterexample

/-- A minimum EEP counterexample has at most four left-indexed squares. -/
theorem squareLeftPairs_card_le_four
    (hmin : G.IsMinimalEEPCounterexample) :
    G.squareLeftPairs.card ≤ 4 := by
  classical
  have hsimple : G.IsSimple :=
    hmin.isBrace.isSimple_of_three_le_card_left hmin.cubic (by
      have hfive := hmin.five_le_card_left
      omega)
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
  have hcoverCard : G.squareLeftPairs.card ≤ (A ∪ B).card :=
    Finset.card_le_card hcover
  have hunion : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have hA : A.card ≤ 2 := by
    simpa [A] using G.squareLeftPairsAtEdge_card_le_two hsimple hmin.cubic e
  have hB : B.card ≤ 2 := by
    simpa [B] using G.squareLeftPairsAtEdge_card_le_two hsimple hmin.cubic f
  omega

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
