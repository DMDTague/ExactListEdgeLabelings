import BachThesisLean.Cubic.BraceReduction
import BachThesisLean.Cubic.BraceSimplicity
import BachThesisLean.Cubic.TinyBraceCases
import BachThesisLean.Cubic.SquareSmoothingReduction

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Minimal EEP counterexamples

This packages the induction hypothesis used throughout the cubic reduction: the
chosen graph is a connected cubic counterexample to EEP, while every strictly
smaller connected cubic graph in the same universe levels has EEP.
-/

structure IsMinimalEEPCounterexample (G : BipartiteMultigraph X Y E) : Prop where
  connected : G.IsConnected
  cubic : G.IsCubic
  failsEEP : ¬ G.HasEEP
  smaller_hasEEP :
    ∀ {X' : Type u} {Y' : Type v} {E' : Type w}
      [Fintype X'] [Fintype Y'] [Fintype E']
      [DecidableEq X'] [DecidableEq Y'] [DecidableEq E'],
      ∀ H : BipartiteMultigraph X' Y' E',
        H.IsConnected → H.IsCubic → H.vertexCard < G.vertexCard → H.HasEEP

namespace IsMinimalEEPCounterexample

variable {G : BipartiteMultigraph X Y E}

/-- A minimal connected cubic EEP counterexample is necessarily a brace.  A
nontrivial tight cut would produce two smaller connected cubic contractions;
minimality gives EEP on both, and tight-cut reconstruction lifts EEP back to
`G`. -/
theorem isBrace (hmin : G.IsMinimalEEPCounterexample) : G.IsBrace := by
  by_contra hnotBrace
  have hMC : G.IsMatchingCovered :=
    G.isMatchingCovered_of_connected_cubic hmin.connected hmin.cubic
  have hsplit :
      ∃ W : Finset (X ⊕ Y), IsNontrivialCutShore W ∧ G.IsTightCut W := by
    by_contra hnone
    apply hnotBrace
    refine ⟨hMC, ?_⟩
    intro W hnontriv hT
    apply hnone
    exact ⟨W, hnontriv, hT⟩
  obtain ⟨W, hWnontriv, hWTight⟩ := hsplit
  obtain ⟨U, _, hUTight, hUnontriv, hOrient⟩ :=
    hWTight.exists_right_oriented_shore hmin.connected hmin.cubic hWnontriv
  have hConnected :=
    hUTight.right_oriented_contractions_connected
      hmin.connected hUnontriv hOrient
  have hCubics :=
    hUTight.right_oriented_contractions_cubic
      hmin.connected hmin.cubic hOrient
  have hSetLt : (G.contractSet U).vertexCard < G.vertexCard :=
    G.contractSet_vertexCard_lt U hUnontriv
  have hComplementLt : (G.contractComplement U).vertexCard < G.vertexCard :=
    G.contractComplement_vertexCard_lt U hUnontriv
  have hSetEEP : (G.contractSet U).HasEEP :=
    hmin.smaller_hasEEP (G.contractSet U) hConnected.2 hCubics.2 hSetLt
  have hComplementEEP : (G.contractComplement U).HasEEP :=
    hmin.smaller_hasEEP
      (G.contractComplement U) hConnected.1 hCubics.1 hComplementLt
  have hEEP : G.HasEEP :=
    (hUTight.right_oriented_hasEEP_iff_contractions
      hmin.connected hmin.cubic hOrient).2
      ⟨hSetEEP, hComplementEEP⟩
  exact hmin.failsEEP hEEP

/-- The finite one- and two-vertex-per-shore base cases exclude tiny minimal
counterexamples. -/
theorem three_le_card_left (hmin : G.IsMinimalEEPCounterexample) :
    3 ≤ Fintype.card X := by
  by_contra hsmall
  have hlt : Fintype.card X < 3 := Nat.lt_of_not_ge hsmall
  exact hmin.failsEEP
    (G.hasEEP_of_connected_cubic_card_left_lt_three
      hmin.connected hmin.cubic hlt)

/-- Consequently every minimal EEP counterexample is simple. -/
theorem isSimple (hmin : G.IsMinimalEEPCounterexample) : G.IsSimple :=
  hmin.isBrace.isSimple_of_three_le_card_left
    hmin.cubic hmin.three_le_card_left

/-- Minimality supplies EEP on either smoothing of any displayed square. -/
theorem squareSmoothing_hasEEP (hmin : G.IsMinimalEEPCounterexample)
    (Q : SquareFrame G) (swap : Bool) : (Q.smooth swap).HasEEP := by
  exact hmin.smaller_hasEEP (Q.smooth swap)
    (BipartiteMultigraph.SquareFrame.IsBrace.squareSmoothing_isConnected
      Q hmin.isBrace hmin.cubic swap)
    (Q.smooth_isCubic hmin.cubic swap)
    (Q.smooth_vertexCard_lt swap)

/-- Every bad prescribed pair in a minimal counterexample meets every displayed
square in at least one of its two marked edge copies. -/
theorem badPair_meets_square (hmin : G.IsMinimalEEPCounterexample)
    (Q : SquareFrame G) {e f : E} (hef : e ≠ f)
    (hbad : ¬ G.EdgePairWitness e f) :
    ¬ Q.OutsideSquare e ∨ ¬ Q.OutsideSquare f := by
  apply
    BipartiteMultigraph.SquareFrame.IsBrace.badPair_meets_square_of_smaller_EEP
      Q hmin.isBrace hmin.cubic
  · intro swap hconn hCubic hlt
    exact hmin.smaller_hasEEP (Q.smooth swap) hconn hCubic hlt
  · exact hef
  · exact hbad

/-- A minimal counterexample therefore cannot contain three pairwise
edge-disjoint displayed squares in the presence of a fixed bad pair. -/
theorem no_three_edgeDisjoint_squares_of_badPair
    (hmin : G.IsMinimalEEPCounterexample)
    (Q0 Q1 Q2 : SquareFrame G)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f)
    (h01 : SquareFrame.SquareEdgeDisjoint Q0 Q1)
    (h02 : SquareFrame.SquareEdgeDisjoint Q0 Q2)
    (h12 : SquareFrame.SquareEdgeDisjoint Q1 Q2) : False := by
  exact SquareFrame.pair_cannot_meet_three_edgeDisjoint_squares Q0 Q1 Q2
    h01 h02 h12
    (hmin.badPair_meets_square Q0 hef hbad)
    (hmin.badPair_meets_square Q1 hef hbad)
    (hmin.badPair_meets_square Q2 hef hbad)

/-- Failure of EEP in a minimal counterexample is witnessed by an actual pair
of distinct edge copies with no common complementary-factor component witness. -/
theorem exists_badPair (hmin : G.IsMinimalEEPCounterexample) :
    ∃ e f : E, e ≠ f ∧ ¬ G.EdgePairWitness e f :=
  SquareFrame.exists_badPair_of_not_hasEEP hmin.failsEEP

/-- A minimal EEP counterexample has no three pairwise edge-disjoint displayed
squares.  This is the square-packing obstruction with the bad pair discharged
from the public statement. -/
theorem no_three_edgeDisjoint_squares
    (hmin : G.IsMinimalEEPCounterexample)
    (Q0 Q1 Q2 : SquareFrame G)
    (h01 : SquareFrame.SquareEdgeDisjoint Q0 Q1)
    (h02 : SquareFrame.SquareEdgeDisjoint Q0 Q2)
    (h12 : SquareFrame.SquareEdgeDisjoint Q1 Q2) : False := by
  obtain ⟨e, f, hef, hbad⟩ := hmin.exists_badPair
  exact hmin.no_three_edgeDisjoint_squares_of_badPair
    Q0 Q1 Q2 hef hbad h01 h02 h12

/-- Existential packaging of the same obstruction. -/
theorem not_exists_three_edgeDisjoint_squares
    (hmin : G.IsMinimalEEPCounterexample) :
    ¬ ∃ Q0 Q1 Q2 : SquareFrame G,
      SquareFrame.SquareEdgeDisjoint Q0 Q1 ∧
      SquareFrame.SquareEdgeDisjoint Q0 Q2 ∧
      SquareFrame.SquareEdgeDisjoint Q1 Q2 := by
  rintro ⟨Q0, Q1, Q2, h01, h02, h12⟩
  exact hmin.no_three_edgeDisjoint_squares Q0 Q1 Q2 h01 h02 h12

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
