import BachThesisLean.Cubic.SquareSmoothingBrace
import BachThesisLean.Cubic.SquareSmoothingSize
import BachThesisLean.Cubic.SquareSmoothingEEP

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Minimal-counterexample reduction through a square

For a cubic brace, both square smoothings remain connected cubic graphs and
have strictly fewer vertices.  Thus any induction hypothesis proving EEP for
smaller connected cubic graphs supplies EEP on both smoothings.  The explicit
square witness lift then rules out a bad prescribed pair whose two marked edge
copies both avoid the four cycle copies.
-/

/-- An induction hypothesis on smaller connected cubic graphs yields an EEP
witness for every distinct prescribed pair outside the displayed square. -/
theorem IsBrace.edgePairWitness_outsideSquare_of_smaller_EEP
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hIH : ∀ swap : Bool,
      (Q.smooth swap).IsConnected →
      (Q.smooth swap).IsCubic →
      vertexCard (Q.smooth swap) < vertexCard G →
      (Q.smooth swap).HasEEP)
    {e f : E} (heOut : Q.OutsideSquare e) (hfOut : Q.OutsideSquare f)
    (hef : e ≠ f) :
    G.EdgePairWitness e f := by
  have hFalse : (Q.smooth false).HasEEP :=
    hIH false
      (BipartiteMultigraph.SquareFrame.IsBrace.squareSmoothing_isConnected
        Q hbrace hG false)
      (Q.smooth_isCubic hG false)
      (Q.smooth_vertexCard_lt false)
  have hTrue : (Q.smooth true).HasEEP :=
    hIH true
      (BipartiteMultigraph.SquareFrame.IsBrace.squareSmoothing_isConnected
        Q hbrace hG true)
      (Q.smooth_isCubic hG true)
      (Q.smooth_vertexCard_lt true)
  exact Q.edgePairWitness_of_both_smoothings hG hFalse hTrue heOut hfOut hef

/-- Contrapositive form: under the smaller-graph EEP induction hypothesis, a
bad pair cannot have both marked edge copies outside this square.  Equivalently
at least one of the two marked copies belongs to the displayed four-cycle. -/
theorem IsBrace.badPair_meets_square_of_smaller_EEP
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hIH : ∀ swap : Bool,
      (Q.smooth swap).IsConnected →
      (Q.smooth swap).IsCubic →
      vertexCard (Q.smooth swap) < vertexCard G →
      (Q.smooth swap).HasEEP)
    {e f : E} (hef : e ≠ f)
    (hbad : ¬ G.EdgePairWitness e f) :
    ¬ Q.OutsideSquare e ∨ ¬ Q.OutsideSquare f := by
  by_cases heOut : Q.OutsideSquare e
  · right
    intro hfOut
    exact hbad
      (BipartiteMultigraph.SquareFrame.IsBrace.edgePairWitness_outsideSquare_of_smaller_EEP
        Q hbrace hG hIH heOut hfOut hef)
  · exact Or.inl heOut

/-- The four cycle copies of two square frames are edge-disjoint.  The
formulation is intentionally edge-copy based: if a copy lies on the first
square, it lies outside the second square. -/
def SquareEdgeDisjoint (Q R : SquareFrame G) : Prop :=
  ∀ e : E, ¬ Q.OutsideSquare e → R.OutsideSquare e

/-- Edge-disjointness of square frames is symmetric. -/
theorem squareEdgeDisjoint_symm {Q R : SquareFrame G}
    (h : SquareEdgeDisjoint Q R) : SquareEdgeDisjoint R Q := by
  intro e heR
  by_contra heQ
  exact heR (h e heQ)

/-- A fixed pair of edge copies cannot meet three pairwise edge-disjoint
squares.  This is the finite pigeonhole step used after square smoothing: each
square must contain one of only two marked copies, so two of the three squares
would share that copy. -/
theorem pair_cannot_meet_three_edgeDisjoint_squares
    (Q0 Q1 Q2 : SquareFrame G) {e f : E}
    (h01 : SquareEdgeDisjoint Q0 Q1)
    (h02 : SquareEdgeDisjoint Q0 Q2)
    (h12 : SquareEdgeDisjoint Q1 Q2)
    (h0 : ¬ Q0.OutsideSquare e ∨ ¬ Q0.OutsideSquare f)
    (h1 : ¬ Q1.OutsideSquare e ∨ ¬ Q1.OutsideSquare f)
    (h2 : ¬ Q2.OutsideSquare e ∨ ¬ Q2.OutsideSquare f) : False := by
  rcases h0 with he0 | hf0
  · rcases h1 with he1 | hf1
    · exact he1 (h01 e he0)
    · rcases h2 with he2 | hf2
      · exact he2 (h02 e he0)
      · exact hf2 (h12 f hf1)
  · rcases h1 with he1 | hf1
    · rcases h2 with he2 | hf2
      · exact he2 (h12 e he1)
      · exact hf2 (h02 f hf0)
    · exact hf1 (h01 f hf0)

/-- Minimal-counterexample square obstruction.  If all smaller connected cubic
smoothings have EEP, a bad pair in a cubic brace forbids three pairwise
edge-disjoint square frames. -/
theorem IsBrace.no_three_edgeDisjoint_squares_of_badPair_of_smaller_EEP
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (Q0 Q1 Q2 : SquareFrame G)
    (hIH0 : ∀ swap : Bool,
      (Q0.smooth swap).IsConnected →
      (Q0.smooth swap).IsCubic →
      vertexCard (Q0.smooth swap) < vertexCard G →
      (Q0.smooth swap).HasEEP)
    (hIH1 : ∀ swap : Bool,
      (Q1.smooth swap).IsConnected →
      (Q1.smooth swap).IsCubic →
      vertexCard (Q1.smooth swap) < vertexCard G →
      (Q1.smooth swap).HasEEP)
    (hIH2 : ∀ swap : Bool,
      (Q2.smooth swap).IsConnected →
      (Q2.smooth swap).IsCubic →
      vertexCard (Q2.smooth swap) < vertexCard G →
      (Q2.smooth swap).HasEEP)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f)
    (h01 : SquareEdgeDisjoint Q0 Q1)
    (h02 : SquareEdgeDisjoint Q0 Q2)
    (h12 : SquareEdgeDisjoint Q1 Q2) : False := by
  have h0 : ¬ Q0.OutsideSquare e ∨ ¬ Q0.OutsideSquare f :=
    BipartiteMultigraph.SquareFrame.IsBrace.badPair_meets_square_of_smaller_EEP
      Q0 hbrace hG hIH0 hef hbad
  have h1 : ¬ Q1.OutsideSquare e ∨ ¬ Q1.OutsideSquare f :=
    BipartiteMultigraph.SquareFrame.IsBrace.badPair_meets_square_of_smaller_EEP
      Q1 hbrace hG hIH1 hef hbad
  have h2 : ¬ Q2.OutsideSquare e ∨ ¬ Q2.OutsideSquare f :=
    BipartiteMultigraph.SquareFrame.IsBrace.badPair_meets_square_of_smaller_EEP
      Q2 hbrace hG hIH2 hef hbad
  exact pair_cannot_meet_three_edgeDisjoint_squares Q0 Q1 Q2 h01 h02 h12 h0 h1 h2

/-- Failure of EEP is witnessed by a concrete pair of distinct edge copies
without an edge-pair witness. -/
theorem exists_badPair_of_not_hasEEP (hnot : ¬ G.HasEEP) :
    ∃ e f : E, e ≠ f ∧ ¬ G.EdgePairWitness e f := by
  classical
  by_contra hnone
  apply hnot
  intro e f hef
  by_contra hbad
  apply hnone
  exact ⟨e, f, hef, hbad⟩

/-- Three pairwise edge-disjoint squares close the EEP induction step for a
cubic brace.  The only recursive inputs are EEP for strictly smaller connected
cubic graphs; the two smoothings of each square meet those hypotheses by the
preceding connectivity and size theorems. -/
theorem IsBrace.hasEEP_of_three_edgeDisjoint_squares_of_smaller_EEP
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (Q0 Q1 Q2 : SquareFrame G)
    (h01 : SquareEdgeDisjoint Q0 Q1)
    (h02 : SquareEdgeDisjoint Q0 Q2)
    (h12 : SquareEdgeDisjoint Q1 Q2)
    (hIH :
      ∀ {X' : Type u} {Y' : Type v} {E' : Type w}
        [Fintype X'] [Fintype Y'] [Fintype E']
        [DecidableEq X'] [DecidableEq Y'] [DecidableEq E'],
        ∀ H : BipartiteMultigraph X' Y' E',
          H.IsConnected → H.IsCubic →
          vertexCard H < vertexCard G → H.HasEEP) :
    G.HasEEP := by
  by_contra hnot
  obtain ⟨e, f, hef, hbad⟩ := exists_badPair_of_not_hasEEP hnot
  have hIH0 : ∀ swap : Bool,
      (Q0.smooth swap).IsConnected →
      (Q0.smooth swap).IsCubic →
      vertexCard (Q0.smooth swap) < vertexCard G →
      (Q0.smooth swap).HasEEP := by
    intro swap hconn hcubic hlt
    exact hIH (Q0.smooth swap) hconn hcubic hlt
  have hIH1 : ∀ swap : Bool,
      (Q1.smooth swap).IsConnected →
      (Q1.smooth swap).IsCubic →
      vertexCard (Q1.smooth swap) < vertexCard G →
      (Q1.smooth swap).HasEEP := by
    intro swap hconn hcubic hlt
    exact hIH (Q1.smooth swap) hconn hcubic hlt
  have hIH2 : ∀ swap : Bool,
      (Q2.smooth swap).IsConnected →
      (Q2.smooth swap).IsCubic →
      vertexCard (Q2.smooth swap) < vertexCard G →
      (Q2.smooth swap).HasEEP := by
    intro swap hconn hcubic hlt
    exact hIH (Q2.smooth swap) hconn hcubic hlt
  exact
    BipartiteMultigraph.SquareFrame.IsBrace.no_three_edgeDisjoint_squares_of_badPair_of_smaller_EEP
      hbrace hG Q0 Q1 Q2 hIH0 hIH1 hIH2 hef hbad h01 h02 h12

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
