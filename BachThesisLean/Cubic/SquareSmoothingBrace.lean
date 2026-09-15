import BachThesisLean.Cubic.BraceMinCut
import BachThesisLean.Cubic.SquareSmoothingDeletion

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Square smoothings inside cubic braces

A square frame already exhibits three distinct left vertices: the two left
vertices of the square and either external left terminal.  Thus a cubic brace
carrying a square frame is in the non-tiny regime where brace simplicity holds.
The simple-brace three-edge cut lower bound then feeds the deletion theorem and
makes both square smoothings connected.
-/

/-- A square frame forces at least three left vertices. -/
theorem three_le_card_left (Q : SquareFrame G) : 3 ≤ Fintype.card X := by
  classical
  let S : Finset X :=
    {Q.leftVertex false, Q.leftVertex true, Q.externalLeft false}
  have h01 : Q.leftVertex false ≠ Q.leftVertex true := Q.leftVertex_ne
  have h0e : Q.leftVertex false ≠ Q.externalLeft false :=
    (Q.externalLeft_ne false false).symm
  have h1e : Q.leftVertex true ≠ Q.externalLeft false :=
    (Q.externalLeft_ne false true).symm
  have hcard : S.card = 3 := by
    simp [S, h01, h0e, h1e]
  calc
    3 = S.card := hcard.symm
    _ ≤ (Finset.univ : Finset X).card :=
      Finset.card_le_card (Finset.subset_univ S)
    _ = Fintype.card X := by simp

/-- Hence a cubic brace carrying this square frame is simple. -/
theorem IsBrace.isSimple_of_squareFrame
    (Q : SquareFrame G) (hbrace : G.IsBrace) (hG : G.IsCubic) : G.IsSimple :=
  hbrace.isSimple_of_three_le_card_left hG (three_le_card_left Q)

/-- The square-frame brace has the global three-edge cut lower bound needed by
the deletion-connectivity theorem. -/
theorem IsBrace.minCut_three_of_squareFrame
    (Q : SquareFrame G) (hbrace : G.IsBrace) (hG : G.IsCubic) :
    ∀ W : Finset (X ⊕ Y), W.Nonempty → Wᶜ.Nonempty →
      3 ≤ (G.edgeCut W).card := by
  intro W hW hWc
  exact hbrace.edgeCut_card_ge_three_of_simple_cubic hG
    (IsBrace.isSimple_of_squareFrame Q hbrace hG) W hW hWc

/-- Either square smoothing of a cubic brace is connected. -/
theorem IsBrace.squareSmoothing_isConnected
    (hbrace : G.IsBrace) (hG : G.IsCubic) (swap : Bool) :
    (Q.smooth swap).IsConnected :=
  Q.smooth_isConnected_of_minCut_three
    (IsBrace.minCut_three_of_squareFrame Q hbrace hG) swap

/-- Both terminal pairings are connected simultaneously. -/
theorem IsBrace.both_squareSmoothings_connected
    (hbrace : G.IsBrace) (hG : G.IsCubic) :
    (Q.smooth false).IsConnected ∧ (Q.smooth true).IsConnected :=
  Q.both_smoothings_connected_of_minCut_three
    (IsBrace.minCut_three_of_squareFrame Q hbrace hG)

/-- Each smoothing is matching-covered as well: connectivity is the only new
input, since square smoothing already preserves cubicity. -/
theorem IsBrace.squareSmoothing_isMatchingCovered
    (hbrace : G.IsBrace) (hG : G.IsCubic) (swap : Bool) :
    (Q.smooth swap).IsMatchingCovered :=
  (Q.smooth swap).isMatchingCovered_of_connected_cubic
    (IsBrace.squareSmoothing_isConnected Q hbrace hG swap)
    (Q.smooth_isCubic hG swap)

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
