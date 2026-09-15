import BachThesisLean.Cubic.SquareSmoothingPfaffianGraphIso
import BachThesisLean.Cubic.OddPathSmoothingWitness
import BachThesisLean.Cubic.PfaffianIsomorphism

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Pfaffian closure under square smoothing

A direct square smoothing factors into four already-audited operations:

1. take the spanning pairing restriction;
2. smooth the retained odd path through the first square column;
3. smooth the retained odd path through the second square column;
4. relabel the resulting graph by the explicit edge-copy isomorphism with the
   direct square smoothing.

Each step preserves a packaged `PfaffianWitness`, so the direct smoothing does
as well.  No external Pfaffian-brace theorem is used here.
-/

/-- Pfaffianness is preserved by either of the two square smoothings. -/
theorem exists_pfaffianWitness_squareSmooth
    (swap : Bool) (h : Nonempty (PfaffianWitness G)) :
    Nonempty (PfaffianWitness (Q.smooth swap)) := by
  have hRestrict :
      Nonempty (PfaffianWitness
        (G.restrictEdges (Q.pairingRestrictionEdges swap))) :=
    exists_pfaffianWitness_restrictEdges (Q.pairingRestrictionEdges swap) h
  have hFirst :
      Nonempty (PfaffianWitness (Q.firstPairingOddPathFrame swap).smooth) :=
    OddPathFrame.exists_pfaffianWitness_smoothOddPath
      (Q.firstPairingOddPathFrame swap) hRestrict
  have hSecond :
      Nonempty (PfaffianWitness (Q.secondPairingOddPathFrame swap).smooth) :=
    OddPathFrame.exists_pfaffianWitness_smoothOddPath
      (Q.secondPairingOddPathFrame swap) hFirst
  exact (Q.twoStepGraphIso swap).pfaffianWitness_nonempty_iff.mpr hSecond

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
