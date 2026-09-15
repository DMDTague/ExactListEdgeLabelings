import BachThesisLean.Cubic.FourVertexAmplifier
import BachThesisLean.Cubic.ShoreSwap

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Shore-symmetric four-vertex amplification

The right-root amplifier theorem is the orientation used by `starProduct`.
A singleton mask rooted on the left shore is reduced to it by exchanging the
bipartition shores.  This is the manuscript phrase “after exchanging the
bipartition shores if necessary” made explicit.
-/

/-- A singleton mask at a left root becomes the right-root amplifier situation
in the shore-swapped graph. -/
theorem singleton_edgeRootMask_amplified_not_hasEVP_left
    (A : BipartiteMultigraph X Y E) (hA : A.IsCubic)
    (x : X) (p : A.PortEnumeration (.inl x))
    (e : {e : E // A.left e ≠ x}) (i : Fin 3)
    (hmask : A.edgeRootMask (.inl x) p e.1 = {i}) :
    ∃ σ : Equiv.Perm (Fin 3),
      ¬ (A.shoreSwap.starProduct CubicRegression.amplifier x 0
          (A.shoreSwapPortEnumeration (.inl x) p)
          CubicRegression.amplifierPorts σ).HasEVP := by
  let p' := A.shoreSwapPortEnumeration (.inl x) p
  let e' : {d : E // A.shoreSwap.right d ≠ x} := ⟨e.1, e.2⟩
  have hAs : A.shoreSwap.IsCubic :=
    (A.shoreSwap_isCubic_iff).2 hA
  have hmask' :
      A.shoreSwap.edgeRootMask (.inr x) p' e'.1 = {i} := by
    calc
      A.shoreSwap.edgeRootMask (.inr x) p' e'.1 =
          A.edgeRootMask (.inl x) p e.1 := by
        simpa [p', e'] using
          (A.shoreSwap_edgeRootMask (.inl x) p e.1)
      _ = {i} := hmask
  exact A.shoreSwap.singleton_edgeRootMask_amplified_not_hasEVP_right
    hAs x p' e' i hmask'

end BipartiteMultigraph
end BachThesisLean
