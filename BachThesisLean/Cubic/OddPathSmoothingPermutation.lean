import BachThesisLean.Cubic.OddPathSmoothingShore
import Mathlib.GroupTheory.Perm.Sign

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Relative permutations through odd-path smoothing

The custom shore-equivalence extension used by the smoothing construction is
the extension of the corresponding reduced relative permutation along the
canonical subtype embedding.  Therefore mathlib's sign theorem for
`viaFintypeEmbedding` applies without re-proving parity by inversion counting.
-/

/-- Canonical embedding of the reduced left shore back into the ambient left
shore. -/
def reducedLeftEmbedding : Q.ReducedLeft ↪ X :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem reducedLeftEmbedding_apply (x : Q.ReducedLeft) :
    Q.reducedLeftEmbedding x = x.val := rfl

/-- The deleted left vertex is outside the range of the reduced-shore
embedding. -/
theorem w_not_mem_range_reducedLeftEmbedding :
    Q.w ∉ Set.range Q.reducedLeftEmbedding := by
  rintro ⟨x, hx⟩
  exact x.property hx

/-- Relative permutations of two extended shore equivalences are obtained by
extending the corresponding reduced relative permutation and fixing `w`. -/
theorem extendReducedEquiv_relativePerm
    (a b : Q.ReducedLeft ≃ Q.ReducedRight) :
    (Q.extendReducedEquiv a).trans (Q.extendReducedEquiv b).symm =
      Equiv.Perm.viaFintypeEmbedding
        (a.trans b.symm : Equiv.Perm Q.ReducedLeft)
        Q.reducedLeftEmbedding := by
  ext x
  by_cases hx : x = Q.w
  · subst x
    simp only [Equiv.trans_apply]
    rw [Q.extendReducedEquiv_apply_w a,
      Q.extendReducedEquiv_symm_apply_z b]
    have hfix :=
      Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range
        (e := (a.trans b.symm : Equiv.Perm Q.ReducedLeft))
        (f := Q.reducedLeftEmbedding) Q.w_not_mem_range_reducedLeftEmbedding
    exact hfix.symm
  · let xr : Q.ReducedLeft := ⟨x, hx⟩
    change (Q.extendReducedEquiv b).symm
        (Q.extendReducedEquiv a xr.val) =
      (Equiv.Perm.viaFintypeEmbedding
        (a.trans b.symm : Equiv.Perm Q.ReducedLeft)
        Q.reducedLeftEmbedding) xr.val
    rw [Q.extendReducedEquiv_apply_reduced a xr,
      Q.extendReducedEquiv_symm_apply_reduced b (a xr)]
    have himage :=
      Equiv.Perm.viaFintypeEmbedding_apply_image
        (e := (a.trans b.symm : Equiv.Perm Q.ReducedLeft))
        (f := Q.reducedLeftEmbedding) xr
    exact himage.symm

/-- Extending both shore identifications by the deleted pair does not change
the sign of their relative permutation. -/
theorem sign_extendReducedEquiv_relativePerm
    (a b : Q.ReducedLeft ≃ Q.ReducedRight) :
    Equiv.Perm.sign
      ((Q.extendReducedEquiv a).trans (Q.extendReducedEquiv b).symm) =
    Equiv.Perm.sign (a.trans b.symm : Equiv.Perm Q.ReducedLeft) := by
  rw [Q.extendReducedEquiv_relativePerm a b]
  exact Equiv.Perm.viaFintypeEmbedding_sign
    (a.trans b.symm : Equiv.Perm Q.ReducedLeft) Q.reducedLeftEmbedding

/-- In the non-fresh local state, lifting a perfect matching preserves the
permutation sign relative to an extended reference equivalence. -/
theorem PerfectMatching.lift_oddPath_referenceSign_of_not_fresh
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (P : Q.smooth.PerfectMatching) (hfresh : ¬ Q.freshSelected P.val) :
    Equiv.Perm.sign
      ((PerfectMatching.lift_oddPath Q P).referencePerm
        (Q.extendReducedEquiv reference)) =
    Equiv.Perm.sign (P.referencePerm reference) := by
  rw [PerfectMatching.referencePerm, PerfectMatching.referencePerm,
    PerfectMatching.lift_oddPath_shoreEquiv_of_not_fresh Q P hfresh]
  exact Q.sign_extendReducedEquiv_relativePerm P.shoreEquiv reference

/-- In the fresh local state, lifting introduces exactly one transposition, so
the relative permutation sign is negated. -/
theorem PerfectMatching.lift_oddPath_referenceSign_of_fresh
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val) :
    Equiv.Perm.sign
      ((PerfectMatching.lift_oddPath Q P).referencePerm
        (Q.extendReducedEquiv reference)) =
    - Equiv.Perm.sign (P.referencePerm reference) := by
  rw [PerfectMatching.referencePerm, PerfectMatching.referencePerm,
    PerfectMatching.lift_oddPath_shoreEquiv_of_fresh Q P hfresh,
    Equiv.trans_assoc, Equiv.Perm.sign_trans,
    Q.sign_extendReducedEquiv_relativePerm P.shoreEquiv reference,
    Equiv.Perm.sign_swap Q.u_ne_w]
  simp

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
