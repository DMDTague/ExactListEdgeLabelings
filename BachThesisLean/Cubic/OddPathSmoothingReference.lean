import BachThesisLean.Cubic.OddPathSmoothing

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Extending shore equivalences across an odd-path smoothing

The smoothing removes exactly one left vertex `w` and one right vertex `z`.
Any equivalence between the reduced shores therefore extends to an equivalence
of the ambient shores by sending the deleted pair to each other.  Keeping this
construction explicit makes the determinant-sign comparison in the Pfaffian
smoothing theorem transparent.
-/

/-- Extend an equivalence of the reduced shores by the deleted pair `w ↦ z`. -/
noncomputable def extendReducedEquiv
    (r : Q.ReducedLeft ≃ Q.ReducedRight) : X ≃ Y where
  toFun x := if hx : x = Q.w then Q.z else (r ⟨x, hx⟩).val
  invFun y := if hy : y = Q.z then Q.w else (r.symm ⟨y, hy⟩).val
  left_inv x := by
    by_cases hx : x = Q.w
    · subst x
      simp
    · have hrz : (r ⟨x, hx⟩).val ≠ Q.z := (r ⟨x, hx⟩).property
      simp [hx, hrz]
  right_inv y := by
    by_cases hy : y = Q.z
    · subst y
      simp
    · have hrw : (r.symm ⟨y, hy⟩).val ≠ Q.w :=
        (r.symm ⟨y, hy⟩).property
      simp [hy, hrw]

@[simp] theorem extendReducedEquiv_apply_w
    (r : Q.ReducedLeft ≃ Q.ReducedRight) :
    Q.extendReducedEquiv r Q.w = Q.z := by
  simp [extendReducedEquiv]

@[simp] theorem extendReducedEquiv_apply_reduced
    (r : Q.ReducedLeft ≃ Q.ReducedRight) (x : Q.ReducedLeft) :
    Q.extendReducedEquiv r x.val = (r x).val := by
  simp [extendReducedEquiv, x.property]

@[simp] theorem extendReducedEquiv_symm_apply_z
    (r : Q.ReducedLeft ≃ Q.ReducedRight) :
    (Q.extendReducedEquiv r).symm Q.z = Q.w := by
  simp [extendReducedEquiv]

@[simp] theorem extendReducedEquiv_symm_apply_reduced
    (r : Q.ReducedLeft ≃ Q.ReducedRight) (y : Q.ReducedRight) :
    (Q.extendReducedEquiv r).symm y.val = (r.symm y).val := by
  simp [extendReducedEquiv, y.property]

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
