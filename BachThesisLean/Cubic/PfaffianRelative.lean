import BachThesisLean.Cubic.PfaffianReference

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Reference-free comparison of Pfaffian terms

Although an individual determinant term is written relative to an arbitrary
shore equivalence `X ≃ Y`, equality of two such terms is intrinsic.  The fixed
reference cancels, leaving only the sign of the relative permutation between
the two matching-induced shore equivalences and the two edge-sign products.

This form is convenient for decomposition arguments: when two global matchings
agree on one side of a cut, only the relative permutation and edge products on
the varying side remain.
-/

/-- The reference permutation of `P` factors through the relative permutation
from `P` to `Q` followed by the reference permutation of `Q`. -/
theorem PerfectMatching.referencePerm_eq_relative_trans
    (reference : X ≃ Y) (P Q : G.PerfectMatching) :
    P.referencePerm reference =
      (P.shoreEquiv.trans Q.shoreEquiv.symm : Equiv.Perm X).trans
        (Q.referencePerm reference) := by
  ext x
  simp [PerfectMatching.referencePerm]

/-- Hence the permutation sign of `P` is the relative sign from `P` to `Q`
times the permutation sign of `Q`. -/
theorem PerfectMatching.referenceSign_eq_relative_mul
    (reference : X ≃ Y) (P Q : G.PerfectMatching) :
    Equiv.Perm.sign (P.referencePerm reference) =
      Equiv.Perm.sign
          (P.shoreEquiv.trans Q.shoreEquiv.symm : Equiv.Perm X) *
        Equiv.Perm.sign (Q.referencePerm reference) := by
  rw [P.referencePerm_eq_relative_trans reference Q,
    Equiv.Perm.sign_trans]
  exact mul_comm _ _

/-- Equality of signed determinant terms is independent of the chosen shore
reference.  It is equivalent to the relative-permutation sign carrying the
edge-sign product of `P` to that of `Q`. -/
theorem PerfectMatching.signedTerm_eq_iff_relative
    (reference : X ≃ Y) (edgeSign : E → ℤˣ)
    (P Q : G.PerfectMatching) :
    P.signedTerm reference edgeSign = Q.signedTerm reference edgeSign ↔
      Equiv.Perm.sign
          (P.shoreEquiv.trans Q.shoreEquiv.symm : Equiv.Perm X) *
          (∏ e ∈ P.val, edgeSign e) =
        ∏ e ∈ Q.val, edgeSign e := by
  unfold PerfectMatching.signedTerm
  rw [P.referenceSign_eq_relative_mul reference Q]
  let sP := Equiv.Perm.sign
    (P.shoreEquiv.trans Q.shoreEquiv.symm : Equiv.Perm X)
  let sQ := Equiv.Perm.sign (Q.referencePerm reference)
  let pP := ∏ e ∈ P.val, edgeSign e
  let pQ := ∏ e ∈ Q.val, edgeSign e
  change (sP * sQ) * pP = sQ * pQ ↔ sP * pP = pQ
  constructor
  · intro h
    have h' : sQ * (sP * pP) = sQ * pQ := by
      calc
        sQ * (sP * pP) = (sP * sQ) * pP := by ac_rfl
        _ = sQ * pQ := h
    exact mul_left_cancel h'
  · intro h
    calc
      (sP * sQ) * pP = sQ * (sP * pP) := by ac_rfl
      _ = sQ * pQ := congrArg (sQ * ·) h

/-- A Pfaffian signing therefore supplies the intrinsic relative equation for
any pair of perfect matchings. -/
theorem PfaffianSigning.relative_product_eq
    {reference : X ≃ Y} (S : PfaffianSigning G reference)
    (P Q : G.PerfectMatching) :
    Equiv.Perm.sign
        (P.shoreEquiv.trans Q.shoreEquiv.symm : Equiv.Perm X) *
        (∏ e ∈ P.val, S.edgeSign e) =
      ∏ e ∈ Q.val, S.edgeSign e := by
  exact (P.signedTerm_eq_iff_relative reference S.edgeSign Q).1
    (S.terms_eq P Q)

end BipartiteMultigraph
end BachThesisLean
