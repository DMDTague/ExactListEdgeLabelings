import BachThesisLean.Cubic.OddPathSmoothingProduct

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Pfaffian closure under odd-path smoothing

Combining the shore-permutation and edge-product calculations gives the
manuscript's elementary smoothing identity.  Both local matching states produce
exactly the same ambient scalar `s(wz)` times the signed determinant term of
the smoothed matching.  Hence an ambient Pfaffian signing, expressed relative
to the canonical extension of a reduced shore reference, descends to a
Pfaffian signing of the smoothed graph.
-/

/-- Every lifted ambient signed term is the middle-path sign times the
corresponding smoothed signed term. -/
theorem PerfectMatching.lift_oddPath_signedTerm
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (edgeSign : E → ℤˣ) (P : Q.smooth.PerfectMatching) :
    (PerfectMatching.lift_oddPath Q P).signedTerm
        (Q.extendReducedEquiv reference) edgeSign =
      edgeSign Q.wz *
        P.signedTerm reference (Q.smoothEdgeSign edgeSign) := by
  unfold PerfectMatching.signedTerm
  by_cases hfresh : Q.freshSelected P.val
  · rw [PerfectMatching.lift_oddPath_referenceSign_of_fresh
        Q reference P hfresh,
      PerfectMatching.lift_oddPath_val Q P,
      Q.prod_liftMatchingSet_of_fresh P.val edgeSign hfresh]
    simp only [neg_mul, mul_neg, neg_neg]
    ac_rfl
  · rw [PerfectMatching.lift_oddPath_referenceSign_of_not_fresh
        Q reference P hfresh,
      PerfectMatching.lift_oddPath_val Q P,
      Q.prod_liftMatchingSet_of_not_fresh P.val edgeSign hfresh]
    ac_rfl

/-- An ambient Pfaffian signing descends through smoothing an odd path with
saturated degree-two internal vertices.  The fresh smoothed copy receives sign
`-s(uz)s(wz)s(wv)`; surviving actual copies retain their old signs. -/
def PfaffianSigning.smoothOddPath
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (S : PfaffianSigning G (Q.extendReducedEquiv reference)) :
    PfaffianSigning Q.smooth reference where
  edgeSign := Q.smoothEdgeSign S.edgeSign
  terms_eq := by
    intro P R
    have hamb := S.terms_eq
      (PerfectMatching.lift_oddPath Q P)
      (PerfectMatching.lift_oddPath Q R)
    rw [PerfectMatching.lift_oddPath_signedTerm Q reference S.edgeSign P,
      PerfectMatching.lift_oddPath_signedTerm Q reference S.edgeSign R] at hamb
    exact mul_left_cancel hamb

@[simp] theorem PfaffianSigning.smoothOddPath_edgeSign_old
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (S : PfaffianSigning G (Q.extendReducedEquiv reference))
    (e : Q.Survivor) :
    (PfaffianSigning.smoothOddPath Q reference S).edgeSign (Q.oldEdge e) =
      S.edgeSign e.val := rfl

@[simp] theorem PfaffianSigning.smoothOddPath_edgeSign_fresh
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (S : PfaffianSigning G (Q.extendReducedEquiv reference)) :
    (PfaffianSigning.smoothOddPath Q reference S).edgeSign Q.freshEdge =
      -(S.edgeSign Q.uz * S.edgeSign Q.wz * S.edgeSign Q.wv) := rfl

/-- Existence form of odd-path Pfaffian closure at a chosen reduced reference. -/
theorem exists_pfaffianSigning_smooth_of_extend
    (reference : Q.ReducedLeft ≃ Q.ReducedRight)
    (h : Nonempty (PfaffianSigning G (Q.extendReducedEquiv reference))) :
    Nonempty (PfaffianSigning Q.smooth reference) := by
  rcases h with ⟨S⟩
  exact ⟨PfaffianSigning.smoothOddPath Q reference S⟩

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
