import BachThesisLean.Cubic.StarProductPfaffianProduct

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-!
# Same-port Pfaffian descent through a star product

A Pfaffian signing on a star product already induces the correct intrinsic
relative Pfaffian equation between two perfect matchings of the `A` factor
that use the same root port.  Glue both source matchings against one common
`B` matching.  The star-product Pfaffian equation then descends because its
relative-permutation sign is exactly the `A` relative sign and its common
`B` edge-sign contribution cancels.

This is the assembled same-port theorem needed before the three port classes
are normalized into a single Pfaffian signing on the contraction.
-/

/-- Same-port relative Pfaffian equation on the `A` factor inherited from a
Pfaffian signing of the star product. -/
theorem PfaffianSigning.sourceA_samePort_relative_product_eq
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (PA QA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hQA : A.IsPerfectMatching QA)
    (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hQi : (p i).1 ∈ QA)
    (hBi : (q (σ i)).1 ∈ PB) :
    Equiv.Perm.sign
        (hPA.shoreEquiv.trans hQA.shoreEquiv.symm : Equiv.Perm XA) *
        (∏ e ∈ PA, S.edgeSign (A.starAEdge B r ell p e)) =
      ∏ e ∈ QA, S.edgeSign (A.starAEdge B r ell p e) := by
  let Pstar := starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi
  let Qstar := starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi
  have hstar := S.relative_product_eq Pstar Qstar
  have hsign := starGluedPM_relativeSign_eq_source
    A B r ell p q σ PA QA PB i hPA hQA hPB hPi hQi hBi
  have hstar' :
      Equiv.Perm.sign
          (hPA.shoreEquiv.trans hQA.shoreEquiv.symm : Equiv.Perm XA) *
          (∏ e ∈ A.starGluedMatching B r ell PA PB i, S.edgeSign e) =
        ∏ e ∈ A.starGluedMatching B r ell QA PB i, S.edgeSign e := by
    simpa [Pstar, Qstar] using hsign ▸ hstar
  exact sourceA_relativeProduct_of_commonStar
    A B r ell p q σ PA QA PB i hPA hQA hPB hPi hQi hBi
    S.edgeSign
    (Equiv.Perm.sign
      (hPA.shoreEquiv.trans hQA.shoreEquiv.symm : Equiv.Perm XA))
    hstar'

end BipartiteMultigraph
end BachThesisLean
