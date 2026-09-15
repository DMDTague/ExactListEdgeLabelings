import BachThesisLean.Cubic.StarProductPfaffianProductB

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
# Same-port Pfaffian descent through a star product: B factor

This is the complementary-factor analogue of `sourceA_samePort_relative_product_eq`.
Two `B` perfect matchings through the same bridge class are glued against one
common `A` matching.  The star-product Pfaffian equation descends using the
right-shore relative-sign factorization and the common-`A` edge-product
cancellation theorem.
-/

/-- Same-port relative Pfaffian equation on the `B` factor inherited from a
Pfaffian signing of the star product. -/
theorem PfaffianSigning.sourceB_samePort_relative_product_eq
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (PA : Finset EA) (PB QB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hQB : B.IsPerfectMatching QB)
    (hAi : (p i).1 ∈ PA)
    (hPi : (q (σ i)).1 ∈ PB) (hQi : (q (σ i)).1 ∈ QB) :
    Equiv.Perm.sign
        (hPB.shoreEquiv.trans hQB.shoreEquiv.symm : Equiv.Perm XB) *
        (∏ e ∈ PB, S.edgeSign (A.starBEdge B r ell q σ e)) =
      ∏ e ∈ QB, S.edgeSign (A.starBEdge B r ell q σ e) := by
  let Pstar := starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hPi
  let Qstar := starGluedPM A B r ell p q σ PA QB i hPA hQB hAi hQi
  have hstar := S.relative_product_eq Pstar Qstar
  have hsign := starGluedPM_relativeSign_eq_sourceB
    A B r ell p q σ PA PB QB i hPA hPB hQB hAi hPi hQi
  have hstar' :
      Equiv.Perm.sign
          (hPB.shoreEquiv.trans hQB.shoreEquiv.symm : Equiv.Perm XB) *
          (∏ e ∈ A.starGluedMatching B r ell PA PB i, S.edgeSign e) =
        ∏ e ∈ A.starGluedMatching B r ell PA QB i, S.edgeSign e := by
    simpa [Pstar, Qstar] using hsign ▸ hstar
  exact sourceB_relativeProduct_of_commonStar
    A B r ell p q σ PA PB QB i hPA hPB hQB hAi hPi hQi
    S.edgeSign
    (Equiv.Perm.sign
      (hPB.shoreEquiv.trans hQB.shoreEquiv.symm : Equiv.Perm XB))
    hstar'

end BipartiteMultigraph
end BachThesisLean
