import BachThesisLean.Cubic.StarProductPfaffianProduct
import BachThesisLean.Cubic.StarProductPfaffianRelativeB

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
# Edge-sign cancellation for common A-factor completion

The bridge-corrected product factorization is already symmetric in the two
source factors.  Holding the `A` matching fixed and varying two same-port `B`
matchings therefore cancels the common `A` product and the common bridge,
leaving exactly the relative edge-product equation on `B`.
-/

/-- If a relative product equation holds for two same-port star matchings with
a common `A` completion, it descends to the varying `B` factor. -/
theorem sourceB_relativeProduct_of_commonStar
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB QB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hQB : B.IsPerfectMatching QB)
    (hAi : (p i).1 ∈ PA)
    (hPi : (q (σ i)).1 ∈ PB) (hQi : (q (σ i)).1 ∈ QB)
    (edgeSign : StarEdge A B r ell → ℤˣ) (c : ℤˣ)
    (hstar :
      c * (∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e) =
        ∏ e ∈ A.starGluedMatching B r ell PA QB i, edgeSign e) :
    c * (∏ e ∈ PB, edgeSign (A.starBEdge B r ell q σ e)) =
      ∏ e ∈ QB, edgeSign (A.starBEdge B r ell q σ e) := by
  classical
  let commonA := ∏ e ∈ PA, edgeSign (A.starAEdge B r ell p e)
  have hprodP := starGluedMatching_prod_mul_bridge
    A B r ell p q σ PA PB i hPA hPB hAi hPi edgeSign
  have hprodQ := starGluedMatching_prod_mul_bridge
    A B r ell p q σ PA QB i hPA hQB hAi hQi edgeSign
  apply mul_left_cancel (a := commonA)
  calc
    commonA * (c * (∏ e ∈ PB, edgeSign (A.starBEdge B r ell q σ e))) =
        c * (commonA * ∏ e ∈ PB, edgeSign (A.starBEdge B r ell q σ e)) := by
          ac_rfl
    _ = c * ((∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e) *
          edgeSign (Sum.inr (Sum.inr i))) := by
          rw [hprodP]
    _ = (c * (∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e)) *
          edgeSign (Sum.inr (Sum.inr i)) := by
          simp [mul_assoc]
    _ = (∏ e ∈ A.starGluedMatching B r ell PA QB i, edgeSign e) *
          edgeSign (Sum.inr (Sum.inr i)) := by rw [hstar]
    _ = commonA * ∏ e ∈ QB, edgeSign (A.starBEdge B r ell q σ e) := hprodQ

end BipartiteMultigraph
end BachThesisLean
