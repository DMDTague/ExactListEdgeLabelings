import BachThesisLean.Cubic.StarProductEEP

namespace BachThesisLean
namespace BipartiteMultigraph

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-! The 2EP companion to star-product EEP invariance. -/

/-- Since EEP and 2EP are equivalent in cubic graphs, star-product EEP
invariance immediately yields star-product 2EP invariance. -/
theorem starProduct_hasTwoEP_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic) :
    (A.starProduct B r ell p q σ).HasTwoEP ↔ A.HasTwoEP ∧ B.HasTwoEP := by
  have hStar : (A.starProduct B r ell p q σ).IsCubic :=
    A.starProduct_isCubic B r ell p q σ hA hB
  rw [← hasEEP_iff_hasTwoEP (A.starProduct B r ell p q σ) hStar,
    ← hasEEP_iff_hasTwoEP A hA, ← hasEEP_iff_hasTwoEP B hB]
  exact A.starProduct_hasEEP_iff B r ell p q σ hA hB

end BipartiteMultigraph
end BachThesisLean
