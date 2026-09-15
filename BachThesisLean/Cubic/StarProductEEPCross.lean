import BachThesisLean.Cubic.StarProductEdgePairCriterion
import BachThesisLean.Cubic.FinThreeIntersection

namespace BachThesisLean
namespace BipartiteMultigraph

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-!
# Cross-shore EEP gluing

If both factors have EEP, every surviving edge on either side has at least two
admissible root ports.  Two size-two subsets of three ports intersect after
any bridge permutation, and the cross-shore edge-pair criterion then glues the
corresponding source witnesses.
-/

/-- Under EEP on both factors, the two source edge-root masks have a common
bridge port after the star permutation. -/
theorem starEdgeMaskIntersection_nonempty_of_hasEEP
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hEA : A.HasEEP) (hEB : B.HasEEP)
    (e : {e : EA // A.right e ≠ r})
    (f : {f : EB // B.left f ≠ ell}) :
    (A.starEdgeMaskIntersection B r ell p q σ e.1 f.1).Nonempty := by
  have hAcard : 2 ≤ (A.edgeRootMask (.inr r) p e.1).card :=
    hEA.edgeRootMask_card_ge_two (.inr r) p e.1 (by
      simpa [Incident] using e.2)
  have hBcard : 2 ≤ (B.edgeRootMask (.inl ell) q f.1).card :=
    hEB.edgeRootMask_card_ge_two (.inl ell) q f.1 (by
      simpa [Incident] using f.2)
  have hinter := finThree_inter_permPreimage_nonempty_of_card_ge_two σ
    (A.edgeRootMask (.inr r) p e.1)
    (B.edgeRootMask (.inl ell) q f.1) hAcard hBcard
  simpa [starEdgeMaskIntersection, finThreePermPreimage] using hinter

/-- EEP on the two source factors glues every pair of surviving cross-shore
edges into a common complementary component of the star product. -/
theorem starCrossEdgePairWitness_of_hasEEP
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    (hEA : A.HasEEP) (hEB : B.HasEEP)
    (e : {e : EA // A.right e ≠ r})
    (f : {f : EB // B.left f ≠ ell}) :
    (A.starProduct B r ell p q σ).EdgePairWitness
      (Sum.inl e : StarEdge A B r ell)
      (Sum.inr (Sum.inl f) : StarEdge A B r ell) := by
  apply (A.starCrossEdgePairWitness_iff_edgeMaskIntersection_nonempty
    B r ell p q σ hA hB e f).2
  exact A.starEdgeMaskIntersection_nonempty_of_hasEEP B r ell p q σ
    hEA hEB e f

end BipartiteMultigraph
end BachThesisLean
