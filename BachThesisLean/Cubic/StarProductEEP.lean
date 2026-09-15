import BachThesisLean.Cubic.StarProductEEPProjection
import BachThesisLean.Cubic.StarProductEEPCross
import BachThesisLean.Cubic.StarProductEEPSameA
import BachThesisLean.Cubic.StarProductEEPSameB

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
# EEP invariance for a cubic star product

This assembles the matching decomposition, source-component projection,
same-side path lifting, and cross-shore port-intersection criterion.  It is the
explicit 3-edge-sum form of the manuscript's tight-cut EEP invariance theorem.
-/

/-- Edge-pair witnesses are symmetric in their two distinguished edges. -/
theorem EdgePairWitness.swap
    {G : BipartiteMultigraph XA YA EA} {e f : EA}
    (h : G.EdgePairWitness e f) : G.EdgePairWitness f e := by
  rcases h with ⟨P, root, hP, he, hf⟩
  exact ⟨P, root, hP, hf, he⟩

/-- EEP on both cubic factors implies EEP on their star product. -/
theorem starProduct_hasEEP_of_factors
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    (hEA : A.HasEEP) (hEB : B.HasEEP) :
    (A.starProduct B r ell p q σ).HasEEP := by
  classical
  intro s t hst
  change (A.starProduct B r ell p q σ).EdgePairWitness s t
  rcases s with ea | srest
  · rcases t with fa | trest
    · have hef : ea.1 ≠ fa.1 := by
        intro h
        apply hst
        exact congrArg Sum.inl (Subtype.ext h)
      have hsrc := hEA ea.1 fa.1 hef
      have hlift := A.starAEdgePairWitness_of_source B r ell p q σ hA hB hsrc
      simpa [starAEdge, ea.2, fa.2] using hlift
    · rcases trest with fb | j
      · exact A.starCrossEdgePairWitness_of_hasEEP B r ell p q σ
          hA hB hEA hEB ea fb
      · have hef : ea.1 ≠ (p j).1 := by
          intro h
          apply ea.2
          rw [h]
          exact A.port_right_eq r p j
        have hsrc := hEA ea.1 (p j).1 hef
        have hlift := A.starAEdgePairWitness_of_source B r ell p q σ hA hB hsrc
        simpa [starAEdge, ea.2] using hlift
  · rcases srest with eb | i
    · rcases t with fa | trest
      · have hcross := A.starCrossEdgePairWitness_of_hasEEP B r ell p q σ
          hA hB hEA hEB fa eb
        exact hcross.swap
      · rcases trest with fb | j
        · have hef : eb.1 ≠ fb.1 := by
            intro h
            apply hst
            exact congrArg (fun z => Sum.inr (Sum.inl z)) (Subtype.ext h)
          have hsrc := hEB eb.1 fb.1 hef
          have hlift := A.starBEdgePairWitness_of_source B r ell p q σ hA hB hsrc
          simpa [starBEdge, eb.2, fb.2] using hlift
        · have hef : eb.1 ≠ (q (σ j)).1 := by
            intro h
            apply eb.2
            rw [h]
            exact B.port_left_eq ell q (σ j)
          have hsrc := hEB eb.1 (q (σ j)).1 hef
          have hlift := A.starBEdgePairWitness_of_source B r ell p q σ hA hB hsrc
          simpa [starBEdge, eb.2] using hlift
    · rcases t with fa | trest
      · have hef : (p i).1 ≠ fa.1 := by
          intro h
          apply fa.2
          rw [← h]
          exact A.port_right_eq r p i
        have hsrc := hEA (p i).1 fa.1 hef
        have hlift := A.starAEdgePairWitness_of_source B r ell p q σ hA hB hsrc
        simpa [starAEdge, fa.2] using hlift
      · rcases trest with fb | j
        · have hef : (q (σ i)).1 ≠ fb.1 := by
            intro h
            apply fb.2
            rw [← h]
            exact B.port_left_eq ell q (σ i)
          have hsrc := hEB (q (σ i)).1 fb.1 hef
          have hlift := A.starBEdgePairWitness_of_source B r ell p q σ hA hB hsrc
          simpa [starBEdge, fb.2] using hlift
        · have hij : i ≠ j := by
            intro h
            apply hst
            subst j
            rfl
          have hpne : (p i).1 ≠ (p j).1 := by
            intro h
            apply hij
            apply p.injective
            exact Subtype.ext h
          have hsrc := hEA (p i).1 (p j).1 hpne
          have hlift := A.starAEdgePairWitness_of_source B r ell p q σ hA hB hsrc
          simpa using hlift

/-- Full EEP invariance for an explicit cubic star product. -/
theorem starProduct_hasEEP_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic) :
    (A.starProduct B r ell p q σ).HasEEP ↔ A.HasEEP ∧ B.HasEEP := by
  constructor
  · intro hStar
    exact ⟨hStar.of_starProduct_left A B r ell p q σ hA,
      hStar.of_starProduct_right A B r ell p q σ hA⟩
  · rintro ⟨hEA, hEB⟩
    exact A.starProduct_hasEEP_of_factors B r ell p q σ hA hB hEA hEB

end BipartiteMultigraph
end BachThesisLean
