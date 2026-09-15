import BachThesisLean.Cubic.StarProductSourceMembership
import BachThesisLean.Cubic.RootDeletionPersistence
import BachThesisLean.Cubic.StarProductFactorLift
import BachThesisLean.Cubic.MatchingCovered

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
# Lifting same-side `B` EEP witnesses through a star product

For the factor whose deleted root lies on the left shore, it is convenient to
carry paths to the right endpoint of each source edge.  That endpoint always
survives root deletion, including when the source edge itself is a root port;
the transported star edge then supplies the final step back to its left
endpoint, as required by `ComponentCarries`.
-/

/-- A common complementary-component witness for two `B` edges lifts to the
corresponding transported edges of the star product. -/
theorem starBEdgePairWitness_of_source
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    {e f : EB} (hpair : B.EdgePairWitness e f) :
    (A.starProduct B r ell p q σ).EdgePairWitness
      (A.starBEdge B r ell q σ e) (A.starBEdge B r ell q σ f) := by
  classical
  rcases hpair with ⟨PB, root, hPB, he, hf⟩
  obtain ⟨k, hqk, _huniq⟩ := hPB.existsUnique_port (.inl ell) q
  let i : Fin 3 := σ.symm k
  have hqi : (q (σ i)).1 ∈ PB := by
    simpa [i] using hqk
  obtain ⟨PA, hPA, hpi⟩ :=
    A.exists_perfectMatching_containing_edge_of_cubic hA (p i).1
  let Pstar := A.starGluedMatching B r ell PA PB i
  have hPstar : (A.starProduct B r ell p q σ).IsPerfectMatching Pstar := by
    simpa [Pstar] using
      A.starGluedMatching_isPerfectMatching B r ell p q σ
        PA PB i hPA hPB hpi hqi
  have heStar : A.starBEdge B r ell q σ e ∈ Pstarᶜ := by
    simpa [Pstar] using
      (A.starBEdge_mem_starGluedMatching_compl_iff
        B r ell q σ PA PB i hPB hqi e).2 he.1
  have hfStar : A.starBEdge B r ell q σ f ∈ Pstarᶜ := by
    simpa [Pstar] using
      (A.starBEdge_mem_starGluedMatching_compl_iff
        B r ell q σ PA PB i hPB hqi f).2 hf.1
  have heRight : B.FactorReachable PBᶜ root (.inr (B.right e)) :=
    he.2.trans (B.factorReachable_endpoints he.1)
  have hfRight : B.FactorReachable PBᶜ root (.inr (B.right f)) :=
    hf.2.trans (B.factorReachable_endpoints hf.1)
  have heStarBack :
      (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
        (.inr ((A.starProduct B r ell p q σ).right
          (A.starBEdge B r ell q σ e)))
        (.inl ((A.starProduct B r ell p q σ).left
          (A.starBEdge B r ell q σ e))) := by
    exact ((A.starProduct B r ell p q σ).factorReachable_endpoints heStar).symm
  have hfStarBack :
      (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
        (.inr ((A.starProduct B r ell p q σ).right
          (A.starBEdge B r ell q σ f)))
        (.inl ((A.starProduct B r ell p q σ).left
          (A.starBEdge B r ell q σ f))) := by
    exact ((A.starProduct B r ell p q σ).factorReachable_endpoints hfStar).symm
  by_cases hroot : B.FactorReachable PBᶜ root (.inl ell)
  · have hTF : B.IsTwoFactor PBᶜ :=
      (B.perfectMatching_compl_iff_twoFactor hB PB).1 hPB
    have hlt : 1 < (Finset.univ : Finset (Fin 3)).card := by decide
    obtain ⟨j, _hj, hji⟩ := Finset.exists_mem_ne hlt i
    have hσji : σ j ≠ σ i := fun h => hji (σ.injective h)
    have hjc : (q (σ j)).1 ∈ PBᶜ :=
      (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)).2 hσji
    have hjroot : (q (σ j)).1 ∈ B.selectedIncident PBᶜ (.inl ell) :=
      (B.mem_selectedIncident PBᶜ (.inl ell) (q (σ j)).1).2
        ⟨hjc, by simp [Incident]⟩
    have hre : B.FactorReachable PBᶜ (.inl ell) (.inr (B.right e)) :=
      hroot.symm.trans heRight
    have hrf : B.FactorReachable PBᶜ (.inl ell) (.inr (B.right f)) :=
      hroot.symm.trans hfRight
    have heDel :
        B.FactorReachable (B.factorDeleteRoot PBᶜ (.inl ell))
          (.inr (B.right (q (σ j)).1)) (.inr (B.right e)) := by
      rcases hTF.factorDeleteLeftRoot_reaches_of_root_reachable
          hjroot hre with hbad | hgood
      · cases hbad
      · exact hgood
    have hfDel :
        B.FactorReachable (B.factorDeleteRoot PBᶜ (.inl ell))
          (.inr (B.right (q (σ j)).1)) (.inr (B.right f)) := by
      rcases hTF.factorDeleteLeftRoot_reaches_of_root_reachable
          hjroot hrf with hbad | hgood
      · cases hbad
      · exact hgood
    have heLift :=
      A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i heDel
    have hfLift :=
      A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i hfDel
    have heCarry :
        (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
          (.inr (.inr (B.right (q (σ j)).1)))
          (.inl ((A.starProduct B r ell p q σ).left
            (A.starBEdge B r ell q σ e))) := by
      have heLift' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (.inr (.inr (B.right (q (σ j)).1)))
            (.inr (.inr (B.right e))) := by
        simpa [Pstar] using heLift
      have heBack' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (.inr (.inr (B.right e)))
            (.inl ((A.starProduct B r ell p q σ).left
              (A.starBEdge B r ell q σ e))) := by
        simpa using heStarBack
      exact heLift'.trans heBack'
    have hfCarry :
        (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
          (.inr (.inr (B.right (q (σ j)).1)))
          (.inl ((A.starProduct B r ell p q σ).left
            (A.starBEdge B r ell q σ f))) := by
      have hfLift' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (.inr (.inr (B.right (q (σ j)).1)))
            (.inr (.inr (B.right f))) := by
        simpa [Pstar] using hfLift
      have hfBack' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (.inr (.inr (B.right f)))
            (.inl ((A.starProduct B r ell p q σ).left
              (A.starBEdge B r ell q σ f))) := by
        simpa using hfStarBack
      exact hfLift'.trans hfBack'
    exact ⟨Pstar,
      (.inr (.inr (B.right (q (σ j)).1)) :
        StarLeft XA XB ell ⊕ StarRight YA YB r),
      hPstar, ⟨heStar, heCarry⟩, ⟨hfStar, hfCarry⟩⟩
  · have heDel := heRight.factorDeleteRoot_of_not_reaches_root hroot
    have hfDel := hfRight.factorDeleteRoot_of_not_reaches_root hroot
    have heLift :=
      A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i heDel
    have hfLift :=
      A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i hfDel
    have heCarry :
        (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
          (A.starBVertexMap B r ell q root)
          (.inl ((A.starProduct B r ell p q σ).left
            (A.starBEdge B r ell q σ e))) := by
      have heLift' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (A.starBVertexMap B r ell q root)
            (.inr (.inr (B.right e))) := by
        simpa [Pstar] using heLift
      have heBack' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (.inr (.inr (B.right e)))
            (.inl ((A.starProduct B r ell p q σ).left
              (A.starBEdge B r ell q σ e))) := by
        simpa using heStarBack
      exact heLift'.trans heBack'
    have hfCarry :
        (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
          (A.starBVertexMap B r ell q root)
          (.inl ((A.starProduct B r ell p q σ).left
            (A.starBEdge B r ell q σ f))) := by
      have hfLift' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (A.starBVertexMap B r ell q root)
            (.inr (.inr (B.right f))) := by
        simpa [Pstar] using hfLift
      have hfBack' :
          (A.starProduct B r ell p q σ).FactorReachable Pstarᶜ
            (.inr (.inr (B.right f)))
            (.inl ((A.starProduct B r ell p q σ).left
              (A.starBEdge B r ell q σ f))) := by
        simpa using hfStarBack
      exact hfLift'.trans hfBack'
    exact ⟨Pstar, A.starBVertexMap B r ell q root,
      hPstar, ⟨heStar, heCarry⟩, ⟨hfStar, hfCarry⟩⟩

end BipartiteMultigraph
end BachThesisLean
