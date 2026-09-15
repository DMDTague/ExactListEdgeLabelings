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
# Lifting same-side `A` EEP witnesses through a star product

A source witness either lies in a complementary component disjoint from the
deleted root, in which case it survives root deletion unchanged, or lies in
the root component, in which case the opened two-factor path is reached from
any unused port.  In both cases the residual path lifts into the glued star
complement.
-/

/-- A common complementary-component witness for two `A` edges lifts to the
corresponding two transported edges of the star product. -/
theorem starAEdgePairWitness_of_source
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    {e f : EA} (hpair : A.EdgePairWitness e f) :
    (A.starProduct B r ell p q σ).EdgePairWitness
      (A.starAEdge B r ell p e) (A.starAEdge B r ell p f) := by
  classical
  rcases hpair with ⟨PA, root, hPA, he, hf⟩
  obtain ⟨i, hpi, _huniq⟩ := hPA.existsUnique_port (.inr r) p
  obtain ⟨PB, hPB, hqi⟩ :=
    B.exists_perfectMatching_containing_edge_of_cubic hB (q (σ i)).1
  let Pstar := A.starGluedMatching B r ell PA PB i
  have hPstar : (A.starProduct B r ell p q σ).IsPerfectMatching Pstar := by
    simpa [Pstar] using
      A.starGluedMatching_isPerfectMatching B r ell p q σ
        PA PB i hPA hPB hpi hqi
  have heStar : A.starAEdge B r ell p e ∈ Pstarᶜ := by
    simpa [Pstar] using
      (A.starAEdge_mem_starGluedMatching_compl_iff
        B r ell p PA PB i hPA hpi e).2 he.1
  have hfStar : A.starAEdge B r ell p f ∈ Pstarᶜ := by
    simpa [Pstar] using
      (A.starAEdge_mem_starGluedMatching_compl_iff
        B r ell p PA PB i hPA hpi f).2 hf.1
  by_cases hroot : A.FactorReachable PAᶜ root (.inr r)
  · have hTF : A.IsTwoFactor PAᶜ :=
      (A.perfectMatching_compl_iff_twoFactor hA PA).1 hPA
    have hlt : 1 < (Finset.univ : Finset (Fin 3)).card := by decide
    obtain ⟨j, _hj, hji⟩ := Finset.exists_mem_ne hlt i
    have hjc : (p j).1 ∈ PAᶜ :=
      (hPA.port_mem_compl_iff_ne A (.inr r) p i hpi j).2 hji
    have hjroot : (p j).1 ∈ A.selectedIncident PAᶜ (.inr r) :=
      (A.mem_selectedIncident PAᶜ (.inr r) (p j).1).2
        ⟨hjc, by simp [Incident]⟩
    have hre : A.FactorReachable PAᶜ (.inr r) (.inl (A.left e)) :=
      hroot.symm.trans he.2
    have hrf : A.FactorReachable PAᶜ (.inr r) (.inl (A.left f)) :=
      hroot.symm.trans hf.2
    have heDel :
        A.FactorReachable (A.factorDeleteRoot PAᶜ (.inr r))
          (.inl (A.left (p j).1)) (.inl (A.left e)) := by
      rcases hTF.factorDeleteRightRoot_reaches_of_root_reachable
          hjroot hre with hbad | hgood
      · cases hbad
      · exact hgood
    have hfDel :
        A.FactorReachable (A.factorDeleteRoot PAᶜ (.inr r))
          (.inl (A.left (p j).1)) (.inl (A.left f)) := by
      rcases hTF.factorDeleteRightRoot_reaches_of_root_reachable
          hjroot hrf with hbad | hgood
      · cases hbad
      · exact hgood
    have heLift :=
      A.factorReachable_starA_of_factorDeleteRoot B r ell p q σ PA PB i heDel
    have hfLift :=
      A.factorReachable_starA_of_factorDeleteRoot B r ell p q σ PA PB i hfDel
    refine ⟨Pstar,
      (.inl (.inl (A.left (p j).1)) :
        StarLeft XA XB ell ⊕ StarRight YA YB r),
      hPstar, ⟨heStar, ?_⟩, ⟨hfStar, ?_⟩⟩
    · simpa [Pstar] using heLift
    · simpa [Pstar] using hfLift
  · have heDel := he.2.factorDeleteRoot_of_not_reaches_root hroot
    have hfDel := hf.2.factorDeleteRoot_of_not_reaches_root hroot
    have heLift :=
      A.factorReachable_starA_of_factorDeleteRoot B r ell p q σ PA PB i heDel
    have hfLift :=
      A.factorReachable_starA_of_factorDeleteRoot B r ell p q σ PA PB i hfDel
    refine ⟨Pstar, A.starAVertexMap B r ell p root,
      hPstar, ⟨heStar, ?_⟩, ⟨hfStar, ?_⟩⟩
    · simpa [Pstar] using heLift
    · simpa [Pstar] using hfLift

end BipartiteMultigraph
end BachThesisLean
