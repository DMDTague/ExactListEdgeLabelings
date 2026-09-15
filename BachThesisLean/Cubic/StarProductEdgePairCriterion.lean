import BachThesisLean.Cubic.StarProductPortCriterion

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
# Cross-shore edge-pair criterion for a star product

This is the edge--edge companion to the manuscript's star-product EVP
criterion.  It is the gluing statement needed for EEP across a cubic 3-edge
sum: two surviving source edges lie on one complementary star component
exactly when the selected bridge port is admissible in both source edge-root
masks.
-/

/-- The common-port set for a surviving `A` edge and a surviving `B` edge. -/
noncomputable def starEdgeMaskIntersection
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : EA) (f : EB) : Finset (Fin 3) := by
  classical
  exact A.edgeRootMask (.inr r) p e ∩
    Finset.univ.filter (fun i => σ i ∈ B.edgeRootMask (.inl ell) q f)

@[simp] theorem mem_starEdgeMaskIntersection
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : EA) (f : EB) (i : Fin 3) :
    i ∈ A.starEdgeMaskIntersection B r ell p q σ e f ↔
      i ∈ A.edgeRootMask (.inr r) p e ∧
        σ i ∈ B.edgeRootMask (.inl ell) q f := by
  classical
  simp [starEdgeMaskIntersection]

/-- A common admissible port produces an actual complementary component
containing the two surviving cross-shore edge copies. -/
theorem starCrossEdgePairWitness_of_edgeMaskIntersection_nonempty
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    (e : {e : EA // A.right e ≠ r})
    (f : {f : EB // B.left f ≠ ell})
    (hmask : (A.starEdgeMaskIntersection B r ell p q σ e.1 f.1).Nonempty) :
    (A.starProduct B r ell p q σ).EdgePairWitness
      (Sum.inl e : StarEdge A B r ell)
      (Sum.inr (Sum.inl f) : StarEdge A B r ell) := by
  classical
  obtain ⟨i, hi⟩ := hmask
  have hi' := (A.mem_starEdgeMaskIntersection B r ell p q σ e.1 f.1 i).1 hi
  obtain ⟨PA, hPA, hpi, heRoot⟩ :=
    (mem_edgeRootMask A (.inr r) p e.1 i).1 hi'.1
  obtain ⟨PB, hPB, hqi, hfRoot⟩ :=
    (mem_edgeRootMask B (.inl ell) q f.1 (σ i)).1 hi'.2
  have hPstar :
      (A.starProduct B r ell p q σ).IsPerfectMatching
        (A.starGluedMatching B r ell PA PB i) :=
    A.starGluedMatching_isPerfectMatching B r ell p q σ
      PA PB i hPA hPB hpi hqi
  have hTFA : A.IsTwoFactor PAᶜ :=
    (A.perfectMatching_compl_iff_twoFactor hA PA).1 hPA
  have hTFB : B.IsTwoFactor PBᶜ :=
    (B.perfectMatching_compl_iff_twoFactor hB PB).1 hPB
  have hlt : 1 < (Finset.univ : Finset (Fin 3)).card := by decide
  obtain ⟨j, _hj, hji⟩ := Finset.exists_mem_ne hlt i
  have hσji : σ j ≠ σ i := fun h => hji (σ.injective h)
  have hjACompl : (p j).1 ∈ PAᶜ :=
    (hPA.port_mem_compl_iff_ne A (.inr r) p i hpi j).2 hji
  have hjARoot : (p j).1 ∈ A.selectedIncident PAᶜ (.inr r) :=
    (A.mem_selectedIncident PAᶜ (.inr r) (p j).1).2
      ⟨hjACompl, by simp [Incident]⟩
  have hAres :
      A.FactorReachable (A.factorDeleteRoot PAᶜ (.inr r))
        (.inl (A.left (p j).1)) (.inl (A.left e.1)) := by
    rcases hTFA.factorDeleteRightRoot_reaches_of_root_reachable
        hjARoot heRoot.2 with hbad | hgood
    · cases hbad
    · exact hgood
  have hAlift :
      (A.starProduct B r ell p q σ).FactorReachable
        (A.starGluedMatching B r ell PA PB i)ᶜ
        (.inl (.inl (A.left (p j).1)))
        (.inl (.inl (A.left e.1))) := by
    simpa using
      (A.factorReachable_starA_of_factorDeleteRoot B r ell p q σ PA PB i hAres)
  have hjBCompl : (q (σ j)).1 ∈ PBᶜ :=
    (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)).2 hσji
  have hjBRoot : (q (σ j)).1 ∈ B.selectedIncident PBᶜ (.inl ell) :=
    (B.mem_selectedIncident PBᶜ (.inl ell) (q (σ j)).1).2
      ⟨hjBCompl, by simp [Incident]⟩
  have hBres :
      B.FactorReachable (B.factorDeleteRoot PBᶜ (.inl ell))
        (.inr (B.right (q (σ j)).1)) (.inl (B.left f.1)) := by
    rcases hTFB.factorDeleteLeftRoot_reaches_of_root_reachable
        hjBRoot hfRoot.2 with hbad | hgood
    · exact (f.2 (Sum.inl.inj hbad)).elim
    · exact hgood
  have hBlift :
      (A.starProduct B r ell p q σ).FactorReachable
        (A.starGluedMatching B r ell PA PB i)ᶜ
        (.inr (.inr (B.right (q (σ j)).1)))
        (.inl (.inr ⟨B.left f.1, f.2⟩)) := by
    simpa [starBVertexMap, f.2] using
      (A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i hBres)
  have heStar : (Sum.inl e : StarEdge A B r ell) ∈
      (A.starGluedMatching B r ell PA PB i)ᶜ := by
    rw [Finset.mem_compl]
    intro hePstar
    have hePA : e.1 ∈ PA :=
      (A.mem_starGluedMatching_aInternal B r ell PA PB i e).1 hePstar
    exact (Finset.mem_compl.mp heRoot.1) hePA
  have hfStar : (Sum.inr (Sum.inl f) : StarEdge A B r ell) ∈
      (A.starGluedMatching B r ell PA PB i)ᶜ := by
    rw [Finset.mem_compl]
    intro hfPstar
    have hfPB : f.1 ∈ PB :=
      (A.mem_starGluedMatching_bInternal B r ell PA PB i f).1 hfPstar
    exact (Finset.mem_compl.mp hfRoot.1) hfPB
  have hbridge :=
    A.starBridge_compl_reachable B r ell p q σ PA PB i j hji
  refine ⟨A.starGluedMatching B r ell PA PB i,
    (.inl (.inl (A.left (p j).1)) :
      StarLeft XA XB ell ⊕ StarRight YA YB r),
    hPstar, ?_, ?_⟩
  · exact ⟨heStar, by simpa using hAlift⟩
  · exact ⟨hfStar, by simpa using hbridge.trans hBlift⟩

/-- Conversely, a cross-shore common factor component contracts to source
edge-root witnesses at the unique selected bridge port. -/
theorem edgeMaskIntersection_nonempty_of_starCrossEdgePairWitness
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic)
    (e : {e : EA // A.right e ≠ r})
    (f : {f : EB // B.left f ≠ ell})
    (hpair : (A.starProduct B r ell p q σ).EdgePairWitness
      (Sum.inl e : StarEdge A B r ell)
      (Sum.inr (Sum.inl f) : StarEdge A B r ell)) :
    (A.starEdgeMaskIntersection B r ell p q σ e.1 f.1).Nonempty := by
  classical
  rcases hpair with ⟨P, root, hP, heStar, hfStar⟩
  obtain ⟨i, hPAraw, hPBraw, hpiraw, hqiraw, hEqraw⟩ :=
    hP.starMatchingDecomposition A B r ell p q σ hA
  let PA := A.starRestrictedA B r ell p P
  let PB := A.starRestrictedB B r ell q σ P
  have hPA : A.IsPerfectMatching PA := by simpa [PA] using hPAraw
  have hPB : B.IsPerfectMatching PB := by simpa [PB] using hPBraw
  have hpi : (p i).1 ∈ PA := by simpa [PA] using hpiraw
  have hqi : (q (σ i)).1 ∈ PB := by simpa [PB] using hqiraw
  have hEq : P = A.starGluedMatching B r ell PA PB i := by
    simpa [PA, PB] using hEqraw
  rw [hEq] at heStar hfStar
  have hcross :
      (A.starProduct B r ell p q σ).FactorReachable
        (A.starGluedMatching B r ell PA PB i)ᶜ
        (.inl (.inl (A.left e.1)))
        (.inl (.inr ⟨B.left f.1, f.2⟩)) := by
    simpa using heStar.2.symm.trans hfStar.2
  have hAc :=
    A.factorReachable_starAContract_of_glued_compl B r ell p q σ
      PA PB i hPA hpi hcross
  have hAroot :
      A.FactorReachable PAᶜ (.inr r) (.inl (A.left e.1)) := by
    have hAc' :
        A.FactorReachable PAᶜ (.inl (A.left e.1)) (.inr r) := by
      simpa [starAContract] using hAc
    exact hAc'.symm
  have hePAc : e.1 ∈ PAᶜ := by
    rw [Finset.mem_compl]
    intro hePA
    exact (Finset.mem_compl.mp heStar.1)
      ((A.mem_starGluedMatching_aInternal B r ell PA PB i e).2 hePA)
  have hiA : i ∈ A.edgeRootMask (.inr r) p e.1 :=
    (mem_edgeRootMask A (.inr r) p e.1 i).2
      ⟨PA, hPA, hpi, ⟨hePAc, hAroot⟩⟩
  have hBc :=
    A.factorReachable_starBContract_of_glued_compl B r ell p q σ
      PA PB i hPB hqi hcross
  have hBroot :
      B.FactorReachable PBᶜ (.inl ell) (.inl (B.left f.1)) := by
    simpa [starBContract] using hBc
  have hfPBc : f.1 ∈ PBᶜ := by
    rw [Finset.mem_compl]
    intro hfPB
    exact (Finset.mem_compl.mp hfStar.1)
      ((A.mem_starGluedMatching_bInternal B r ell PA PB i f).2 hfPB)
  have hiB : σ i ∈ B.edgeRootMask (.inl ell) q f.1 :=
    (mem_edgeRootMask B (.inl ell) q f.1 (σ i)).2
      ⟨PB, hPB, hqi, ⟨hfPBc, hBroot⟩⟩
  exact ⟨i, (A.mem_starEdgeMaskIntersection B r ell p q σ e.1 f.1 i).2
    ⟨hiA, hiB⟩⟩

/-- Full cross-shore edge-pair port criterion. -/
theorem starCrossEdgePairWitness_iff_edgeMaskIntersection_nonempty
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    (e : {e : EA // A.right e ≠ r})
    (f : {f : EB // B.left f ≠ ell}) :
    (A.starProduct B r ell p q σ).EdgePairWitness
        (Sum.inl e : StarEdge A B r ell)
        (Sum.inr (Sum.inl f) : StarEdge A B r ell) ↔
      (A.starEdgeMaskIntersection B r ell p q σ e.1 f.1).Nonempty := by
  constructor
  · exact A.edgeMaskIntersection_nonempty_of_starCrossEdgePairWitness
      B r ell p q σ hA e f
  · exact A.starCrossEdgePairWitness_of_edgeMaskIntersection_nonempty
      B r ell p q σ hA hB e f

end BipartiteMultigraph
end BachThesisLean
