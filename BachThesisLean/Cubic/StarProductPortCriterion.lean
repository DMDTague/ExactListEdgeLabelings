import BachThesisLean.Cubic.StarProductFactorLift
import BachThesisLean.Cubic.StarProductFactorContract
import BachThesisLean.Cubic.TwoFactorRootComponent

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
# Star-product port criterion

The manuscript's boxed condition is an intersection between the edge-root mask
on the `A` side and the inverse image, under the bridge permutation, of the
vertex-root mask on the `B` side.  The theorem at the end of this file is the
full biconditional from Proposition `prop:star-port-criterion` of v13.23, in an
edge-copy-aware form.  In fact connectedness is not needed for the local
statement once the two factors are assumed cubic.
-/

/-- The finite port intersection appearing in Proposition
`prop:star-port-criterion` of v13.23. -/
noncomputable def starPortMaskIntersection
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : EA) (v : XB ⊕ YB) : Finset (Fin 3) := by
  classical
  exact A.edgeRootMask (.inr r) p e ∩
    Finset.univ.filter (fun i => σ i ∈ B.vertexRootMask (.inl ell) q v)

@[simp] theorem mem_starPortMaskIntersection
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : EA) (v : XB ⊕ YB) (i : Fin 3) :
    i ∈ A.starPortMaskIntersection B r ell p q σ e v ↔
      i ∈ A.edgeRootMask (.inr r) p e ∧
        σ i ∈ B.vertexRootMask (.inl ell) q v := by
  classical
  simp [starPortMaskIntersection]

/-- Contracting the canonical surviving `B` vertex back toward the `A` factor
lands at the deleted `A` root. -/
@[simp] theorem starAContract_starBVertexMap_of_ne
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (v : XB ⊕ YB) (hv : v ≠ (Sum.inl ell : XB ⊕ YB)) :
    starAContract r ell (A.starBVertexMap B r ell q v) = .inr r := by
  cases v with
  | inl x =>
      have hx : x ≠ ell := by
        intro h
        apply hv
        exact congrArg (fun z : XB => (Sum.inl z : XB ⊕ YB)) h
      simp [starBVertexMap, starAContract, hx]
  | inr y =>
      rfl

/-- Contracting the canonical surviving `B` vertex to the `B` factor recovers
that original vertex. -/
@[simp] theorem starBContract_starBVertexMap_of_ne
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (v : XB ⊕ YB) (hv : v ≠ (Sum.inl ell : XB ⊕ YB)) :
    starBContract r ell (A.starBVertexMap B r ell q v) = v := by
  cases v with
  | inl x =>
      have hx : x ≠ ell := by
        intro h
        apply hv
        exact congrArg (fun z : XB => (Sum.inl z : XB ⊕ YB)) h
      simp [starBVertexMap, starBContract, hx]
  | inr y =>
      rfl

/-- Constructive half of the manuscript's star-product port criterion.  Here
`e` is explicitly an edge copy surviving `A-r`, while `v` is explicitly not
the deleted `B` root.  A nonempty boxed port intersection produces an actual
perfect matching and a common complementary-factor component in the star
product. -/
theorem starEdgeVertexWitness_of_portMaskIntersection_nonempty
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    (e : {e : EA // A.right e ≠ r}) (v : XB ⊕ YB)
    (hvroot : v ≠ (Sum.inl ell : XB ⊕ YB))
    (hmask : (A.starPortMaskIntersection B r ell p q σ e.1 v).Nonempty) :
    (A.starProduct B r ell p q σ).EdgeVertexWitness
      (Sum.inl e : StarEdge A B r ell)
      (A.starBVertexMap B r ell q v) := by
  classical
  obtain ⟨i, hi⟩ := hmask
  have hi' := (A.mem_starPortMaskIntersection B r ell p q σ e.1 v i).1 hi
  obtain ⟨PA, hPA, hpi, heRoot⟩ :=
    (mem_edgeRootMask A (.inr r) p e.1 i).1 hi'.1
  obtain ⟨PB, hPB, hqi, hvRoot⟩ :=
    (mem_vertexRootMask B (.inl ell) q v (σ i)).1 hi'.2
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
  have heStar : (Sum.inl e : StarEdge A B r ell) ∈
      (A.starGluedMatching B r ell PA PB i)ᶜ := by
    rw [Finset.mem_compl]
    intro hePstar
    have hePA : e.1 ∈ PA :=
      (A.mem_starGluedMatching_aInternal B r ell PA PB i e).1 hePstar
    exact (Finset.mem_compl.mp heRoot.1) hePA
  have hjBCompl : (q (σ j)).1 ∈ PBᶜ :=
    (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)).2 hσji
  have hjBRoot : (q (σ j)).1 ∈ B.selectedIncident PBᶜ (.inl ell) :=
    (B.mem_selectedIncident PBᶜ (.inl ell) (q (σ j)).1).2
      ⟨hjBCompl, by simp [Incident]⟩
  have hBres :
      B.FactorReachable (B.factorDeleteRoot PBᶜ (.inl ell))
        (.inr (B.right (q (σ j)).1)) v := by
    rcases hTFB.factorDeleteLeftRoot_reaches_of_root_reachable
        hjBRoot hvRoot with hbad | hgood
    · exact (hvroot hbad).elim
    · exact hgood
  have hBlift :
      (A.starProduct B r ell p q σ).FactorReachable
        (A.starGluedMatching B r ell PA PB i)ᶜ
        (.inr (.inr (B.right (q (σ j)).1)))
        (A.starBVertexMap B r ell q v) := by
    simpa using
      (A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i hBres)
  have hbridge :=
    A.starBridge_compl_reachable B r ell p q σ PA PB i j hji
  refine ⟨A.starGluedMatching B r ell PA PB i,
    (.inl (.inl (A.left (p j).1)) :
      StarLeft XA XB ell ⊕ StarRight YA YB r),
    hPstar, ?_, ?_⟩
  · exact ⟨heStar, by simpa using hAlift⟩
  · exact hbridge.trans hBlift

/-- Converse half of the star-product port criterion.  Any cross-shore EVP
witness in the star product contracts to witnesses in both source factors,
forcing the unique selected bridge port into the boxed mask intersection. -/
theorem portMaskIntersection_nonempty_of_starEdgeVertexWitness
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic)
    (e : {e : EA // A.right e ≠ r}) (v : XB ⊕ YB)
    (hvroot : v ≠ (Sum.inl ell : XB ⊕ YB))
    (hEV : (A.starProduct B r ell p q σ).EdgeVertexWitness
      (Sum.inl e : StarEdge A B r ell)
      (A.starBVertexMap B r ell q v)) :
    (A.starPortMaskIntersection B r ell p q σ e.1 v).Nonempty := by
  classical
  rcases hEV with ⟨P, root, hP, heStar, hvStar⟩
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
  rw [hEq] at heStar hvStar
  have hcross :
      (A.starProduct B r ell p q σ).FactorReachable
        (A.starGluedMatching B r ell PA PB i)ᶜ
        (.inl (.inl (A.left e.1)))
        (A.starBVertexMap B r ell q v) := by
    simpa using heStar.2.symm.trans hvStar
  have hAc :=
    A.factorReachable_starAContract_of_glued_compl B r ell p q σ
      PA PB i hPA hpi hcross
  rw [A.starAContract_starBVertexMap_of_ne B r ell q v hvroot] at hAc
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
  rw [A.starBContract_starBVertexMap_of_ne B r ell q v hvroot] at hBc
  have hBroot : B.FactorReachable PBᶜ (.inl ell) v := by
    simpa [starBContract] using hBc
  have hiB : σ i ∈ B.vertexRootMask (.inl ell) q v :=
    (mem_vertexRootMask B (.inl ell) q v (σ i)).2
      ⟨PB, hPB, hqi, hBroot⟩
  exact ⟨i, (A.mem_starPortMaskIntersection B r ell p q σ e.1 v i).2
    ⟨hiA, hiB⟩⟩

/-- Full edge-copy form of the manuscript's boxed star-product port criterion.
The cross-shore pair has an EVP witness exactly when
`S_A(e,r) ∩ σ⁻¹(T_B(v,ell))` is nonempty. -/
theorem starEdgeVertexWitness_iff_portMaskIntersection_nonempty
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic)
    (e : {e : EA // A.right e ≠ r}) (v : XB ⊕ YB)
    (hvroot : v ≠ (Sum.inl ell : XB ⊕ YB)) :
    (A.starProduct B r ell p q σ).EdgeVertexWitness
        (Sum.inl e : StarEdge A B r ell)
        (A.starBVertexMap B r ell q v) ↔
      (A.starPortMaskIntersection B r ell p q σ e.1 v).Nonempty := by
  constructor
  · exact A.portMaskIntersection_nonempty_of_starEdgeVertexWitness
      B r ell p q σ hA e v hvroot
  · exact A.starEdgeVertexWitness_of_portMaskIntersection_nonempty
      B r ell p q σ hA hB e v hvroot

end BipartiteMultigraph
end BachThesisLean
