import BachThesisLean.Cubic.StarProductEdgePairCriterion

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
# Projecting EEP from a star product

A complementary component witness in a star product contracts to a witness in
each source factor.  This is the projection half of tight-cut/3-edge-sum EEP
invariance, stated first for the explicit star-product model.
-/

/-- Contracting the left endpoint of a transported `B` edge recovers the
original `B` left endpoint, including the root-edge/bridge case. -/
@[simp] theorem starBContract_left_starBEdge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : EB) :
    starBContract r ell
      (.inl ((A.starProduct B r ell p q σ).left
        (A.starBEdge B r ell q σ e))) =
      (.inl (B.left e) : XB ⊕ YB) := by
  classical
  by_cases h : B.left e = ell
  · simp [starBEdge, starProduct, starBContract, h]
  · simp [starBEdge, starProduct, starBContract, h]

/-- EEP of a star product projects to the `A` factor. -/
theorem HasEEP.of_starProduct_left
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic)
    (hStar : (A.starProduct B r ell p q σ).HasEEP) : A.HasEEP := by
  classical
  intro e f hef
  have hneStar :
      A.starAEdge B r ell p e ≠ A.starAEdge B r ell p f := by
    intro h
    exact hef (A.starAEdge_injective B r ell p h)
  obtain ⟨P, root, hP, heStar, hfStar⟩ :=
    hStar (A.starAEdge B r ell p e) (A.starAEdge B r ell p f) hneStar
  let PA := A.starRestrictedA B r ell p P
  let PB := A.starRestrictedB B r ell q σ P
  obtain ⟨i, hPAraw, hPBraw, hpiraw, hqiraw, hEqraw⟩ :=
    hP.starMatchingDecomposition A B r ell p q σ hA
  have hPA : A.IsPerfectMatching PA := by simpa [PA] using hPAraw
  have hPB : B.IsPerfectMatching PB := by simpa [PB] using hPBraw
  have hpi : (p i).1 ∈ PA := by simpa [PA] using hpiraw
  have hqi : (q (σ i)).1 ∈ PB := by simpa [PB] using hqiraw
  have hEq : P = A.starGluedMatching B r ell PA PB i := by
    simpa [PA, PB] using hEqraw
  have hePAc : e ∈ PAᶜ := by
    rw [Finset.mem_compl]
    intro hePA
    have heP : A.starAEdge B r ell p e ∈ P :=
      (A.mem_starRestrictedA B r ell p P e).1 (by simpa [PA] using hePA)
    exact (Finset.mem_compl.mp heStar.1) heP
  have hfPAc : f ∈ PAᶜ := by
    rw [Finset.mem_compl]
    intro hfPA
    have hfP : A.starAEdge B r ell p f ∈ P :=
      (A.mem_starRestrictedA B r ell p P f).1 (by simpa [PA] using hfPA)
    exact (Finset.mem_compl.mp hfStar.1) hfP
  have heStar' := heStar
  have hfStar' := hfStar
  rw [hEq] at heStar' hfStar'
  have heA :=
    A.factorReachable_starAContract_of_glued_compl B r ell p q σ
      PA PB i hPA hpi heStar'.2
  have hfA :=
    A.factorReachable_starAContract_of_glued_compl B r ell p q σ
      PA PB i hPA hpi hfStar'.2
  refine ⟨PA, starAContract r ell root, hPA, ?_, ?_⟩
  · refine ⟨hePAc, ?_⟩
    simpa [starAContract] using heA
  · refine ⟨hfPAc, ?_⟩
    simpa [starAContract] using hfA

/-- EEP of a star product projects to the `B` factor.  The matching
restriction machinery needs cubicity only on `A`, which supplies the unique
bridge used to reconstruct both source matchings. -/
theorem HasEEP.of_starProduct_right
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic)
    (hStar : (A.starProduct B r ell p q σ).HasEEP) : B.HasEEP := by
  classical
  intro e f hef
  have hneStar :
      A.starBEdge B r ell q σ e ≠ A.starBEdge B r ell q σ f := by
    intro h
    exact hef (A.starBEdge_injective B r ell q σ h)
  obtain ⟨P, root, hP, heStar, hfStar⟩ :=
    hStar (A.starBEdge B r ell q σ e) (A.starBEdge B r ell q σ f) hneStar
  let PA := A.starRestrictedA B r ell p P
  let PB := A.starRestrictedB B r ell q σ P
  obtain ⟨i, hPAraw, hPBraw, hpiraw, hqiraw, hEqraw⟩ :=
    hP.starMatchingDecomposition A B r ell p q σ hA
  have hPA : A.IsPerfectMatching PA := by simpa [PA] using hPAraw
  have hPB : B.IsPerfectMatching PB := by simpa [PB] using hPBraw
  have hpi : (p i).1 ∈ PA := by simpa [PA] using hpiraw
  have hqi : (q (σ i)).1 ∈ PB := by simpa [PB] using hqiraw
  have hEq : P = A.starGluedMatching B r ell PA PB i := by
    simpa [PA, PB] using hEqraw
  have hePBc : e ∈ PBᶜ := by
    rw [Finset.mem_compl]
    intro hePB
    have heP : A.starBEdge B r ell q σ e ∈ P :=
      (A.mem_starRestrictedB B r ell q σ P e).1 (by simpa [PB] using hePB)
    exact (Finset.mem_compl.mp heStar.1) heP
  have hfPBc : f ∈ PBᶜ := by
    rw [Finset.mem_compl]
    intro hfPB
    have hfP : A.starBEdge B r ell q σ f ∈ P :=
      (A.mem_starRestrictedB B r ell q σ P f).1 (by simpa [PB] using hfPB)
    exact (Finset.mem_compl.mp hfStar.1) hfP
  have heStar' := heStar
  have hfStar' := hfStar
  rw [hEq] at heStar' hfStar'
  have heB :=
    A.factorReachable_starBContract_of_glued_compl B r ell p q σ
      PA PB i hPB hqi heStar'.2
  have hfB :=
    A.factorReachable_starBContract_of_glued_compl B r ell p q σ
      PA PB i hPB hqi hfStar'.2
  refine ⟨PB, starBContract r ell root, hPB, ?_, ?_⟩
  · refine ⟨hePBc, ?_⟩
    rw [A.starBContract_left_starBEdge B r ell p q σ e] at heB
    exact heB
  · refine ⟨hfPBc, ?_⟩
    rw [A.starBContract_left_starBEdge B r ell p q σ f] at hfB
    exact hfB

end BipartiteMultigraph
end BachThesisLean
