import BachThesisLean.Cubic.StarProductDecompositionB

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
# Matching decomposition across a star product

Together with the forward gluing construction, the restriction lemmas show
that a perfect matching of the star product is obtained uniquely from perfect
matchings of the two source factors through its unique selected bridge.
-/

/-- A star-product perfect matching is exactly the gluing of its two canonical
factor restrictions through its unique selected bridge. -/
theorem IsPerfectMatching.eq_starGluedMatching_restrictions
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) {P : Finset (StarEdge A B r ell)}
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    ∃ i : Fin 3,
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P ∧
      P = A.starGluedMatching B r ell
        (A.starRestrictedA B r ell p P)
        (A.starRestrictedB B r ell q σ P) i := by
  classical
  obtain ⟨i, hi, huniq⟩ :=
    hP.existsUnique_starBridge A B r ell p q σ hA
  refine ⟨i, hi, ?_⟩
  ext s
  rcases s with ea | rest
  · rw [A.mem_starGluedMatching_aInternal B r ell
      (A.starRestrictedA B r ell p P)
      (A.starRestrictedB B r ell q σ P) i ea]
    exact (A.mem_starRestrictedA_internal B r ell p P ea).symm
  · rcases rest with eb | j
    · rw [A.mem_starGluedMatching_bInternal B r ell
        (A.starRestrictedA B r ell p P)
        (A.starRestrictedB B r ell q σ P) i eb]
      exact (A.mem_starRestrictedB_internal B r ell q σ P eb).symm
    · rw [A.mem_starGluedMatching_bridge B r ell
        (A.starRestrictedA B r ell p P)
        (A.starRestrictedB B r ell q σ P) i j]
      constructor
      · intro hj
        exact huniq j hj
      · intro hji
        subst j
        exact hi

/-- Bundled converse to the matching gluing construction: a perfect matching
of the star product restores perfect matchings of both source factors, uses
the corresponding source ports, and glues back to the original edge set. -/
theorem IsPerfectMatching.starMatchingDecomposition
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) {P : Finset (StarEdge A B r ell)}
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    ∃ i : Fin 3,
      A.IsPerfectMatching (A.starRestrictedA B r ell p P) ∧
      B.IsPerfectMatching (A.starRestrictedB B r ell q σ P) ∧
      (p i).1 ∈ A.starRestrictedA B r ell p P ∧
      (q (σ i)).1 ∈ A.starRestrictedB B r ell q σ P ∧
      P = A.starGluedMatching B r ell
        (A.starRestrictedA B r ell p P)
        (A.starRestrictedB B r ell q σ P) i := by
  classical
  obtain ⟨i, hi, hEq⟩ :=
    hP.eq_starGluedMatching_restrictions A B r ell p q σ hA
  refine ⟨i, ?_, ?_, ?_, ?_, hEq⟩
  · exact A.starRestrictedA_isPerfectMatching B r ell p q σ hA P hP
  · exact A.starRestrictedB_isPerfectMatching B r ell p q σ hA P hP
  · exact (A.mem_starRestrictedA_port B r ell p P i).2 hi
  · exact (A.mem_starRestrictedB_port B r ell q σ P i).2 hi

/-- Fixed-port existence criterion for perfect matchings of a star product.
This is the matching-theoretic half of the manuscript's star-port criterion;
the complementary two-factor path statement is handled separately. -/
theorem starPerfectMatching_usingBridge_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (i : Fin 3) :
    (∃ P : Finset (StarEdge A B r ell),
      (A.starProduct B r ell p q σ).IsPerfectMatching P ∧
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P) ↔
    ∃ PA : Finset EA, ∃ PB : Finset EB,
      A.IsPerfectMatching PA ∧ B.IsPerfectMatching PB ∧
      (p i).1 ∈ PA ∧ (q (σ i)).1 ∈ PB := by
  classical
  constructor
  · rintro ⟨P, hP, hi⟩
    refine ⟨A.starRestrictedA B r ell p P,
      A.starRestrictedB B r ell q σ P, ?_, ?_, ?_, ?_⟩
    · exact A.starRestrictedA_isPerfectMatching B r ell p q σ hA P hP
    · exact A.starRestrictedB_isPerfectMatching B r ell p q σ hA P hP
    · exact (A.mem_starRestrictedA_port B r ell p P i).2 hi
    · exact (A.mem_starRestrictedB_port B r ell q σ P i).2 hi
  · rintro ⟨PA, PB, hPA, hPB, hpi, hqi⟩
    refine ⟨A.starGluedMatching B r ell PA PB i, ?_, ?_⟩
    · exact A.starGluedMatching_isPerfectMatching B r ell p q σ
        PA PB i hPA hPB hpi hqi
    · exact (A.mem_starGluedMatching_bridge B r ell PA PB i i).2 rfl

/-!
## Complementary-factor port bookkeeping

The full star-port criterion is a statement about components of the complements
of the matchings above.  The first bookkeeping step is that the two unused
source ports are exactly the two unused joining edges.
-/

/-- Once a perfect matching uses port `i`, source port `j` belongs to the
complement exactly when `j ≠ i`. -/
theorem IsPerfectMatching.port_mem_compl_iff_ne
    (G : BipartiteMultigraph XA YA EA) {P : Finset EA}
    (hP : G.IsPerfectMatching P) (root : XA ⊕ YA)
    (ports : G.PortEnumeration root) (i : Fin 3)
    (hi : (ports i).1 ∈ P) (j : Fin 3) :
    (ports j).1 ∈ Pᶜ ↔ j ≠ i := by
  rw [Finset.mem_compl]
  constructor
  · intro hj hji
    subst j
    exact hj hi
  · intro hji hj
    obtain ⟨k, hk, huniq⟩ := hP.existsUnique_port root ports
    exact hji ((huniq j hj).trans (huniq i hi).symm)

/-- In a glued star matching, bridge `j` is complementary exactly when it is
not the selected bridge `i`. -/
@[simp] theorem mem_starGluedMatching_bridge_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (PA : Finset EA) (PB : Finset EB) (i j : Fin 3) :
    (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈
        (A.starGluedMatching B r ell PA PB i)ᶜ ↔ j ≠ i := by
  simp

/-- The complementary status of an `A` root port agrees exactly with the
corresponding bridge in the glued star matching. -/
theorem starA_port_compl_iff_bridge_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (PA : Finset EA) (PB : Finset EB) (i j : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA) :
    (p j).1 ∈ PAᶜ ↔
      (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈
        (A.starGluedMatching B r ell PA PB i)ᶜ := by
  rw [hPA.port_mem_compl_iff_ne A (.inr r) p i hpi j]
  simp

/-- The complementary status of a `B` root port agrees exactly with its
permuted bridge in the glued star matching. -/
theorem starB_port_compl_iff_bridge_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i j : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB) :
    (q (σ j)).1 ∈ PBᶜ ↔
      (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈
        (A.starGluedMatching B r ell PA PB i)ᶜ := by
  rw [hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)]
  simp

end BipartiteMultigraph
end BachThesisLean
