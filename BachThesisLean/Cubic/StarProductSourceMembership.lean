import BachThesisLean.Cubic.StarProductMatchingDecomposition

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
# Source-edge membership in a glued star matching

The total edge maps send the selected source root port to the selected bridge
and all other source edges to their surviving/internal or unused-bridge copies.
Consequently source matching membership is exactly star matching membership.
-/

/-- `A`-source matching membership is preserved by `starAEdge`. -/
theorem starAEdge_mem_starGluedMatching_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA) (e : EA) :
    A.starAEdge B r ell p e ∈ A.starGluedMatching B r ell PA PB i ↔ e ∈ PA := by
  classical
  by_cases hr : A.right e = r
  · let er : {g : EA // g ∈ A.incidentEdges (.inr r)} :=
      ⟨e, (A.mem_incidentEdges (.inr r) e).2 (by simpa [Incident] using hr)⟩
    let j : Fin 3 := p.symm er
    have hpj : (p j).1 = e := by
      have hsub : p j = er := by simpa [j] using p.apply_symm_apply er
      exact congrArg Subtype.val hsub
    have hedge : A.starAEdge B r ell p e =
        (Sum.inr (Sum.inr j) : StarEdge A B r ell) := by
      rw [← hpj]
      exact A.starAEdge_port B r ell p j
    constructor
    · intro hs
      have hji : j = i :=
        (A.mem_starGluedMatching_bridge B r ell PA PB i j).1 (by
          simpa [hedge] using hs)
      rw [← hpj, hji]
      exact hpi
    · intro hePA
      obtain ⟨k, _hk, huniq⟩ := hPA.existsUnique_port (.inr r) p
      have hjPA : (p j).1 ∈ PA := by simpa [hpj] using hePA
      have hji : j = i := (huniq j hjPA).trans (huniq i hpi).symm
      rw [hedge]
      exact (A.mem_starGluedMatching_bridge B r ell PA PB i j).2 hji
  · let es : {g : EA // A.right g ≠ r} := ⟨e, hr⟩
    have hedge : A.starAEdge B r ell p e =
        (Sum.inl es : StarEdge A B r ell) := by
      simp [starAEdge, hr, es]
    rw [hedge]
    exact A.mem_starGluedMatching_aInternal B r ell PA PB i es

/-- Complementary membership is likewise preserved on the `A` side. -/
@[simp] theorem starAEdge_mem_starGluedMatching_compl_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA) (e : EA) :
    A.starAEdge B r ell p e ∈ (A.starGluedMatching B r ell PA PB i)ᶜ ↔
      e ∈ PAᶜ := by
  simp [A.starAEdge_mem_starGluedMatching_iff B r ell p PA PB i hPA hpi e]

/-- `B`-source matching membership is preserved by `starBEdge`. -/
theorem starBEdge_mem_starGluedMatching_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB) (e : EB) :
    A.starBEdge B r ell q σ e ∈ A.starGluedMatching B r ell PA PB i ↔ e ∈ PB := by
  classical
  by_cases hl : B.left e = ell
  · let er : {g : EB // g ∈ B.incidentEdges (.inl ell)} :=
      ⟨e, (B.mem_incidentEdges (.inl ell) e).2 (by simpa [Incident] using hl)⟩
    let k : Fin 3 := q.symm er
    let j : Fin 3 := σ.symm k
    have hqk : (q k).1 = e := by
      have hsub : q k = er := by simpa [k] using q.apply_symm_apply er
      exact congrArg Subtype.val hsub
    have hσj : σ j = k := by simp [j]
    have hedge : A.starBEdge B r ell q σ e =
        (Sum.inr (Sum.inr j) : StarEdge A B r ell) := by
      rw [← hqk, ← hσj]
      exact A.starBEdge_port B r ell q σ j
    constructor
    · intro hs
      have hji : j = i :=
        (A.mem_starGluedMatching_bridge B r ell PA PB i j).1 (by
          simpa [hedge] using hs)
      have hki : k = σ i := by rw [← hσj, hji]
      rw [← hqk, hki]
      exact hqi
    · intro hePB
      obtain ⟨t, _ht, huniq⟩ := hPB.existsUnique_port (.inl ell) q
      have hkPB : (q k).1 ∈ PB := by simpa [hqk] using hePB
      have hki : k = σ i := (huniq k hkPB).trans (huniq (σ i) hqi).symm
      have hji : j = i := by
        apply σ.injective
        simpa [hσj] using hki
      rw [hedge]
      exact (A.mem_starGluedMatching_bridge B r ell PA PB i j).2 hji
  · let es : {g : EB // B.left g ≠ ell} := ⟨e, hl⟩
    have hedge : A.starBEdge B r ell q σ e =
        (Sum.inr (Sum.inl es) : StarEdge A B r ell) := by
      simp [starBEdge, hl, es]
    rw [hedge]
    exact A.mem_starGluedMatching_bInternal B r ell PA PB i es

/-- Complementary membership is preserved on the `B` side. -/
@[simp] theorem starBEdge_mem_starGluedMatching_compl_iff
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB) (e : EB) :
    A.starBEdge B r ell q σ e ∈ (A.starGluedMatching B r ell PA PB i)ᶜ ↔
      e ∈ PBᶜ := by
  simp [A.starBEdge_mem_starGluedMatching_iff B r ell q σ PA PB i hPB hqi e]

end BipartiteMultigraph
end BachThesisLean
