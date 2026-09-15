import BachThesisLean.Cubic.StarProductMatchingDecomposition
import BachThesisLean.Cubic.TwoFactorRootPathLeft

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
# Lifting complementary factor paths into a star product

After the deleted roots are removed, a source-factor path uses only surviving
internal edge copies.  The maps below embed such paths into the complement of
a glued star matching.  The arbitrary root branch of each total vertex map is
never used by a selected adjacency in the root-deleted factor; it only makes
the map total so `ReflTransGen.lift` can be applied directly.
-/

/-- Total vertex map from `A` into the star-product vertex type.  The deleted
right root is sent to a harmless surviving `A`-left vertex chosen from port
zero; every non-root vertex is embedded canonically. -/
noncomputable def starAVertexMap
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r)) :
    XA ⊕ YA → StarLeft XA XB ell ⊕ StarRight YA YB r
  | .inl x => .inl (.inl x)
  | .inr y =>
      if h : y = r then
        .inl (.inl (A.left (p (0 : Fin 3)).1))
      else
        .inr (.inl ⟨y, h⟩)

@[simp] theorem starAVertexMap_left
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r)) (x : XA) :
    A.starAVertexMap B r ell p (.inl x) = .inl (.inl x) := rfl

@[simp] theorem starAVertexMap_right_of_ne
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (y : YA) (hy : y ≠ r) :
    A.starAVertexMap B r ell p (.inr y) = .inr (.inl ⟨y, hy⟩) := by
  simp [starAVertexMap, hy]

/-- Total vertex map from `B` into the star-product vertex type.  The deleted
left root is sent to a harmless surviving `B`-right vertex chosen from port
zero; every non-root vertex is embedded canonically. -/
noncomputable def starBVertexMap
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell)) :
    XB ⊕ YB → StarLeft XA XB ell ⊕ StarRight YA YB r
  | .inl x =>
      if h : x = ell then
        .inr (.inr (B.right (q (0 : Fin 3)).1))
      else
        .inl (.inr ⟨x, h⟩)
  | .inr y => .inr (.inr y)

@[simp] theorem starBVertexMap_left_of_ne
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (x : XB) (hx : x ≠ ell) :
    A.starBVertexMap B r ell q (.inl x) = .inl (.inr ⟨x, hx⟩) := by
  simp [starBVertexMap, hx]

@[simp] theorem starBVertexMap_right
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell)) (y : YB) :
    A.starBVertexMap B r ell q (.inr y) = .inr (.inr y) := rfl

/-- A selected adjacency of the `A` complementary factor after deleting its
right root becomes a selected internal adjacency in the star complement. -/
theorem selectedAdjacent_starA_of_factorDeleteRoot
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    {u v : XA ⊕ YA}
    (h : A.SelectedAdjacent (A.factorDeleteRoot PAᶜ (.inr r)) u v) :
    (A.starProduct B r ell p q σ).SelectedAdjacent
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (A.starAVertexMap B r ell p u)
      (A.starAVertexMap B r ell p v) := by
  classical
  rcases h with ⟨e, heT, hdir | hdir⟩
  · have heT' := (A.mem_factorDeleteRoot PAᶜ (.inr r) e).1 heT
    have hright : A.right e ≠ r := by
      intro hr
      apply heT'.2
      exact (A.mem_selectedIncident PAᶜ (.inr r) e).2
        ⟨heT'.1, by simpa [Incident] using hr⟩
    let se : StarEdge A B r ell := .inl ⟨e, hright⟩
    have hse : se ∈ (A.starGluedMatching B r ell PA PB i)ᶜ := by
      rw [Finset.mem_compl]
      intro hmem
      have hePA : e ∈ PA :=
        (A.mem_starGluedMatching_aInternal B r ell PA PB i ⟨e, hright⟩).1 hmem
      have hnotPA : e ∉ PA := by simpa using heT'.1
      exact hnotPA hePA
    refine ⟨se, hse, ?_⟩
    rcases hdir with ⟨rfl, rfl⟩
    exact Or.inl (by
      constructor <;> simp [se, starAVertexMap, starProduct, hright])
  · have heT' := (A.mem_factorDeleteRoot PAᶜ (.inr r) e).1 heT
    have hright : A.right e ≠ r := by
      intro hr
      apply heT'.2
      exact (A.mem_selectedIncident PAᶜ (.inr r) e).2
        ⟨heT'.1, by simpa [Incident] using hr⟩
    let se : StarEdge A B r ell := .inl ⟨e, hright⟩
    have hse : se ∈ (A.starGluedMatching B r ell PA PB i)ᶜ := by
      rw [Finset.mem_compl]
      intro hmem
      have hePA : e ∈ PA :=
        (A.mem_starGluedMatching_aInternal B r ell PA PB i ⟨e, hright⟩).1 hmem
      have hnotPA : e ∉ PA := by simpa using heT'.1
      exact hnotPA hePA
    refine ⟨se, hse, ?_⟩
    rcases hdir with ⟨rfl, rfl⟩
    exact Or.inr (by
      constructor <;> simp [se, starAVertexMap, starProduct, hright])

/-- Reachability in the root-deleted `A` complement lifts to reachability in
the star complement. -/
theorem factorReachable_starA_of_factorDeleteRoot
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    {u v : XA ⊕ YA}
    (h : A.FactorReachable (A.factorDeleteRoot PAᶜ (.inr r)) u v) :
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (A.starAVertexMap B r ell p u)
      (A.starAVertexMap B r ell p v) := by
  exact Relation.ReflTransGen.lift
    (A.starAVertexMap B r ell p)
    (fun _ _ hab =>
      A.selectedAdjacent_starA_of_factorDeleteRoot B r ell p q σ PA PB i hab)
    h

/-- A selected adjacency of the `B` complementary factor after deleting its
left root becomes a selected internal adjacency in the star complement. -/
theorem selectedAdjacent_starB_of_factorDeleteRoot
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    {u v : XB ⊕ YB}
    (h : B.SelectedAdjacent (B.factorDeleteRoot PBᶜ (.inl ell)) u v) :
    (A.starProduct B r ell p q σ).SelectedAdjacent
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (A.starBVertexMap B r ell q u)
      (A.starBVertexMap B r ell q v) := by
  classical
  rcases h with ⟨e, heT, hdir | hdir⟩
  · have heT' := (B.mem_factorDeleteRoot PBᶜ (.inl ell) e).1 heT
    have hleft : B.left e ≠ ell := by
      intro hl
      apply heT'.2
      exact (B.mem_selectedIncident PBᶜ (.inl ell) e).2
        ⟨heT'.1, by simpa [Incident] using hl⟩
    let se : StarEdge A B r ell := .inr (.inl ⟨e, hleft⟩)
    have hse : se ∈ (A.starGluedMatching B r ell PA PB i)ᶜ := by
      rw [Finset.mem_compl]
      intro hmem
      have hePB : e ∈ PB :=
        (A.mem_starGluedMatching_bInternal B r ell PA PB i ⟨e, hleft⟩).1 hmem
      have hnotPB : e ∉ PB := by simpa using heT'.1
      exact hnotPB hePB
    refine ⟨se, hse, ?_⟩
    rcases hdir with ⟨rfl, rfl⟩
    exact Or.inl (by
      constructor <;> simp [se, starBVertexMap, starProduct, hleft])
  · have heT' := (B.mem_factorDeleteRoot PBᶜ (.inl ell) e).1 heT
    have hleft : B.left e ≠ ell := by
      intro hl
      apply heT'.2
      exact (B.mem_selectedIncident PBᶜ (.inl ell) e).2
        ⟨heT'.1, by simpa [Incident] using hl⟩
    let se : StarEdge A B r ell := .inr (.inl ⟨e, hleft⟩)
    have hse : se ∈ (A.starGluedMatching B r ell PA PB i)ᶜ := by
      rw [Finset.mem_compl]
      intro hmem
      have hePB : e ∈ PB :=
        (A.mem_starGluedMatching_bInternal B r ell PA PB i ⟨e, hleft⟩).1 hmem
      have hnotPB : e ∉ PB := by simpa using heT'.1
      exact hnotPB hePB
    refine ⟨se, hse, ?_⟩
    rcases hdir with ⟨rfl, rfl⟩
    exact Or.inr (by
      constructor <;> simp [se, starBVertexMap, starProduct, hleft])

/-- Reachability in the root-deleted `B` complement lifts to reachability in
the star complement. -/
theorem factorReachable_starB_of_factorDeleteRoot
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    {u v : XB ⊕ YB}
    (h : B.FactorReachable (B.factorDeleteRoot PBᶜ (.inl ell)) u v) :
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (A.starBVertexMap B r ell q u)
      (A.starBVertexMap B r ell q v) := by
  exact Relation.ReflTransGen.lift
    (A.starBVertexMap B r ell q)
    (fun _ _ hab =>
      A.selectedAdjacent_starB_of_factorDeleteRoot B r ell p q σ PA PB i hab)
    h

/-- The two unused `A` ports are joined by the lifted residual `A` path in the
complement of the glued star matching. -/
theorem starA_compl_reachable_between_unused_ports
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i j k : Fin 3)
    (hA : A.IsCubic) (hPA : A.IsPerfectMatching PA)
    (hpi : (p i).1 ∈ PA) (hji : j ≠ i) (hki : k ≠ i) :
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (.inl (.inl (A.left (p j).1)))
      (.inl (.inl (A.left (p k).1))) := by
  have hTF : A.IsTwoFactor PAᶜ :=
    (A.perfectMatching_compl_iff_twoFactor hA PA).1 hPA
  have hjc : (p j).1 ∈ PAᶜ :=
    (hPA.port_mem_compl_iff_ne A (.inr r) p i hpi j).2 hji
  have hkc : (p k).1 ∈ PAᶜ :=
    (hPA.port_mem_compl_iff_ne A (.inr r) p i hpi k).2 hki
  have hjroot : (p j).1 ∈ A.selectedIncident PAᶜ (.inr r) :=
    (A.mem_selectedIncident PAᶜ (.inr r) (p j).1).2
      ⟨hjc, by simp [Incident]⟩
  have hkroot : (p k).1 ∈ A.selectedIncident PAᶜ (.inr r) :=
    (A.mem_selectedIncident PAᶜ (.inr r) (p k).1).2
      ⟨hkc, by simp [Incident]⟩
  have hsrc := hTF.factorDeleteRightRoot_reaches_between_ports hjroot hkroot
  have hlift :=
    A.factorReachable_starA_of_factorDeleteRoot B r ell p q σ PA PB i hsrc
  simpa [starAVertexMap] using hlift

/-- The two unused `B` ports are joined by the lifted residual `B` path in the
complement of the glued star matching. -/
theorem starB_compl_reachable_between_unused_ports
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i j k : Fin 3)
    (hB : B.IsCubic) (hPB : B.IsPerfectMatching PB)
    (hqi : (q (σ i)).1 ∈ PB) (hji : j ≠ i) (hki : k ≠ i) :
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (.inr (.inr (B.right (q (σ j)).1)))
      (.inr (.inr (B.right (q (σ k)).1))) := by
  have hTF : B.IsTwoFactor PBᶜ :=
    (B.perfectMatching_compl_iff_twoFactor hB PB).1 hPB
  have hσj : σ j ≠ σ i := fun h => hji (σ.injective h)
  have hσk : σ k ≠ σ i := fun h => hki (σ.injective h)
  have hjc : (q (σ j)).1 ∈ PBᶜ :=
    (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)).2 hσj
  have hkc : (q (σ k)).1 ∈ PBᶜ :=
    (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ k)).2 hσk
  have hjroot : (q (σ j)).1 ∈ B.selectedIncident PBᶜ (.inl ell) :=
    (B.mem_selectedIncident PBᶜ (.inl ell) (q (σ j)).1).2
      ⟨hjc, by simp [Incident]⟩
  have hkroot : (q (σ k)).1 ∈ B.selectedIncident PBᶜ (.inl ell) :=
    (B.mem_selectedIncident PBᶜ (.inl ell) (q (σ k)).1).2
      ⟨hkc, by simp [Incident]⟩
  have hsrc := hTF.factorDeleteLeftRoot_reaches_between_ports hjroot hkroot
  have hlift :=
    A.factorReachable_starB_of_factorDeleteRoot B r ell p q σ PA PB i hsrc
  simpa [starBVertexMap] using hlift

/-- An unused bridge is itself an edge of the complementary factor. -/
theorem starBridge_compl_reachable
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i j : Fin 3) (hji : j ≠ i) :
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (.inl (.inl (A.left (p j).1)))
      (.inr (.inr (B.right (q (σ j)).1))) := by
  have hbridge : (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈
      (A.starGluedMatching B r ell PA PB i)ᶜ :=
    (A.mem_starGluedMatching_bridge_compl B r ell PA PB i j).2 hji
  simpa using
    ((A.starProduct B r ell p q σ).factorReachable_endpoints hbridge)

/-- The two unused bridges and the two lifted source paths lie in one
complementary component.  This is the connectivity core of the manuscript's
star-product cycle-splicing argument. -/
theorem starCompl_splice_unused_ports
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i j k : Fin 3)
    (hA : A.IsCubic) (hB : B.IsCubic)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hpi : (p i).1 ∈ PA) (hqi : (q (σ i)).1 ∈ PB)
    (hji : j ≠ i) (hki : k ≠ i) :
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (.inl (.inl (A.left (p j).1)))
      (.inl (.inl (A.left (p k).1))) ∧
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (.inr (.inr (B.right (q (σ j)).1)))
      (.inr (.inr (B.right (q (σ k)).1))) ∧
    (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ
      (.inl (.inl (A.left (p j).1)))
      (.inr (.inr (B.right (q (σ k)).1))) := by
  have hAp := A.starA_compl_reachable_between_unused_ports B r ell p q σ
    PA PB i j k hA hPA hpi hji hki
  have hBp := A.starB_compl_reachable_between_unused_ports B r ell p q σ
    PA PB i j k hB hPB hqi hji hki
  have hbj := A.starBridge_compl_reachable B r ell p q σ PA PB i j hji
  exact ⟨hAp, hBp, hbj.trans hBp⟩

end BipartiteMultigraph
end BachThesisLean
