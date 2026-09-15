import BachThesisLean.Cubic.TightCutCorrespondence

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w uA vA wA uB vB wB

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Extending perfect matchings across an oriented tight cut

The eventual Pfaffian contraction argument needs more than existence of perfect
matchings: a perfect matching of either contraction must be completed to an
actual perfect matching of the original edge-copy graph while retaining every
selected contraction copy.

The already formalized star-product reconstruction gives this cleanly.  The
selected root port determines one of the three boundary copies.  Cubicity of
the opposite contraction supplies a perfect matching through the corresponding
port, the two matchings glue across that bridge, and the reconstruction
isomorphism erases the tags back to the original copies.
-/

section StarMembership

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-- Every selected `A` copy is represented by a selected internal copy or the
selected bridge in the glued matching. -/
theorem IsPerfectMatching.starAEdge_mem_starGluedMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA)
    {e : EA} (he : e ∈ PA) :
    A.starAEdge B r ell p e ∈ A.starGluedMatching B r ell PA PB i := by
  classical
  by_cases hr : A.right e = r
  · have heq : e = (p i).1 :=
      (A.isMatching_iff PA).1 hPA.isMatching e he (p i).1 hpi (.inr r)
        (by simpa [Incident] using hr) (by simp [Incident])
    subst e
    simp [starAEdge, A.port_right_eq]
  · simp [starAEdge, hr, he]

/-- Symmetric membership statement for the `B` source of a glued matching. -/
theorem IsPerfectMatching.starBEdge_mem_starGluedMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB)
    {e : EB} (he : e ∈ PB) :
    A.starBEdge B r ell q σ e ∈ A.starGluedMatching B r ell PA PB i := by
  classical
  by_cases hl : B.left e = ell
  · have heq : e = (q (σ i)).1 :=
      (B.isMatching_iff PB).1 hPB.isMatching e he (q (σ i)).1 hqi (.inl ell)
        (by simpa [Incident] using hl) (by simp [Incident])
    subst e
    simp [starBEdge, B.port_left_eq]
  · simp [starBEdge, hl, he]

end StarMembership

/-- Under the tight-cut reconstruction, an `A` edge of the outside contraction
recovers exactly its original edge copy. -/
@[simp] theorem tightCutEdgeErase_starAEdge_contractSet
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (e : ContractSetEdge G W) :
    G.tightCutEdgeErase W c
      ((G.contractSet W).starAEdge (G.contractComplement W)
        (contractSetRoot W) (contractComplementRoot W)
        (G.contractSetPorts W c) e) = e.val := by
  classical
  by_cases hroot :
      (G.contractSet W).right e = contractSetRoot W
  · simp [starAEdge, hroot, tightCutEdgeErase, contractSetPorts]
  · simp [starAEdge, hroot, tightCutEdgeErase]

/-- Under the same reconstruction, a `B` edge of the inside contraction also
recovers exactly its original edge copy. -/
@[simp] theorem tightCutEdgeErase_starBEdge_contractComplement
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (e : ContractComplementEdge G W) :
    G.tightCutEdgeErase W c
      ((G.contractSet W).starBEdge (G.contractComplement W)
        (contractSetRoot W) (contractComplementRoot W)
        (G.contractComplementPorts W c) (Equiv.refl (Fin 3)) e) = e.val := by
  classical
  by_cases hroot :
      (G.contractComplement W).left e = contractComplementRoot W
  · simp [starBEdge, hroot, tightCutEdgeErase, contractComplementPorts]
  · simp [starBEdge, hroot, tightCutEdgeErase]

/-- Every perfect matching of `G / W` extends to a perfect matching of the
original graph, preserving every selected actual edge copy. -/
theorem IsTightCut.exists_perfectMatching_extending_contractSet
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅)
    (P : Finset (ContractSetEdge G W))
    (hP : (G.contractSet W).IsPerfectMatching P) :
    ∃ PG : Finset E, G.IsPerfectMatching PG ∧
      ∀ e : ContractSetEdge G W, e ∈ P → e.val ∈ PG := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  let A := G.contractSet W
  let B := G.contractComplement W
  let p := G.contractSetPorts W c
  let q := G.contractComplementPorts W c
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  obtain ⟨i, hi, -⟩ := hP.existsUnique_port (.inr (contractSetRoot W)) p
  obtain ⟨PB, hPB, hqi⟩ :=
    B.exists_perfectMatching_containing_edge_of_cubic hCubic.1 (q i).1
  let Pstar : Finset (StarEdge A B (contractSetRoot W) (contractComplementRoot W)) :=
    A.starGluedMatching B (contractSetRoot W) (contractComplementRoot W) P PB i
  have hPstar :
      (A.starProduct B (contractSetRoot W) (contractComplementRoot W)
        p q (Equiv.refl (Fin 3))).IsPerfectMatching Pstar := by
    dsimp [Pstar]
    exact A.starGluedMatching_isPerfectMatching B
      (contractSetRoot W) (contractComplementRoot W) p q
      (Equiv.refl (Fin 3)) P PB i hP hPB hi (by simpa using hqi)
  let φ : GraphIso
      (G.tightCutStarProduct W c) G :=
    G.tightCutReconstructionIso W c hOrient
  let PG : Finset E := φ.mapEdges Pstar
  refine ⟨PG, ?_, ?_⟩
  · have : G.IsPerfectMatching (φ.mapEdges Pstar) :=
      (φ.isPerfectMatching_map_iff Pstar).2 (by
        simpa [tightCutStarProduct, A, B, p, q] using hPstar)
    simpa [PG] using this
  · intro e he
    have hstar :
        A.starAEdge B (contractSetRoot W) (contractComplementRoot W) p e ∈ Pstar := by
      exact IsPerfectMatching.starAEdge_mem_starGluedMatching A B
        (contractSetRoot W) (contractComplementRoot W) p P PB i hP hi he
    have himage :
        φ.edgeEquiv
          (A.starAEdge B (contractSetRoot W) (contractComplementRoot W) p e) ∈
          φ.mapEdges Pstar :=
      (φ.mem_mapEdges_apply Pstar _).2 hstar
    simpa [PG, φ, tightCutReconstructionIso, tightCutEdgeEquiv,
      A, B, p, q, c] using himage

/-- Every perfect matching of `G / Wᶜ` likewise extends to the original graph,
again preserving every selected actual edge copy. -/
theorem IsTightCut.exists_perfectMatching_extending_contractComplement
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅)
    (P : Finset (ContractComplementEdge G W))
    (hP : (G.contractComplement W).IsPerfectMatching P) :
    ∃ PG : Finset E, G.IsPerfectMatching PG ∧
      ∀ e : ContractComplementEdge G W, e ∈ P → e.val ∈ PG := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  let A := G.contractSet W
  let B := G.contractComplement W
  let p := G.contractSetPorts W c
  let q := G.contractComplementPorts W c
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  obtain ⟨i, hi, -⟩ := hP.existsUnique_port (.inl (contractComplementRoot W)) q
  obtain ⟨PA, hPA, hpi⟩ :=
    A.exists_perfectMatching_containing_edge_of_cubic hCubic.2 (p i).1
  let Pstar : Finset (StarEdge A B (contractSetRoot W) (contractComplementRoot W)) :=
    A.starGluedMatching B (contractSetRoot W) (contractComplementRoot W) PA P i
  have hPstar :
      (A.starProduct B (contractSetRoot W) (contractComplementRoot W)
        p q (Equiv.refl (Fin 3))).IsPerfectMatching Pstar := by
    dsimp [Pstar]
    exact A.starGluedMatching_isPerfectMatching B
      (contractSetRoot W) (contractComplementRoot W) p q
      (Equiv.refl (Fin 3)) PA P i hPA hP hpi (by simpa using hi)
  let φ : GraphIso
      (G.tightCutStarProduct W c) G :=
    G.tightCutReconstructionIso W c hOrient
  let PG : Finset E := φ.mapEdges Pstar
  refine ⟨PG, ?_, ?_⟩
  · have : G.IsPerfectMatching (φ.mapEdges Pstar) :=
      (φ.isPerfectMatching_map_iff Pstar).2 (by
        simpa [tightCutStarProduct, A, B, p, q] using hPstar)
    simpa [PG] using this
  · intro e he
    have hstar :
        A.starBEdge B (contractSetRoot W) (contractComplementRoot W)
          q (Equiv.refl (Fin 3)) e ∈ Pstar := by
      exact IsPerfectMatching.starBEdge_mem_starGluedMatching A B
        (contractSetRoot W) (contractComplementRoot W) q
        (Equiv.refl (Fin 3)) PA P i hP (by simpa using hi) he
    have himage :
        φ.edgeEquiv
          (A.starBEdge B (contractSetRoot W) (contractComplementRoot W)
            q (Equiv.refl (Fin 3)) e) ∈ φ.mapEdges Pstar :=
      (φ.mem_mapEdges_apply Pstar _).2 hstar
    simpa [PG, φ, tightCutReconstructionIso, tightCutEdgeEquiv,
      A, B, p, q, c] using himage

end BipartiteMultigraph
end BachThesisLean
