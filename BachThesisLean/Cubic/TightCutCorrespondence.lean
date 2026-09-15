import BachThesisLean.Cubic.TightCutReconstruction
import BachThesisLean.Cubic.TightCutContractionConnectivity
import BachThesisLean.Cubic.StarProductTwoEP
import BachThesisLean.Cubic.IsomorphismProperties

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Tight-cut correspondence for connected cubic bipartite multigraphs

The preceding files construct the two explicit contractions of a right-oriented
three-edge tight cut, prove their cubicity and connectedness, and reconstruct
the original graph as their three-port star product.  This file packages those
ingredients into the manuscript-level correspondence and invariance statements.

All boundary data are carried by edge copies.  In particular, the three ports
are enumerated by the subtype of `cutFromRight W`, so parallel boundary edges
remain distinct throughout the correspondence.
-/

/-- Complementing the vertex shore swaps the two oriented boundary pieces. -/
@[simp] theorem cutFromLeft_compl
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    G.cutFromLeft Wᶜ = G.cutFromRight W := by
  classical
  ext e
  simp [cutFromLeft, cutFromRight]

/-- Complementing the vertex shore swaps the two oriented boundary pieces. -/
@[simp] theorem cutFromRight_compl
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    G.cutFromRight Wᶜ = G.cutFromLeft W := by
  classical
  ext e
  simp [cutFromLeft, cutFromRight]

/-- Tightness is unchanged by exchanging the two cut shores. -/
theorem IsTightCut.compl
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) : G.IsTightCut Wᶜ := by
  intro P hP
  simpa using hT P hP

/-- Nontriviality is unchanged by exchanging the two cut shores. -/
theorem IsNontrivialCutShore.compl
    {W : Finset (X ⊕ Y)} (hW : IsNontrivialCutShore W) :
    IsNontrivialCutShore Wᶜ := by
  simpa [IsNontrivialCutShore, and_comm] using hW

/-- In the right-oriented branch, the whole three-edge boundary is exactly
`cutFromRight W`. -/
theorem IsTightCut.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) :
    (G.cutFromRight W).card = 3 := by
  have hEdge : (G.edgeCut W).card = 3 :=
    hT.edgeCut_card_eq_three_of_connected_cubic hconn hG
  rw [G.edgeCut_eq_oriented_union W, hOrient] at hEdge
  simpa using hEdge

/-- Every nontrivial tight cut of a connected cubic graph can be represented by
one of its two shores so that all three boundary copies point into that shore. -/
theorem IsTightCut.exists_right_oriented_shore
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hnontriv : IsNontrivialCutShore W) :
    ∃ U : Finset (X ⊕ Y),
      (U = W ∨ U = Wᶜ) ∧ G.IsTightCut U ∧ IsNontrivialCutShore U ∧
        G.cutFromLeft U = ∅ := by
  rcases hT.oriented_three_of_connected_cubic hconn hG with hL | hR
  · have hRightEmpty : G.cutFromRight W = ∅ := Finset.card_eq_zero.mp hL.2
    refine ⟨Wᶜ, Or.inr rfl, hT.compl, hnontriv.compl, ?_⟩
    simpa using hRightEmpty
  · have hLeftEmpty : G.cutFromLeft W = ∅ := Finset.card_eq_zero.mp hR.1
    exact ⟨W, Or.inl rfl, hT, hnontriv, hLeftEmpty⟩

/-- A nontrivial right-oriented tight cut has connected, cubic,
matching-covered contractions on both sides. -/
theorem IsTightCut.right_oriented_contractions_matchingCovered
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hnontriv : IsNontrivialCutShore W)
    (hOrient : G.cutFromLeft W = ∅) :
    (G.contractComplement W).IsMatchingCovered ∧
      (G.contractSet W).IsMatchingCovered := by
  have hConnected :=
    hT.right_oriented_contractions_connected hconn hnontriv hOrient
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  exact ⟨
    (G.contractComplement W).isMatchingCovered_of_connected_cubic
      hConnected.1 hCubic.1,
    (G.contractSet W).isMatchingCovered_of_connected_cubic
      hConnected.2 hCubic.2⟩

/-- The explicit contraction pair reconstructs the original graph as a
three-port star product, with the three original boundary edge copies used as
ports. -/
theorem IsTightCut.exists_right_oriented_reconstruction
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) :
    ∃ c : Fin 3 ≃ {e // e ∈ G.cutFromRight W},
      Nonempty (GraphIso (G.tightCutStarProduct W c) G) := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  exact ⟨c, ⟨G.tightCutReconstructionIso W c hOrient⟩⟩

/-- EEP decomposes exactly through a right-oriented tight three-edge cut. -/
theorem IsTightCut.right_oriented_hasEEP_iff_contractions
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) :
    G.HasEEP ↔
      (G.contractSet W).HasEEP ∧ (G.contractComplement W).HasEEP := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  have hIso : GraphIso (G.tightCutStarProduct W c) G :=
    G.tightCutReconstructionIso W c hOrient
  calc
    G.HasEEP ↔ (G.tightCutStarProduct W c).HasEEP := hIso.hasEEP_iff
    _ ↔ (G.contractSet W).HasEEP ∧ (G.contractComplement W).HasEEP := by
      simpa [tightCutStarProduct] using
        (G.contractSet W).starProduct_hasEEP_iff
          (G.contractComplement W)
          (contractSetRoot W) (contractComplementRoot W)
          (G.contractSetPorts W c) (G.contractComplementPorts W c)
          (Equiv.refl (Fin 3)) hCubic.2 hCubic.1

/-- The full tagged two-element property likewise decomposes exactly through
a right-oriented tight three-edge cut. -/
theorem IsTightCut.right_oriented_hasTwoEP_iff_contractions
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) :
    G.HasTwoEP ↔
      (G.contractSet W).HasTwoEP ∧ (G.contractComplement W).HasTwoEP := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  have hIso : GraphIso (G.tightCutStarProduct W c) G :=
    G.tightCutReconstructionIso W c hOrient
  calc
    G.HasTwoEP ↔ (G.tightCutStarProduct W c).HasTwoEP := hIso.hasTwoEP_iff
    _ ↔ (G.contractSet W).HasTwoEP ∧ (G.contractComplement W).HasTwoEP := by
      simpa [tightCutStarProduct] using
        (G.contractSet W).starProduct_hasTwoEP_iff
          (G.contractComplement W)
          (contractSetRoot W) (contractComplementRoot W)
          (G.contractSetPorts W c) (G.contractComplementPorts W c)
          (Equiv.refl (Fin 3)) hCubic.2 hCubic.1

end BipartiteMultigraph
end BachThesisLean
