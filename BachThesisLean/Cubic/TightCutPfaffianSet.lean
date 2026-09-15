import BachThesisLean.Cubic.StarProductPfaffianNormalizeA
import BachThesisLean.Cubic.StarProductPfaffianRelativeB
import BachThesisLean.Cubic.StarProductPfaffianProductB
import BachThesisLean.Cubic.StarProductPfaffianSamePortB
import BachThesisLean.Cubic.StarProductPfaffianNormalizeB
import BachThesisLean.Cubic.PfaffianIsomorphism

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Pfaffian descent across a right-oriented tight cut

For a connected cubic graph with a right-oriented tight cut, the explicit
reconstruction identifies the original graph with the star product of its two
contractions.  Transport a Pfaffian witness to that star product and apply the
three-port-normalized source-factor descent theorems.
-/

/-- A Pfaffian witness descends through a right-oriented tight cut to `G / W`.
All edge-copy information is retained by the explicit tight-cut reconstruction
isomorphism. -/
noncomputable def IsTightCut.pfaffianWitness_contractSet
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) (WG : PfaffianWitness G) :
    PfaffianWitness (G.contractSet W) := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  let A := G.contractSet W
  let B := G.contractComplement W
  let p := G.contractSetPorts W c
  let q := G.contractComplementPorts W c
  let φ : GraphIso (G.tightCutStarProduct W c) G :=
    G.tightCutReconstructionIso W c hOrient
  let Wstar : PfaffianWitness (G.tightCutStarProduct W c) := WG.map φ.symm
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  let Sstar : PfaffianSigning
      (A.starProduct B (contractSetRoot W) (contractComplementRoot W)
        p q (Equiv.refl (Fin 3))) Wstar.reference := by
    simpa [tightCutStarProduct, A, B, p, q] using Wstar.signing
  exact Sstar.sourceAPfaffianWitness A B
    (contractSetRoot W) (contractComplementRoot W) p q
    (Equiv.refl (Fin 3)) hCubic.2 hCubic.1

/-- The same Pfaffian witness descends to the complementary contraction
`G / Wᶜ`. -/
noncomputable def IsTightCut.pfaffianWitness_contractComplement
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) (WG : PfaffianWitness G) :
    PfaffianWitness (G.contractComplement W) := by
  classical
  let c : Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
    G.tightCutBoundaryEnumeration W
      (hT.cutFromRight_card_eq_three_of_right_oriented_connected_cubic
        hconn hG hOrient)
  let A := G.contractSet W
  let B := G.contractComplement W
  let p := G.contractSetPorts W c
  let q := G.contractComplementPorts W c
  let φ : GraphIso (G.tightCutStarProduct W c) G :=
    G.tightCutReconstructionIso W c hOrient
  let Wstar : PfaffianWitness (G.tightCutStarProduct W c) := WG.map φ.symm
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  let Sstar : PfaffianSigning
      (A.starProduct B (contractSetRoot W) (contractComplementRoot W)
        p q (Equiv.refl (Fin 3))) Wstar.reference := by
    simpa [tightCutStarProduct, A, B, p, q] using Wstar.signing
  exact Sstar.sourceBPfaffianWitness A B
    (contractSetRoot W) (contractComplementRoot W) p q
    (Equiv.refl (Fin 3)) hCubic.2 hCubic.1

/-- Proposition-level tight-cut descent: Pfaffianness of the original graph
implies Pfaffianness of both explicit contractions. -/
theorem IsTightCut.pfaffianWitness_contractions_nonempty
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅)
    (hPf : Nonempty (PfaffianWitness G)) :
    Nonempty (PfaffianWitness (G.contractSet W)) ∧
      Nonempty (PfaffianWitness (G.contractComplement W)) := by
  rcases hPf with ⟨WG⟩
  exact ⟨⟨hT.pfaffianWitness_contractSet hconn hG hOrient WG⟩,
    ⟨hT.pfaffianWitness_contractComplement hconn hG hOrient WG⟩⟩

end BipartiteMultigraph
end BachThesisLean
