import BachThesisLean.Cubic.TightCutMatchingExtension

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Common completions across a tight cut

For Pfaffian descent, two perfect matchings of one contraction that use the
same cut port must be compared after extension to the original graph.  The
opposite factor can be chosen once and reused for both glued matchings.  This
is the cancellation bridge needed by the relative-sign formalism.
-/

/-- Two perfect matchings of `G / W` through the same boundary port admit a
single common perfect matching of `G / Wᶜ` against which both can be glued. -/
theorem IsTightCut.exists_common_complement_for_contractSet_pair
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅)
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (P Q : Finset (ContractSetEdge G W))
    (hP : (G.contractSet W).IsPerfectMatching P)
    (hQ : (G.contractSet W).IsPerfectMatching Q)
    (i : Fin 3)
    (hPi : ((G.contractSetPorts W c) i).1 ∈ P)
    (hQi : ((G.contractSetPorts W c) i).1 ∈ Q) :
    ∃ PB : Finset (ContractComplementEdge G W),
      (G.contractComplement W).IsPerfectMatching PB ∧
      ((G.contractComplementPorts W c) i).1 ∈ PB ∧
      ((G.contractSet W).starProduct (G.contractComplement W)
        (contractSetRoot W) (contractComplementRoot W)
        (G.contractSetPorts W c) (G.contractComplementPorts W c)
        (Equiv.refl (Fin 3))).IsPerfectMatching
          ((G.contractSet W).starGluedMatching (G.contractComplement W)
            (contractSetRoot W) (contractComplementRoot W) P PB i) ∧
      ((G.contractSet W).starProduct (G.contractComplement W)
        (contractSetRoot W) (contractComplementRoot W)
        (G.contractSetPorts W c) (G.contractComplementPorts W c)
        (Equiv.refl (Fin 3))).IsPerfectMatching
          ((G.contractSet W).starGluedMatching (G.contractComplement W)
            (contractSetRoot W) (contractComplementRoot W) Q PB i) := by
  classical
  let A := G.contractSet W
  let B := G.contractComplement W
  let p := G.contractSetPorts W c
  let q := G.contractComplementPorts W c
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  obtain ⟨PB, hPB, hPBport⟩ :=
    B.exists_perfectMatching_containing_edge_of_cubic hCubic.1 (q i).1
  refine ⟨PB, hPB, ?_, ?_, ?_⟩
  · simpa [q] using hPBport
  · simpa [A, B, p, q] using
      A.starGluedMatching_isPerfectMatching B
        (contractSetRoot W) (contractComplementRoot W) p q
        (Equiv.refl (Fin 3)) P PB i hP hPB
        (by simpa [p] using hPi) (by simpa [q] using hPBport)
  · simpa [A, B, p, q] using
      A.starGluedMatching_isPerfectMatching B
        (contractSetRoot W) (contractComplementRoot W) p q
        (Equiv.refl (Fin 3)) Q PB i hQ hPB
        (by simpa [p] using hQi) (by simpa [q] using hPBport)

/-- Symmetrically, two perfect matchings of `G / Wᶜ` through the same boundary
port admit one common perfect matching of `G / W` against which both glue. -/
theorem IsTightCut.exists_common_set_for_contractComplement_pair
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅)
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (P Q : Finset (ContractComplementEdge G W))
    (hP : (G.contractComplement W).IsPerfectMatching P)
    (hQ : (G.contractComplement W).IsPerfectMatching Q)
    (i : Fin 3)
    (hPi : ((G.contractComplementPorts W c) i).1 ∈ P)
    (hQi : ((G.contractComplementPorts W c) i).1 ∈ Q) :
    ∃ PA : Finset (ContractSetEdge G W),
      (G.contractSet W).IsPerfectMatching PA ∧
      ((G.contractSetPorts W c) i).1 ∈ PA ∧
      ((G.contractSet W).starProduct (G.contractComplement W)
        (contractSetRoot W) (contractComplementRoot W)
        (G.contractSetPorts W c) (G.contractComplementPorts W c)
        (Equiv.refl (Fin 3))).IsPerfectMatching
          ((G.contractSet W).starGluedMatching (G.contractComplement W)
            (contractSetRoot W) (contractComplementRoot W) PA P i) ∧
      ((G.contractSet W).starProduct (G.contractComplement W)
        (contractSetRoot W) (contractComplementRoot W)
        (G.contractSetPorts W c) (G.contractComplementPorts W c)
        (Equiv.refl (Fin 3))).IsPerfectMatching
          ((G.contractSet W).starGluedMatching (G.contractComplement W)
            (contractSetRoot W) (contractComplementRoot W) PA Q i) := by
  classical
  let A := G.contractSet W
  let B := G.contractComplement W
  let p := G.contractSetPorts W c
  let q := G.contractComplementPorts W c
  have hCubic := hT.right_oriented_contractions_cubic hconn hG hOrient
  obtain ⟨PA, hPA, hPAport⟩ :=
    A.exists_perfectMatching_containing_edge_of_cubic hCubic.2 (p i).1
  refine ⟨PA, hPA, ?_, ?_, ?_⟩
  · simpa [p] using hPAport
  · simpa [A, B, p, q] using
      A.starGluedMatching_isPerfectMatching B
        (contractSetRoot W) (contractComplementRoot W) p q
        (Equiv.refl (Fin 3)) PA P i hPA hP
        (by simpa [p] using hPAport) (by simpa [q] using hPi)
  · simpa [A, B, p, q] using
      A.starGluedMatching_isPerfectMatching B
        (contractSetRoot W) (contractComplementRoot W) p q
        (Equiv.refl (Fin 3)) PA Q i hPA hQ
        (by simpa [p] using hPAport) (by simpa [q] using hQi)

end BipartiteMultigraph
end BachThesisLean
