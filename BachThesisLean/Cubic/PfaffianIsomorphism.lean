import BachThesisLean.Cubic.PfaffianReference
import BachThesisLean.Cubic.Isomorphism

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe u v w u' v' w'

variable {X : Type u} {Y : Type v} {E : Type w}
variable {X' : Type u'} {Y' : Type v'} {E' : Type w'}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [Fintype X'] [Fintype Y'] [Fintype E']
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq E']
variable {G : BipartiteMultigraph X Y E}
variable {H : BipartiteMultigraph X' Y' E'}

/-!
# Pfaffian witnesses under graph isomorphism

A graph isomorphism relabels both shores and the actual edge-copy type.  A
perfect matching therefore transports by mapping its selected copies, while a
reference shore equivalence is conjugated by the two vertex relabellings.  The
relative matching permutation is conjugated by the left-shore equivalence, so
its sign is unchanged; the product of edge signs is unchanged after pulling
the signing through the edge-copy equivalence.
-/

namespace GraphIso

/-- Transport a perfect matching along a graph isomorphism. -/
noncomputable def mapPerfectMatching (φ : GraphIso G H)
    (P : G.PerfectMatching) : H.PerfectMatching :=
  ⟨φ.mapEdges P.val, (φ.isPerfectMatching_map_iff P.val).2 P.property⟩

@[simp] theorem mapPerfectMatching_val (φ : GraphIso G H)
    (P : G.PerfectMatching) :
    (φ.mapPerfectMatching P).val = φ.mapEdges P.val := rfl

/-- Transport a fixed identification of the two shores through the vertex
relabelings. -/
def mapReference (φ : GraphIso G H) (reference : X ≃ Y) : X' ≃ Y' :=
  φ.leftEquiv.symm.trans (reference.trans φ.rightEquiv)

/-- Transport an edge signing by pulling labels back along the edge-copy
equivalence. -/
def mapEdgeSign (φ : GraphIso G H) (edgeSign : E → ℤˣ) : E' → ℤˣ :=
  fun e' => edgeSign (φ.edgeEquiv.symm e')

@[simp] theorem mapEdgeSign_apply (φ : GraphIso G H) (edgeSign : E → ℤˣ)
    (e : E) :
    φ.mapEdgeSign edgeSign (φ.edgeEquiv e) = edgeSign e := by
  simp [mapEdgeSign]

/-- Mapping a set back through the inverse edge equivalence and then forward
recovers the original target set. -/
@[simp] theorem mapEdges_mapEdges_symm (φ : GraphIso G H) (S : Finset E') :
    φ.mapEdges (φ.symm.mapEdges S) = S := by
  ext e'
  obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
  rw [φ.mem_mapEdges_apply]
  simpa [GraphIso.symm] using
    (φ.symm.mem_mapEdges_apply S (φ.edgeEquiv e))

/-- Consequently inverse transport followed by forward transport fixes every
perfect matching. -/
@[simp] theorem mapPerfectMatching_symm_map (φ : GraphIso G H)
    (P : H.PerfectMatching) :
    φ.mapPerfectMatching (φ.symm.mapPerfectMatching P) = P := by
  apply Subtype.ext
  exact φ.mapEdges_mapEdges_symm P.val

/-- The shore equivalence represented by a mapped matching is the old shore
equivalence conjugated by the two vertex relabelings. -/
theorem mapPerfectMatching_shoreEquiv (φ : GraphIso G H)
    (P : G.PerfectMatching) :
    (φ.mapPerfectMatching P).shoreEquiv =
      φ.leftEquiv.symm.trans (P.shoreEquiv.trans φ.rightEquiv) := by
  ext x'
  obtain ⟨x, rfl⟩ := φ.leftEquiv.surjective x'
  have hmem :
      φ.edgeEquiv (P.property.matchingEdge x) ∈
        (φ.mapPerfectMatching P).val := by
    change φ.edgeEquiv (P.property.matchingEdge x) ∈ φ.mapEdges P.val
    exact (φ.mem_mapEdges_apply P.val (P.property.matchingEdge x)).2
      (P.property.matchingEdge_mem x)
  have hleft :
      H.left (φ.edgeEquiv (P.property.matchingEdge x)) = φ.leftEquiv x := by
    calc
      H.left (φ.edgeEquiv (P.property.matchingEdge x)) =
          φ.leftEquiv (G.left (P.property.matchingEdge x)) :=
        φ.map_left (P.property.matchingEdge x)
      _ = φ.leftEquiv x := congrArg φ.leftEquiv (P.property.matchingEdge_left x)
  have hedge :
      (φ.mapPerfectMatching P).property.matchingEdge (φ.leftEquiv x) =
        φ.edgeEquiv (P.property.matchingEdge x) :=
    (φ.mapPerfectMatching P).property.matchingEdge_eq_of_mem_left
      (φ.leftEquiv x) hmem hleft
  change
    H.right ((φ.mapPerfectMatching P).property.matchingEdge (φ.leftEquiv x)) =
      (φ.leftEquiv.symm.trans (P.shoreEquiv.trans φ.rightEquiv))
        (φ.leftEquiv x)
  rw [hedge, φ.map_right]
  simp [IsPerfectMatching.matchingRight]

/-- Relative matching permutations are conjugated by the left-shore
relabeling. -/
theorem mapPerfectMatching_referencePerm (φ : GraphIso G H)
    (reference : X ≃ Y) (P : G.PerfectMatching) :
    (φ.mapPerfectMatching P).referencePerm (φ.mapReference reference) =
      φ.leftEquiv.permCongr (P.referencePerm reference) := by
  rw [PerfectMatching.referencePerm, PerfectMatching.referencePerm,
    φ.mapPerfectMatching_shoreEquiv P]
  ext x'
  simp [mapReference, Equiv.permCongr_def]

/-- Products of transported edge signs over transported edge sets are
unchanged. -/
theorem prod_mapEdges_mapEdgeSign (φ : GraphIso G H) (S : Finset E)
    (edgeSign : E → ℤˣ) :
    (∏ e' ∈ φ.mapEdges S, φ.mapEdgeSign edgeSign e') =
      ∏ e ∈ S, edgeSign e := by
  simpa [mapEdges, mapEdgeSign] using
    (Finset.prod_map S φ.edgeEquiv.toEmbedding (φ.mapEdgeSign edgeSign))

/-- A full signed determinant term is invariant under graph isomorphism when
both the shore reference and edge signing are transported canonically. -/
theorem mapPerfectMatching_signedTerm (φ : GraphIso G H)
    (reference : X ≃ Y) (edgeSign : E → ℤˣ)
    (P : G.PerfectMatching) :
    (φ.mapPerfectMatching P).signedTerm
        (φ.mapReference reference) (φ.mapEdgeSign edgeSign) =
      P.signedTerm reference edgeSign := by
  rw [PerfectMatching.signedTerm, PerfectMatching.signedTerm,
    φ.mapPerfectMatching_referencePerm reference P,
    Equiv.Perm.sign_permCongr, φ.mapPerfectMatching_val,
    φ.prod_mapEdges_mapEdgeSign]

end GraphIso

/-- A Pfaffian signing transports across a graph isomorphism. -/
noncomputable def PfaffianSigning.map
    {reference : X ≃ Y} (S : PfaffianSigning G reference)
    (φ : GraphIso G H) :
    PfaffianSigning H (φ.mapReference reference) where
  edgeSign := φ.mapEdgeSign S.edgeSign
  terms_eq := by
    intro P R
    let P0 : G.PerfectMatching := φ.symm.mapPerfectMatching P
    let R0 : G.PerfectMatching := φ.symm.mapPerfectMatching R
    calc
      P.signedTerm (φ.mapReference reference) (φ.mapEdgeSign S.edgeSign) =
          P0.signedTerm reference S.edgeSign := by
            simpa [P0] using
              φ.mapPerfectMatching_signedTerm reference S.edgeSign P0
      _ = R0.signedTerm reference S.edgeSign := S.terms_eq P0 R0
      _ = R.signedTerm (φ.mapReference reference) (φ.mapEdgeSign S.edgeSign) := by
            symm
            simpa [R0] using
              φ.mapPerfectMatching_signedTerm reference S.edgeSign R0

/-- Witness-level transport of Pfaffianness across graph isomorphism. -/
noncomputable def PfaffianWitness.map
    (W : PfaffianWitness G) (φ : GraphIso G H) : PfaffianWitness H where
  reference := φ.mapReference W.reference
  signing := W.signing.map φ

/-- Existence of a packaged Pfaffian witness is an isomorphism invariant. -/
theorem GraphIso.pfaffianWitness_nonempty_iff (φ : GraphIso G H) :
    Nonempty (PfaffianWitness H) ↔ Nonempty (PfaffianWitness G) := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.map φ.symm⟩
  · rintro ⟨W⟩
    exact ⟨W.map φ⟩

end BipartiteMultigraph
end BachThesisLean
