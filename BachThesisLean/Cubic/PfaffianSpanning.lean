import BachThesisLean.Cubic.PfaffianReference
import BachThesisLean.Cubic.EdgeRestriction

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Pfaffian closure under spanning edge restriction

This is part (a) of the manuscript's elementary Pfaffian closure lemma.  A
spanning subgraph keeps both vertex shores and deletes some actual edge copies.
Every perfect matching of the restricted graph therefore lifts to a perfect
matching of the ambient graph.  Its matching permutation is unchanged, and the
product of the restricted edge signs is exactly the ambient product over the
lifted set of copies.
-/

/-- Products over a restricted edge set agree with products over the lifted
ambient set of actual copies. -/
theorem prod_liftRestrictedEdgeSet
    (S : Finset E) (T : Finset {e : E // e ∈ S})
    {M : Type*} [CommMonoid M] (f : E → M) :
    (∏ e ∈ liftRestrictedEdgeSet S T, f e) =
      ∏ a ∈ T, f a.val := by
  simpa [liftRestrictedEdgeSet, restrictedEdgeEmbedding] using
    (Finset.prod_map T (restrictedEdgeEmbedding S) f)

/-- Lifting a restricted perfect matching does not change the right vertex
matched to any given left vertex. -/
theorem PerfectMatching.lift_restrictEdges_matchingRight
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (P : (G.restrictEdges S).PerfectMatching) (x : X) :
    (P.lift_restrictEdges G S).property.matchingRight x =
      P.property.matchingRight x := by
  let a := P.property.matchingEdge x
  have haP : a ∈ P.val := by
    simpa [a] using P.property.matchingEdge_mem x
  have haLift : a.val ∈ liftRestrictedEdgeSet S P.val :=
    (mem_liftRestrictedEdgeSet_iff S P.val a.val).2 ⟨a, haP, rfl⟩
  have haLeft : G.left a.val = x := by
    change (G.restrictEdges S).left a = x
    exact P.property.matchingEdge_left x
  have hEdge :
      (P.lift_restrictEdges G S).property.matchingEdge x = a.val :=
    (P.lift_restrictEdges G S).property.matchingEdge_eq_of_mem_left
      x haLift haLeft
  change G.right ((P.lift_restrictEdges G S).property.matchingEdge x) =
    G.right a.val
  rw [hEdge]

/-- Hence lifting preserves the shore equivalence represented by the matching. -/
theorem PerfectMatching.lift_restrictEdges_shoreEquiv
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (P : (G.restrictEdges S).PerfectMatching) :
    (P.lift_restrictEdges G S).shoreEquiv = P.shoreEquiv := by
  ext x
  exact P.lift_restrictEdges_matchingRight G S x

/-- The relative matching permutation is unchanged by lifting. -/
theorem PerfectMatching.lift_restrictEdges_referencePerm
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (reference : X ≃ Y)
    (P : (G.restrictEdges S).PerfectMatching) :
    (P.lift_restrictEdges G S).referencePerm reference =
      P.referencePerm reference := by
  simp only [PerfectMatching.referencePerm]
  rw [P.lift_restrictEdges_shoreEquiv G S]

/-- The full signed determinant term of a restricted perfect matching equals
that of its ambient lift when the restricted signing is obtained by restriction
of the ambient edge-copy signing. -/
theorem PerfectMatching.lift_restrictEdges_signedTerm
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (reference : X ≃ Y) (edgeSign : E → ℤˣ)
    (P : (G.restrictEdges S).PerfectMatching) :
    (P.lift_restrictEdges G S).signedTerm reference edgeSign =
      P.signedTerm reference (fun e => edgeSign e.val) := by
  rw [PerfectMatching.signedTerm, PerfectMatching.signedTerm,
    P.lift_restrictEdges_referencePerm G S reference,
    PerfectMatching.lift_restrictEdges_val,
    prod_liftRestrictedEdgeSet]

/-- Any spanning edge restriction of a graph with a Pfaffian signing inherits
a Pfaffian signing by restricting the signs to the surviving actual copies. -/
def PfaffianSigning.restrictEdges
    {reference : X ≃ Y} (S : Finset E)
    (Pfs : PfaffianSigning G reference) :
    PfaffianSigning (G.restrictEdges S) reference where
  edgeSign e := Pfs.edgeSign e.val
  terms_eq := by
    intro P Q
    rw [← P.lift_restrictEdges_signedTerm G S reference Pfs.edgeSign,
      ← Q.lift_restrictEdges_signedTerm G S reference Pfs.edgeSign]
    exact Pfs.terms_eq (P.lift_restrictEdges G S) (Q.lift_restrictEdges G S)

@[simp] theorem PfaffianSigning.restrictEdges_edgeSign
    {reference : X ≃ Y} (S : Finset E)
    (Pfs : PfaffianSigning G reference) (e : {e : E // e ∈ S}) :
    (Pfs.restrictEdges S).edgeSign e = Pfs.edgeSign e.val := rfl

/-- Witness-level form of spanning-subgraph Pfaffian closure. -/
def PfaffianWitness.restrictEdges
    (W : PfaffianWitness G) (S : Finset E) :
    PfaffianWitness (G.restrictEdges S) where
  reference := W.reference
  signing := W.signing.restrictEdges S

/-- Existence form of spanning-subgraph Pfaffian closure. -/
theorem exists_pfaffianWitness_restrictEdges
    (S : Finset E) (h : Nonempty (PfaffianWitness G)) :
    Nonempty (PfaffianWitness (G.restrictEdges S)) := by
  rcases h with ⟨W⟩
  exact ⟨W.restrictEdges S⟩

end BipartiteMultigraph
end BachThesisLean
