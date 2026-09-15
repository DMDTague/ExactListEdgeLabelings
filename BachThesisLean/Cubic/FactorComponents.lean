import BachThesisLean.Cubic.Foundations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Finite complementary-factor components

The star-product port criterion needs an edge-copy-aware way to count a
connected component of a selected factor.  These definitions keep the two
bipartition shores separate and count the same component from either shore.
-/

/-- Left-shore vertices in the selected-factor component of `root`. -/
noncomputable def factorComponentLeft
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => G.FactorReachable S root (.inl x))

/-- Right-shore vertices in the selected-factor component of `root`. -/
noncomputable def factorComponentRight
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) : Finset Y := by
  classical
  exact Finset.univ.filter (fun y => G.FactorReachable S root (.inr y))

/-- Selected edge copies carried by the selected-factor component of `root`. -/
noncomputable def factorComponentEdges
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) : Finset E := by
  classical
  exact S.filter (fun e => G.FactorReachable S root (.inl (G.left e)))

@[simp] theorem mem_factorComponentLeft
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) (x : X) :
    x ∈ G.factorComponentLeft S root ↔ G.FactorReachable S root (.inl x) := by
  classical
  simp [factorComponentLeft]

@[simp] theorem mem_factorComponentRight
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) (y : Y) :
    y ∈ G.factorComponentRight S root ↔ G.FactorReachable S root (.inr y) := by
  classical
  simp [factorComponentRight]

@[simp] theorem mem_factorComponentEdges
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) (e : E) :
    e ∈ G.factorComponentEdges S root ↔
      e ∈ S ∧ G.FactorReachable S root (.inl (G.left e)) := by
  classical
  simp [factorComponentEdges]

/-- For a selected edge, reachability of either endpoint from a fixed root is
equivalent. -/
theorem factorReachable_right_iff_left_of_mem
    (G : BipartiteMultigraph X Y E) {S : Finset E} {root : X ⊕ Y}
    {e : E} (he : e ∈ S) :
    G.FactorReachable S root (.inr (G.right e)) ↔
      G.FactorReachable S root (.inl (G.left e)) := by
  constructor
  · intro h
    exact h.trans (G.factorReachable_endpoints he).symm
  · intro h
    exact h.trans (G.factorReachable_endpoints he)

/-- Component edges are exactly the selected edges incident with the left
vertices of the component. -/
theorem factorComponentEdges_eq_biUnion_left
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) :
    G.factorComponentEdges S root =
      (G.factorComponentLeft S root).biUnion
        (fun x => G.selectedIncident S (.inl x)) := by
  classical
  ext e
  constructor
  · intro he
    have he' := (G.mem_factorComponentEdges S root e).1 he
    rw [Finset.mem_biUnion]
    refine ⟨G.left e, ?_, ?_⟩
    · exact (G.mem_factorComponentLeft S root (G.left e)).2 he'.2
    · exact (G.mem_selectedIncident S (.inl (G.left e)) e).2 ⟨he'.1, rfl⟩
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨x, hx, hex⟩ := he
    have hex' := (G.mem_selectedIncident S (.inl x) e).1 hex
    have hx' := (G.mem_factorComponentLeft S root x).1 hx
    apply (G.mem_factorComponentEdges S root e).2
    refine ⟨hex'.1, ?_⟩
    rw [hex'.2]
    exact hx'

/-- Right-shore form of `factorComponentEdges_eq_biUnion_left`. -/
theorem factorComponentEdges_eq_biUnion_right
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) :
    G.factorComponentEdges S root =
      (G.factorComponentRight S root).biUnion
        (fun y => G.selectedIncident S (.inr y)) := by
  classical
  ext e
  constructor
  · intro he
    have he' := (G.mem_factorComponentEdges S root e).1 he
    have hright : G.FactorReachable S root (.inr (G.right e)) :=
      (G.factorReachable_right_iff_left_of_mem he'.1).2 he'.2
    rw [Finset.mem_biUnion]
    refine ⟨G.right e, ?_, ?_⟩
    · exact (G.mem_factorComponentRight S root (G.right e)).2 hright
    · exact (G.mem_selectedIncident S (.inr (G.right e)) e).2 ⟨he'.1, rfl⟩
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨y, hy, hey⟩ := he
    have hey' := (G.mem_selectedIncident S (.inr y) e).1 hey
    have hy' := (G.mem_factorComponentRight S root y).1 hy
    have hright : G.FactorReachable S root (.inr (G.right e)) := by
      rw [hey'.2]
      exact hy'
    apply (G.mem_factorComponentEdges S root e).2
    exact ⟨hey'.1, (G.factorReachable_right_iff_left_of_mem hey'.1).1 hright⟩

/-- Selected-incidence fibres at distinct left vertices remain disjoint. -/
theorem selectedIncident_left_pairwiseDisjoint
    (G : BipartiteMultigraph X Y E) (S : Finset E) (U : Finset X) :
    (U : Set X).PairwiseDisjoint (fun x => G.selectedIncident S (.inl x)) := by
  intro x _ x' _ hxx'
  change Disjoint (G.selectedIncident S (.inl x))
    (G.selectedIncident S (.inl x'))
  rw [Finset.disjoint_left]
  intro e hex hex'
  have hx := ((G.mem_selectedIncident S (.inl x) e).1 hex).2
  have hx' := ((G.mem_selectedIncident S (.inl x') e).1 hex').2
  exact hxx' (hx.symm.trans hx')

/-- Selected-incidence fibres at distinct right vertices remain disjoint. -/
theorem selectedIncident_right_pairwiseDisjoint
    (G : BipartiteMultigraph X Y E) (S : Finset E) (V : Finset Y) :
    (V : Set Y).PairwiseDisjoint (fun y => G.selectedIncident S (.inr y)) := by
  intro y _ y' _ hyy'
  change Disjoint (G.selectedIncident S (.inr y))
    (G.selectedIncident S (.inr y'))
  rw [Finset.disjoint_left]
  intro e hey hey'
  have hy := ((G.mem_selectedIncident S (.inr y) e).1 hey).2
  have hy' := ((G.mem_selectedIncident S (.inr y') e).1 hey').2
  exact hyy' (hy.symm.trans hy')

/-- Counting the component edges from the left shore gives the sum of the
selected degrees of its left vertices. -/
theorem factorComponentEdges_card_eq_sum_left
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) :
    (G.factorComponentEdges S root).card =
      ∑ x ∈ G.factorComponentLeft S root,
        (G.selectedIncident S (.inl x)).card := by
  rw [G.factorComponentEdges_eq_biUnion_left S root]
  exact Finset.card_biUnion (G.selectedIncident_left_pairwiseDisjoint S _)

/-- Counting the same component from the right shore gives the corresponding
right-degree sum. -/
theorem factorComponentEdges_card_eq_sum_right
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) :
    (G.factorComponentEdges S root).card =
      ∑ y ∈ G.factorComponentRight S root,
        (G.selectedIncident S (.inr y)).card := by
  rw [G.factorComponentEdges_eq_biUnion_right S root]
  exact Finset.card_biUnion (G.selectedIncident_right_pairwiseDisjoint S _)

/-- Bipartite degree balance inside a finite selected-factor component. -/
theorem factorComponent_degree_sum_balance
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) :
    (∑ x ∈ G.factorComponentLeft S root,
        (G.selectedIncident S (.inl x)).card) =
      ∑ y ∈ G.factorComponentRight S root,
        (G.selectedIncident S (.inr y)).card := by
  rw [← G.factorComponentEdges_card_eq_sum_left S root,
    ← G.factorComponentEdges_card_eq_sum_right S root]

end BipartiteMultigraph
end BachThesisLean
