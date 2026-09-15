import BachThesisLean.Cubic.Isomorphism

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w u' v' w'

variable {X : Type u} {Y : Type v} {E : Type w}
variable {X' : Type u'} {Y' : Type v'} {E' : Type w'}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [Fintype X'] [Fintype Y'] [Fintype E']
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq E']
variable {G : BipartiteMultigraph X Y E} {H : BipartiteMultigraph X' Y' E'}

namespace GraphIso

/-- The induced equivalence on the manuscript's tagged vertex-or-edge
objects. -/
def elementEquiv (φ : GraphIso G H) :
    ((X ⊕ Y) ⊕ E) ≃ ((X' ⊕ Y') ⊕ E') :=
  Equiv.sumCongr φ.vertexEquiv φ.edgeEquiv

@[simp] theorem elementEquiv_vertex (φ : GraphIso G H) (v : X ⊕ Y) :
    φ.elementEquiv (.inl v) = .inl (φ.vertexEquiv v) := rfl

@[simp] theorem elementEquiv_edge (φ : GraphIso G H) (e : E) :
    φ.elementEquiv (.inr e) = .inr (φ.edgeEquiv e) := rfl

/-- Membership of a tagged vertex/edge in a complementary factor component
transports along graph isomorphisms. -/
theorem componentContains_map (φ : GraphIso G H) (S : Finset E)
    {root : X ⊕ Y} {a : (X ⊕ Y) ⊕ E}
    (h : G.ComponentContains S root a) :
    H.ComponentContains (φ.mapEdges S) (φ.vertexEquiv root)
      (φ.elementEquiv a) := by
  cases a with
  | inl v =>
      exact φ.factorReachable_map S h
  | inr e =>
      exact φ.componentCarries_map S h

/-- EVP transports along a graph isomorphism. -/
theorem hasEVP_map (φ : GraphIso G H) (h : G.HasEVP) : H.HasEVP := by
  intro e' v'
  obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
  obtain ⟨v, rfl⟩ := φ.vertexEquiv.surjective v'
  obtain ⟨P, root, hP, he, hv⟩ := h e v
  refine ⟨φ.mapEdges P, φ.vertexEquiv root,
    (φ.isPerfectMatching_map_iff P).2 hP, ?_, ?_⟩
  · simpa using φ.componentCarries_map Pᶜ he
  · simpa using φ.factorReachable_map Pᶜ hv

/-- EVP is invariant under graph isomorphism. -/
theorem hasEVP_iff (φ : GraphIso G H) : H.HasEVP ↔ G.HasEVP := by
  constructor
  · exact φ.symm.hasEVP_map
  · exact φ.hasEVP_map

/-- The full tagged two-element property transports along graph isomorphisms. -/
theorem hasTwoEP_map (φ : GraphIso G H) (h : G.HasTwoEP) : H.HasTwoEP := by
  intro a' b' hab'
  obtain ⟨a, rfl⟩ := φ.elementEquiv.surjective a'
  obtain ⟨b, rfl⟩ := φ.elementEquiv.surjective b'
  have hab : a ≠ b := by
    intro hEq
    apply hab'
    exact congrArg φ.elementEquiv hEq
  obtain ⟨P, root, hP, ha, hb⟩ := h a b hab
  refine ⟨φ.mapEdges P, φ.vertexEquiv root,
    (φ.isPerfectMatching_map_iff P).2 hP, ?_, ?_⟩
  · simpa using φ.componentContains_map Pᶜ ha
  · simpa using φ.componentContains_map Pᶜ hb

/-- The full tagged two-element property is an isomorphism invariant. -/
theorem hasTwoEP_iff (φ : GraphIso G H) : H.HasTwoEP ↔ G.HasTwoEP := by
  constructor
  · exact φ.symm.hasTwoEP_map
  · exact φ.hasTwoEP_map

end GraphIso
end BipartiteMultigraph
end BachThesisLean
