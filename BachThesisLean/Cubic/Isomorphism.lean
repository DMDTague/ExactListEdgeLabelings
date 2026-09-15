import BachThesisLean.Cubic.PortMasks

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w u' v' w'

variable {X : Type u} {Y : Type v} {E : Type w}
variable {X' : Type u'} {Y' : Type v'} {E' : Type w'}

/-!
# Isomorphisms of bipartite edge-copy multigraphs

Tight-cut contractions are most naturally compared with the explicit star
product only up to relabelling of vertices and edge copies.  This file records
that relabelling once and proves transport for the matching/component notions
used by EEP.  Parallel edges are preserved because `edgeEquiv` acts on actual
edge copies.
-/

/-- A bipartite multigraph isomorphism preserves both shore endpoint maps and
is allowed to relabel all three underlying finite types. -/
structure GraphIso
    (G : BipartiteMultigraph X Y E)
    (H : BipartiteMultigraph X' Y' E') where
  leftEquiv : X ≃ X'
  rightEquiv : Y ≃ Y'
  edgeEquiv : E ≃ E'
  map_left : ∀ e, H.left (edgeEquiv e) = leftEquiv (G.left e)
  map_right : ∀ e, H.right (edgeEquiv e) = rightEquiv (G.right e)

namespace GraphIso

variable [Fintype X] [Fintype Y] [Fintype E]
variable [Fintype X'] [Fintype Y'] [Fintype E']
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq E']
variable {G : BipartiteMultigraph X Y E} {H : BipartiteMultigraph X' Y' E'}

/-- The induced equivalence on tagged bipartite vertices. -/
def vertexEquiv (φ : GraphIso G H) : X ⊕ Y ≃ X' ⊕ Y' :=
  Equiv.sumCongr φ.leftEquiv φ.rightEquiv

@[simp] theorem vertexEquiv_inl (φ : GraphIso G H) (x : X) :
    φ.vertexEquiv (.inl x) = .inl (φ.leftEquiv x) := rfl

@[simp] theorem vertexEquiv_inr (φ : GraphIso G H) (y : Y) :
    φ.vertexEquiv (.inr y) = .inr (φ.rightEquiv y) := rfl

/-- Transport an edge subset along the edge-copy equivalence. -/
noncomputable def mapEdges (φ : GraphIso G H) (S : Finset E) : Finset E' :=
  S.map φ.edgeEquiv.toEmbedding

@[simp] theorem mem_mapEdges_apply (φ : GraphIso G H) (S : Finset E) (e : E) :
    φ.edgeEquiv e ∈ φ.mapEdges S ↔ e ∈ S := by
  simp [mapEdges]

@[simp] theorem mapEdges_univ (φ : GraphIso G H) :
    φ.mapEdges (Finset.univ : Finset E) = Finset.univ := by
  ext e'
  obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
  simp

@[simp] theorem mapEdges_compl (φ : GraphIso G H) (S : Finset E) :
    φ.mapEdges Sᶜ = (φ.mapEdges S)ᶜ := by
  ext e'
  obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
  simp

/-- Incidence is preserved exactly by the three relabellings. -/
theorem incident_map_iff (φ : GraphIso G H) (e : E) (v : X ⊕ Y) :
    H.Incident (φ.edgeEquiv e) (φ.vertexEquiv v) ↔ G.Incident e v := by
  cases v with
  | inl x =>
      change H.left (φ.edgeEquiv e) = φ.leftEquiv x ↔ G.left e = x
      rw [φ.map_left e]
      exact φ.leftEquiv.injective.eq_iff
  | inr y =>
      change H.right (φ.edgeEquiv e) = φ.rightEquiv y ↔ G.right e = y
      rw [φ.map_right e]
      exact φ.rightEquiv.injective.eq_iff

/-- Selected incidence sets commute with graph isomorphism. -/
theorem selectedIncident_map (φ : GraphIso G H) (S : Finset E) (v : X ⊕ Y) :
    H.selectedIncident (φ.mapEdges S) (φ.vertexEquiv v) =
      (G.selectedIncident S v).map φ.edgeEquiv.toEmbedding := by
  ext e'
  obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
  simp [φ.incident_map_iff]

/-- Spanning-factor degrees are invariant under relabelling. -/
theorem isSpanningFactor_map_iff (φ : GraphIso G H) (d : ℕ) (S : Finset E) :
    H.IsSpanningFactor d (φ.mapEdges S) ↔ G.IsSpanningFactor d S := by
  constructor
  · intro h v
    have hv := h (φ.vertexEquiv v)
    rw [φ.selectedIncident_map, Finset.card_map] at hv
    exact hv
  · intro h v'
    obtain ⟨v, rfl⟩ := φ.vertexEquiv.surjective v'
    rw [φ.selectedIncident_map, Finset.card_map]
    exact h v

/-- Perfect matchings are invariant under graph isomorphism. -/
theorem isPerfectMatching_map_iff (φ : GraphIso G H) (S : Finset E) :
    H.IsPerfectMatching (φ.mapEdges S) ↔ G.IsPerfectMatching S :=
  φ.isSpanningFactor_map_iff 1 S

/-- Two-factors are invariant under graph isomorphism. -/
theorem isTwoFactor_map_iff (φ : GraphIso G H) (S : Finset E) :
    H.IsTwoFactor (φ.mapEdges S) ↔ G.IsTwoFactor S :=
  φ.isSpanningFactor_map_iff 2 S

/-- Cubicity is invariant under relabelling. -/
theorem isCubic_iff (φ : GraphIso G H) : H.IsCubic ↔ G.IsCubic := by
  constructor
  · intro h v
    have hv := h (φ.vertexEquiv v)
    change (H.selectedIncident Finset.univ (φ.vertexEquiv v)).card = 3 at hv
    rw [← φ.mapEdges_univ, φ.selectedIncident_map, Finset.card_map] at hv
    exact hv
  · intro h v'
    obtain ⟨v, rfl⟩ := φ.vertexEquiv.surjective v'
    change (H.selectedIncident Finset.univ (φ.vertexEquiv v)).card = 3
    rw [← φ.mapEdges_univ, φ.selectedIncident_map, Finset.card_map]
    exact h v

/-- One selected adjacency transports along a graph isomorphism. -/
theorem selectedAdjacent_map (φ : GraphIso G H) (S : Finset E)
    {u v : X ⊕ Y} (h : G.SelectedAdjacent S u v) :
    H.SelectedAdjacent (φ.mapEdges S) (φ.vertexEquiv u) (φ.vertexEquiv v) := by
  rcases h with ⟨e, he, hdir | hdir⟩
  · refine ⟨φ.edgeEquiv e, (φ.mem_mapEdges_apply S e).2 he, Or.inl ?_⟩
    rcases hdir with ⟨rfl, rfl⟩
    constructor
    · simp [φ.map_left]
    · simp [φ.map_right]
  · refine ⟨φ.edgeEquiv e, (φ.mem_mapEdges_apply S e).2 he, Or.inr ?_⟩
    rcases hdir with ⟨rfl, rfl⟩
    constructor
    · simp [φ.map_right]
    · simp [φ.map_left]

/-- Factor reachability transports along a graph isomorphism. -/
theorem factorReachable_map (φ : GraphIso G H) (S : Finset E)
    {u v : X ⊕ Y} (h : G.FactorReachable S u v) :
    H.FactorReachable (φ.mapEdges S) (φ.vertexEquiv u) (φ.vertexEquiv v) := by
  exact Relation.ReflTransGen.lift φ.vertexEquiv
    (fun _ _ hab => φ.selectedAdjacent_map S hab) h

/-- Edge-component membership transports along a graph isomorphism. -/
theorem componentCarries_map (φ : GraphIso G H) (S : Finset E)
    {root : X ⊕ Y} {e : E} (h : G.ComponentCarries S root e) :
    H.ComponentCarries (φ.mapEdges S) (φ.vertexEquiv root) (φ.edgeEquiv e) := by
  refine ⟨(φ.mem_mapEdges_apply S e).2 h.1, ?_⟩
  have hr := φ.factorReachable_map S h.2
  simpa [φ.map_left] using hr

/-- Connectedness is invariant under relabelling. -/
theorem isConnected_map (φ : GraphIso G H) (h : G.IsConnected) : H.IsConnected := by
  rcases h with ⟨⟨v⟩, hconn⟩
  refine ⟨⟨φ.vertexEquiv v⟩, ?_⟩
  intro a b
  obtain ⟨a', rfl⟩ := φ.vertexEquiv.surjective a
  obtain ⟨b', rfl⟩ := φ.vertexEquiv.surjective b
  simpa using φ.factorReachable_map Finset.univ (hconn a' b')

/-- Symmetry of graph isomorphism. -/
def symm (φ : GraphIso G H) : GraphIso H G where
  leftEquiv := φ.leftEquiv.symm
  rightEquiv := φ.rightEquiv.symm
  edgeEquiv := φ.edgeEquiv.symm
  map_left := by
    intro e'
    obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
    rw [φ.map_left e]
    simp
  map_right := by
    intro e'
    obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
    rw [φ.map_right e]
    simp

/-- Connectedness is an isomorphism invariant. -/
theorem isConnected_iff (φ : GraphIso G H) : H.IsConnected ↔ G.IsConnected := by
  constructor
  · exact φ.symm.isConnected_map
  · exact φ.isConnected_map

/-- A pointwise two-edge witness transports along an isomorphism. -/
theorem edgePairWitness_map (φ : GraphIso G H) {e f : E}
    (h : G.EdgePairWitness e f) :
    H.EdgePairWitness (φ.edgeEquiv e) (φ.edgeEquiv f) := by
  rcases h with ⟨P, root, hP, he, hf⟩
  refine ⟨φ.mapEdges P, φ.vertexEquiv root,
    (φ.isPerfectMatching_map_iff P).2 hP, ?_, ?_⟩
  · simpa using φ.componentCarries_map Pᶜ he
  · simpa using φ.componentCarries_map Pᶜ hf

/-- EEP transports along a graph isomorphism. -/
theorem hasEEP_map (φ : GraphIso G H) (h : G.HasEEP) : H.HasEEP := by
  intro e' f' hef'
  obtain ⟨e, rfl⟩ := φ.edgeEquiv.surjective e'
  obtain ⟨f, rfl⟩ := φ.edgeEquiv.surjective f'
  have hef : e ≠ f := by
    intro hEq
    apply hef'
    exact congrArg φ.edgeEquiv hEq
  change H.EdgePairWitness (φ.edgeEquiv e) (φ.edgeEquiv f)
  exact φ.edgePairWitness_map (h.edgePairWitness hef)

/-- EEP is an isomorphism invariant. -/
theorem hasEEP_iff (φ : GraphIso G H) : H.HasEEP ↔ G.HasEEP := by
  constructor
  · exact φ.symm.hasEEP_map
  · exact φ.hasEEP_map

end GraphIso
end BipartiteMultigraph
end BachThesisLean
