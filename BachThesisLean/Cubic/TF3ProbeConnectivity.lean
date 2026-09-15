import BachThesisLean.Cubic.TF3ProbeDegrees

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- Embed an old vertex into the two-vertex probe. -/
def edgeProbeVertexMap : X ⊕ Y → (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y)
  | .inl x => .inl (.inl x)
  | .inr y => .inr (.inl y)

@[simp] theorem edgeProbeVertexMap_inl (x : X) :
    edgeProbeVertexMap (Sum.inl x : X ⊕ Y) =
      (.inl (.inl x) : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y)) := rfl

@[simp] theorem edgeProbeVertexMap_inr (y : Y) :
    edgeProbeVertexMap (Sum.inr y : X ⊕ Y) =
      (.inr (.inl y) : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y)) := rfl

/-- The deleted edge step is replaced in the probe by the explicit path
`x - eta - xi - y`. -/
theorem edgeProbe_deletedEdge_reachable
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).FactorReachable Finset.univ
      (edgeProbeVertexMap (.inl (G.left e)))
      (edgeProbeVertexMap (.inr (G.right e))) := by
  have hxEta :
      (G.edgeProbe e).FactorReachable Finset.univ
        (.inl (.inl (G.left e))) (.inr (probeEta : EdgeProbeRight Y)) := by
    simpa using
      (G.edgeProbe e).factorReachable_endpoints
        (show (.inr .xEta : EdgeProbeEdge e) ∈ (Finset.univ : Finset (EdgeProbeEdge e)) by
          simp)
  have hpole :
      (G.edgeProbe e).FactorReachable Finset.univ
        (.inl (probeXi : EdgeProbeLeft X)) (.inr (probeEta : EdgeProbeRight Y)) := by
    simpa using
      (G.edgeProbe e).factorReachable_endpoints
        (show (.inr .pole0 : EdgeProbeEdge e) ∈ (Finset.univ : Finset (EdgeProbeEdge e)) by
          simp)
  have hyXi :
      (G.edgeProbe e).FactorReachable Finset.univ
        (.inl (probeXi : EdgeProbeLeft X)) (.inr (.inl (G.right e))) := by
    simpa using
      (G.edgeProbe e).factorReachable_endpoints
        (show (.inr .yXi : EdgeProbeEdge e) ∈ (Finset.univ : Finset (EdgeProbeEdge e)) by
          simp)
  exact hxEta.trans (hpole.symm.trans hyXi)

/-- The endpoints of any old edge remain connected after inserting the probe.
For the deleted copy this is the three-edge replacement path; every other copy
survives literally. -/
theorem edgeProbe_oldEdge_reachable
    (G : BipartiteMultigraph X Y E) (e f : E) :
    (G.edgeProbe e).FactorReachable Finset.univ
      (edgeProbeVertexMap (.inl (G.left f)))
      (edgeProbeVertexMap (.inr (G.right f))) := by
  by_cases hfe : f = e
  · subst f
    exact G.edgeProbe_deletedEdge_reachable e
  · simpa using
      (G.edgeProbe e).factorReachable_endpoints
        (show (.inl ⟨f, hfe⟩ : EdgeProbeEdge e) ∈
            (Finset.univ : Finset (EdgeProbeEdge e)) by simp)

/-- One old adjacency step maps to reachability in the probe. -/
theorem edgeProbe_reachable_of_old_selectedAdjacent
    (G : BipartiteMultigraph X Y E) (e : E) {a b : X ⊕ Y}
    (h : G.SelectedAdjacent Finset.univ a b) :
    (G.edgeProbe e).FactorReachable Finset.univ
      (edgeProbeVertexMap a) (edgeProbeVertexMap b) := by
  rcases h with ⟨f, _, hab | hab⟩
  · rcases hab with ⟨rfl, rfl⟩
    exact G.edgeProbe_oldEdge_reachable e f
  · rcases hab with ⟨rfl, rfl⟩
    exact (G.edgeProbe_oldEdge_reachable e f).symm

/-- Every old factor-reachability path has a probe path between the embedded
old endpoints. -/
theorem edgeProbe_reachable_of_old_reachable
    (G : BipartiteMultigraph X Y E) (e : E) {a b : X ⊕ Y}
    (h : G.FactorReachable Finset.univ a b) :
    (G.edgeProbe e).FactorReachable Finset.univ
      (edgeProbeVertexMap a) (edgeProbeVertexMap b) := by
  induction h with
  | refl => exact (G.edgeProbe e).factorReachable_refl Finset.univ _
  | tail _ hab ih =>
      exact ih.trans (G.edgeProbe_reachable_of_old_selectedAdjacent e hab)

/-- The new right pole is attached directly to the embedded old left endpoint. -/
theorem edgeProbe_eta_reaches_oldLeft
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).FactorReachable Finset.univ
      (.inr (probeEta : EdgeProbeRight Y))
      (edgeProbeVertexMap (.inl (G.left e))) := by
  have h :=
    (G.edgeProbe e).factorReachable_endpoints
      (show (.inr .xEta : EdgeProbeEdge e) ∈ (Finset.univ : Finset (EdgeProbeEdge e)) by
        simp)
  simpa using h.symm

/-- The new left pole is attached directly to the embedded old right endpoint. -/
theorem edgeProbe_xi_reaches_oldRight
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).FactorReachable Finset.univ
      (.inl (probeXi : EdgeProbeLeft X))
      (edgeProbeVertexMap (.inr (G.right e))) := by
  simpa using
    (G.edgeProbe e).factorReachable_endpoints
      (show (.inr .yXi : EdgeProbeEdge e) ∈ (Finset.univ : Finset (EdgeProbeEdge e)) by
        simp)

/-- The two-vertex probe of a connected graph is connected. -/
theorem edgeProbe_isConnected
    (G : BipartiteMultigraph X Y E) (hG : G.IsConnected) (e : E) :
    (G.edgeProbe e).IsConnected := by
  let anchor : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y) :=
    edgeProbeVertexMap (.inl (G.left e))
  have holdToAnchor : ∀ z : X ⊕ Y,
      (G.edgeProbe e).FactorReachable Finset.univ
        (edgeProbeVertexMap z) anchor := by
    intro z
    exact G.edgeProbe_reachable_of_old_reachable e
      (hG.2 z (.inl (G.left e)))
  have hallToAnchor : ∀ z : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y),
      (G.edgeProbe e).FactorReachable Finset.univ z anchor := by
    intro z
    rcases z with xl | yr
    · rcases xl with x | unit
      · exact holdToAnchor (.inl x)
      · cases unit
        exact (G.edgeProbe_xi_reaches_oldRight e).trans
          (holdToAnchor (.inr (G.right e)))
    · rcases yr with y | unit
      · exact holdToAnchor (.inr y)
      · cases unit
        exact G.edgeProbe_eta_reaches_oldLeft e
  refine ⟨⟨anchor⟩, ?_⟩
  intro a b
  exact (hallToAnchor a).trans (hallToAnchor b).symm

end BipartiteMultigraph
end BachThesisLean
