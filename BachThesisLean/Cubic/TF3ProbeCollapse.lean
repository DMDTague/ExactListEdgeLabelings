import BachThesisLean.Cubic.TF3ProbeMatching

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- Collapse the two new pole vertices back onto the endpoints of the replaced
edge: `xi` collapses to the old right endpoint and `eta` to the old left
endpoint. -/
def edgeProbeCollapse
    (G : BipartiteMultigraph X Y E) (e : E) :
    (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y) → X ⊕ Y
  | .inl (.inl x) => .inl x
  | .inr (.inl y) => .inr y
  | .inl (.inr _) => .inr (G.right e)
  | .inr (.inr _) => .inl (G.left e)

@[simp] theorem edgeProbeCollapse_old
    (G : BipartiteMultigraph X Y E) (e : E) (z : X ⊕ Y) :
    G.edgeProbeCollapse e (edgeProbeVertexMap z) = z := by
  cases z <;> rfl

@[simp] theorem edgeProbeCollapse_xi
    (G : BipartiteMultigraph X Y E) (e : E) :
    G.edgeProbeCollapse e (.inl (probeXi : EdgeProbeLeft X)) =
      .inr (G.right e) := rfl

@[simp] theorem edgeProbeCollapse_eta
    (G : BipartiteMultigraph X Y E) (e : E) :
    G.edgeProbeCollapse e (.inr (probeEta : EdgeProbeRight Y)) =
      .inl (G.left e) := rfl

/-- One complementary adjacency step in the probe collapses to source-factor
reachability for the complement of the restricted edge set.  Joins collapse to
reflexive steps, while a pole edge collapses to the deleted source edge `e`. -/
theorem edgeProbeCollapse_selectedAdjacent_reachable
    (G : BipartiteMultigraph X Y E) (e : E)
    (P : Finset (EdgeProbeEdge e))
    {a b : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y)}
    (h : (G.edgeProbe e).SelectedAdjacent Pᶜ a b) :
    G.FactorReachable (G.edgeProbeRestrict e P)ᶜ
      (G.edgeProbeCollapse e a) (G.edgeProbeCollapse e b) := by
  rcases h with ⟨g, hg, hab | hab⟩
  · have hgNot : g ∉ P := Finset.mem_compl.mp hg
    rcases g with f | fresh
    · have hfNot : f.1 ∉ G.edgeProbeRestrict e P := by
        intro hf
        exact hgNot ((G.mem_edgeProbeRestrict_iff_old_mem e P f.2).1 hf)
      have hfCompl : f.1 ∈ (G.edgeProbeRestrict e P)ᶜ :=
        Finset.mem_compl.mpr hfNot
      rcases hab with ⟨rfl, rfl⟩
      simpa [edgeProbeCollapse] using G.factorReachable_endpoints hfCompl
    · cases fresh with
      | xEta =>
          rcases hab with ⟨rfl, rfl⟩
          exact G.factorReachable_refl _ _
      | yXi =>
          rcases hab with ⟨rfl, rfl⟩
          exact G.factorReachable_refl _ _
      | pole0 =>
          rcases hab with ⟨rfl, rfl⟩
          have heCompl : e ∈ (G.edgeProbeRestrict e P)ᶜ :=
            Finset.mem_compl.mpr (G.edgeProbeRestrict_not_mem_deleted e P)
          simpa [edgeProbeCollapse] using
            (G.factorReachable_endpoints heCompl).symm
      | pole1 =>
          rcases hab with ⟨rfl, rfl⟩
          have heCompl : e ∈ (G.edgeProbeRestrict e P)ᶜ :=
            Finset.mem_compl.mpr (G.edgeProbeRestrict_not_mem_deleted e P)
          simpa [edgeProbeCollapse] using
            (G.factorReachable_endpoints heCompl).symm
  · have hgNot : g ∉ P := Finset.mem_compl.mp hg
    rcases g with f | fresh
    · have hfNot : f.1 ∉ G.edgeProbeRestrict e P := by
        intro hf
        exact hgNot ((G.mem_edgeProbeRestrict_iff_old_mem e P f.2).1 hf)
      have hfCompl : f.1 ∈ (G.edgeProbeRestrict e P)ᶜ :=
        Finset.mem_compl.mpr hfNot
      rcases hab with ⟨rfl, rfl⟩
      simpa [edgeProbeCollapse] using (G.factorReachable_endpoints hfCompl).symm
    · cases fresh with
      | xEta =>
          rcases hab with ⟨rfl, rfl⟩
          exact G.factorReachable_refl _ _
      | yXi =>
          rcases hab with ⟨rfl, rfl⟩
          exact G.factorReachable_refl _ _
      | pole0 =>
          rcases hab with ⟨rfl, rfl⟩
          have heCompl : e ∈ (G.edgeProbeRestrict e P)ᶜ :=
            Finset.mem_compl.mpr (G.edgeProbeRestrict_not_mem_deleted e P)
          simpa [edgeProbeCollapse] using G.factorReachable_endpoints heCompl
      | pole1 =>
          rcases hab with ⟨rfl, rfl⟩
          have heCompl : e ∈ (G.edgeProbeRestrict e P)ᶜ :=
            Finset.mem_compl.mpr (G.edgeProbeRestrict_not_mem_deleted e P)
          simpa [edgeProbeCollapse] using G.factorReachable_endpoints heCompl

/-- Every complementary factor path in the probe descends under collapse to a
complementary factor path in the source graph. -/
theorem edgeProbeCollapse_reachable
    (G : BipartiteMultigraph X Y E) (e : E)
    (P : Finset (EdgeProbeEdge e))
    {a b : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y)}
    (h : (G.edgeProbe e).FactorReachable Pᶜ a b) :
    G.FactorReachable (G.edgeProbeRestrict e P)ᶜ
      (G.edgeProbeCollapse e a) (G.edgeProbeCollapse e b) := by
  induction h with
  | refl => exact G.factorReachable_refl _ _
  | tail _ hab ih =>
      exact ih.trans (G.edgeProbeCollapse_selectedAdjacent_reachable e P hab)

end BipartiteMultigraph
end BachThesisLean
