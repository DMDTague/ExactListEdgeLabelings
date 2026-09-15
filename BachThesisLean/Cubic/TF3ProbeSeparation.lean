import BachThesisLean.Cubic.TF3ProbeConnectivity

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- A selected edge excludes any distinct selected edge incident with the same
vertex. -/
theorem IsPerfectMatching.not_mem_of_mem_incident_ne
    {G : BipartiteMultigraph X Y E} {P : Finset E}
    (hP : G.IsPerfectMatching P) {a b : E} {z : X ⊕ Y}
    (ha : a ∈ P) (haInc : G.Incident a z)
    (hbInc : G.Incident b z) (hba : b ≠ a) : b ∉ P := by
  intro hb
  exact hba
    (((G.isMatching_iff P).1 hP.isMatching) b hb a ha z hbInc haInc)

/-- If the `y-xi` join is selected, the `x-eta` join is selected as well. -/
theorem edgeProbe_xEta_mem_of_yXi_mem
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hP : (G.edgeProbe e).IsPerfectMatching P)
    (hyXi : (.inr .yXi : EdgeProbeEdge e) ∈ P) :
    (.inr .xEta : EdgeProbeEdge e) ∈ P := by
  have hyXiInc :
      (G.edgeProbe e).Incident (.inr .yXi)
        (.inl (probeXi : EdgeProbeLeft X)) := by rfl
  have hp0Inc :
      (G.edgeProbe e).Incident (.inr .pole0)
        (.inl (probeXi : EdgeProbeLeft X)) := by rfl
  have hp1Inc :
      (G.edgeProbe e).Incident (.inr .pole1)
        (.inl (probeXi : EdgeProbeLeft X)) := by rfl
  have hp0 : (.inr .pole0 : EdgeProbeEdge e) ∉ P :=
    hP.not_mem_of_mem_incident_ne hyXi hyXiInc hp0Inc (by simp)
  have hp1 : (.inr .pole1 : EdgeProbeEdge e) ∉ P :=
    hP.not_mem_of_mem_incident_ne hyXi hyXiInc hp1Inc (by simp)
  obtain ⟨g, hg, _⟩ :=
    hP.existsUnique_incident (.inr (probeEta : EdgeProbeRight Y))
  rcases g with f | fresh
  · have hbad :
        (Sum.inl (G.right f.1) : EdgeProbeRight Y) = probeEta := by
      simpa [Incident, edgeProbe_right_old] using hg.2
    cases hbad
  · cases fresh with
    | xEta => exact hg.1
    | yXi =>
        have hbad :
            (Sum.inl (G.right e) : EdgeProbeRight Y) = probeEta := by
          simpa [Incident, edgeProbe_right_yXi] using hg.2
        cases hbad
    | pole0 => exact False.elim (hp0 hg.1)
    | pole1 => exact False.elim (hp1 hg.1)

/-- If the `x-eta` join is selected, the `y-xi` join is selected as well. -/
theorem edgeProbe_yXi_mem_of_xEta_mem
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hP : (G.edgeProbe e).IsPerfectMatching P)
    (hxEta : (.inr .xEta : EdgeProbeEdge e) ∈ P) :
    (.inr .yXi : EdgeProbeEdge e) ∈ P := by
  have hxEtaInc :
      (G.edgeProbe e).Incident (.inr .xEta)
        (.inr (probeEta : EdgeProbeRight Y)) := by rfl
  have hp0Inc :
      (G.edgeProbe e).Incident (.inr .pole0)
        (.inr (probeEta : EdgeProbeRight Y)) := by rfl
  have hp1Inc :
      (G.edgeProbe e).Incident (.inr .pole1)
        (.inr (probeEta : EdgeProbeRight Y)) := by rfl
  have hp0 : (.inr .pole0 : EdgeProbeEdge e) ∉ P :=
    hP.not_mem_of_mem_incident_ne hxEta hxEtaInc hp0Inc (by simp)
  have hp1 : (.inr .pole1 : EdgeProbeEdge e) ∉ P :=
    hP.not_mem_of_mem_incident_ne hxEta hxEtaInc hp1Inc (by simp)
  obtain ⟨g, hg, _⟩ :=
    hP.existsUnique_incident (.inl (probeXi : EdgeProbeLeft X))
  rcases g with f | fresh
  · have hbad :
        (Sum.inl (G.left f.1) : EdgeProbeLeft X) = probeXi := by
      simpa [Incident, edgeProbe_left_old] using hg.2
    cases hbad
  · cases fresh with
    | xEta =>
        have hbad :
            (Sum.inl (G.left e) : EdgeProbeLeft X) = probeXi := by
          simpa [Incident, edgeProbe_left_xEta] using hg.2
        cases hbad
    | yXi => exact hg.1
    | pole0 => exact False.elim (hp0 hg.1)
    | pole1 => exact False.elim (hp1 hg.1)

/-- In a perfect matching of the probe the two join copies are selected
together. -/
theorem edgeProbe_join_mem_iff
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hP : (G.edgeProbe e).IsPerfectMatching P) :
    (.inr .xEta : EdgeProbeEdge e) ∈ P ↔
      (.inr .yXi : EdgeProbeEdge e) ∈ P :=
  ⟨G.edgeProbe_yXi_mem_of_xEta_mem e hP,
    G.edgeProbe_xEta_mem_of_yXi_mem e hP⟩

/-- Boolean tag separating the two new pole vertices from all old vertices. -/
def edgeProbePoleStatus :
    (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y) → Bool
  | .inl (.inl _) => false
  | .inr (.inl _) => false
  | .inl (.inr _) => true
  | .inr (.inr _) => true

@[simp] theorem edgeProbePoleStatus_old (z : X ⊕ Y) :
    edgeProbePoleStatus (edgeProbeVertexMap z) = false := by
  cases z <;> rfl

@[simp] theorem edgeProbePoleStatus_xi :
    edgeProbePoleStatus
      ((.inl (probeXi : EdgeProbeLeft X)) :
        EdgeProbeLeft X ⊕ EdgeProbeRight Y) = true := rfl

@[simp] theorem edgeProbePoleStatus_eta :
    edgeProbePoleStatus
      ((.inr (probeEta : EdgeProbeRight Y)) :
        EdgeProbeLeft X ⊕ EdgeProbeRight Y) = true := rfl

/-- Once both joins belong to the perfect matching, every complementary edge
stays entirely among old vertices or entirely inside the two-vertex pole. -/
theorem edgeProbePoleStatus_eq_of_compl_selectedAdjacent
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hxEta : (.inr .xEta : EdgeProbeEdge e) ∈ P)
    (hyXi : (.inr .yXi : EdgeProbeEdge e) ∈ P)
    {a b : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y)}
    (h : (G.edgeProbe e).SelectedAdjacent Pᶜ a b) :
    edgeProbePoleStatus a = edgeProbePoleStatus b := by
  rcases h with ⟨g, hg, hab | hab⟩
  · have hgNot : g ∉ P := Finset.mem_compl.mp hg
    rcases g with f | fresh
    · rcases hab with ⟨rfl, rfl⟩
      rfl
    · cases fresh with
      | xEta => exact False.elim (hgNot hxEta)
      | yXi => exact False.elim (hgNot hyXi)
      | pole0 =>
          rcases hab with ⟨rfl, rfl⟩
          rfl
      | pole1 =>
          rcases hab with ⟨rfl, rfl⟩
          rfl
  · have hgNot : g ∉ P := Finset.mem_compl.mp hg
    rcases g with f | fresh
    · rcases hab with ⟨rfl, rfl⟩
      rfl
    · cases fresh with
      | xEta => exact False.elim (hgNot hxEta)
      | yXi => exact False.elim (hgNot hyXi)
      | pole0 =>
          rcases hab with ⟨rfl, rfl⟩
          rfl
      | pole1 =>
          rcases hab with ⟨rfl, rfl⟩
          rfl

/-- A complementary component joining the new left pole to any old vertex
forces both probe joins to be absent from the perfect matching. -/
theorem edgeProbe_joins_not_mem_of_xi_reaches_old
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hP : (G.edgeProbe e).IsPerfectMatching P) (z : X ⊕ Y)
    (hreach : (G.edgeProbe e).FactorReachable Pᶜ
      (.inl (probeXi : EdgeProbeLeft X)) (edgeProbeVertexMap z)) :
    (.inr .xEta : EdgeProbeEdge e) ∉ P ∧
      (.inr .yXi : EdgeProbeEdge e) ∉ P := by
  have hcontra : ¬ ((.inr .xEta : EdgeProbeEdge e) ∈ P) := by
    intro hxEta
    have hyXi := (G.edgeProbe_join_mem_iff e hP).1 hxEta
    have hstatus := hreach.map_eq
      (fun q : (EdgeProbeLeft X) ⊕ (EdgeProbeRight Y) => edgeProbePoleStatus q)
      (fun _ _ hab => G.edgeProbePoleStatus_eq_of_compl_selectedAdjacent
        e hxEta hyXi hab)
    simpa using hstatus
  refine ⟨hcontra, ?_⟩
  intro hyXi
  exact hcontra ((G.edgeProbe_join_mem_iff e hP).2 hyXi)

end BipartiteMultigraph
end BachThesisLean
