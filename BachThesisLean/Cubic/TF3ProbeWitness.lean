import BachThesisLean.Cubic.TF3ProbeCollapse
import BachThesisLean.Cubic.MatchingCovered

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- In the designated probe coloring, color `1` is exactly the old target
vertex. -/
theorem edgeProbeLeftColoring_eq_one_iff
    (G : BipartiteMultigraph X Y E) (e : E) (v : X)
    (hv : v ≠ G.left e) (z : EdgeProbeLeft X) :
    (G.edgeProbeLeftColoring e v hv).color z = 1 ↔ z = .inl v := by
  rcases z with x | unit
  · simp [edgeProbeLeftColoring]
  · cases unit
    simp [edgeProbeLeftColoring]

/-- In the designated probe coloring, color `2` is exactly the new left pole
`xi`. -/
theorem edgeProbeLeftColoring_eq_two_iff
    (G : BipartiteMultigraph X Y E) (e : E) (v : X)
    (hv : v ≠ G.left e) (z : EdgeProbeLeft X) :
    (G.edgeProbeLeftColoring e v hv).color z = 2 ↔
      z = (probeXi : EdgeProbeLeft X) := by
  rcases z with x | unit
  · by_cases hx : x = v <;> simp [edgeProbeLeftColoring, probeXi, hx]
  · cases unit
    simp [edgeProbeLeftColoring, probeXi]

/-- A `TF3` witness on the edge probe yields an edge--vertex witness for every
old left vertex different from the left endpoint of the replaced edge. -/
theorem edgeProbe_hasTF3_edgeVertex_left_ne
    (G : BipartiteMultigraph X Y E) (e : E) (v : X)
    (hv : v ≠ G.left e)
    (hTF3 : (G.edgeProbe e).HasTF3) :
    ∃ P : Finset E, ∃ root : X ⊕ Y,
      G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
        G.FactorReachable Pᶜ root (.inl v) := by
  let c := G.edgeProbeLeftColoring e v hv
  obtain ⟨P, root, hP, hall⟩ := hTF3 c
  obtain ⟨v1, hv1Color, hv1Reach⟩ := hall 1
  obtain ⟨v2, hv2Color, hv2Reach⟩ := hall 2
  have hv1 : v1 = (.inl v : EdgeProbeLeft X) :=
    (G.edgeProbeLeftColoring_eq_one_iff e v hv v1).1 hv1Color
  have hv2 : v2 = (probeXi : EdgeProbeLeft X) :=
    (G.edgeProbeLeftColoring_eq_two_iff e v hv v2).1 hv2Color
  rw [hv1] at hv1Reach
  rw [hv2] at hv2Reach
  have hxiV :
      (G.edgeProbe e).FactorReachable Pᶜ
        (.inl (probeXi : EdgeProbeLeft X))
        (edgeProbeVertexMap (.inl v)) := by
    exact hv2Reach.symm.trans (by simpa using hv1Reach)
  obtain ⟨hxEta, hyXi⟩ :=
    G.edgeProbe_joins_not_mem_of_xi_reaches_old e hP (.inl v) hxiV
  let R : Finset E := G.edgeProbeRestrict e P
  have hR : G.IsPerfectMatching R := by
    simpa [R] using G.edgeProbeRestrict_isPerfectMatching e hP hxEta hyXi
  have hdesc0 := G.edgeProbeCollapse_reachable e P hxiV
  have hdesc :
      G.FactorReachable Rᶜ (.inr (G.right e)) (.inl v) := by
    simpa [R] using hdesc0
  have heCompl : e ∈ Rᶜ := by
    apply Finset.mem_compl.mpr
    simpa [R] using G.edgeProbeRestrict_not_mem_deleted e P
  have heCarry : G.ComponentCarries Rᶜ (.inr (G.right e)) e := by
    refine ⟨heCompl, ?_⟩
    exact (G.factorReachable_endpoints heCompl).symm
  exact ⟨R, .inr (G.right e), hR, heCarry, hdesc⟩

/-- In a cubic graph the endpoint of a prescribed edge already has an EVP
witness: force another incident copy into a perfect matching, thereby leaving
the prescribed edge in the complementary factor. -/
theorem edgeVertexWitness_left_endpoint_of_cubic
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (e : E) :
    ∃ P : Finset E, ∃ root : X ⊕ Y,
      G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
        G.FactorReachable Pᶜ root (.inl (G.left e)) := by
  obtain ⟨f, hfInc, hfe⟩ := hG.exists_incident_ne (.inl (G.left e)) e
  obtain ⟨P, hP, hfP⟩ := G.exists_perfectMatching_containing_edge_of_cubic hG f
  have heNot : e ∉ P := by
    intro heP
    have heInc : G.Incident e (.inl (G.left e)) := rfl
    have hEq := ((G.isMatching_iff P).1 hP.isMatching)
      f hfP e heP (.inl (G.left e)) hfInc heInc
    exact hfe hEq
  have heCompl : e ∈ Pᶜ := Finset.mem_compl.mpr heNot
  refine ⟨P, .inl (G.left e), hP, ?_, G.factorReachable_refl Pᶜ _⟩
  exact ⟨heCompl, G.factorReachable_refl Pᶜ _⟩

/-- If the edge probe has `TF3`, every old left vertex has the required
edge--vertex witness in the source cubic graph. -/
theorem edgeProbe_hasTF3_edgeVertex_left
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (e : E) (v : X)
    (hTF3 : (G.edgeProbe e).HasTF3) :
    ∃ P : Finset E, ∃ root : X ⊕ Y,
      G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
        G.FactorReachable Pᶜ root (.inl v) := by
  by_cases hv : v = G.left e
  · subst v
    exact G.edgeVertexWitness_left_endpoint_of_cubic hG e
  · exact G.edgeProbe_hasTF3_edgeVertex_left_ne e v hv hTF3

end BipartiteMultigraph
end BachThesisLean
