import BachThesisLean.Cubic.PortMasks

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Two admissible ports

This is the root-mask form of the vertex half of manuscript Lemma
`lem:two-port`.  Under EEP and cubicity, for every chosen root `r` and every
vertex `v`, at least two matching ports can be used while the complementary
factor component through `r` still reaches `v`.
-/

/-- EEP supplies, for each forbidden port `i`, some different matching port
that keeps `v` on the complementary component through `r`. -/
theorem HasEEP.exists_vertexRootMask_port_ne
    {G : BipartiteMultigraph X Y E} (hEEP : G.HasEEP) (hG : G.IsCubic)
    (r : X ⊕ Y) (ports : G.PortEnumeration r) (v : X ⊕ Y)
    (i : Fin 3) :
    ∃ j ∈ G.vertexRootMask r ports v, j ≠ i := by
  have hEVP : G.HasEVP := hEEP.hasEVP hG
  obtain ⟨P, root, hP, hpi, hv⟩ := hEVP (ports i).val v
  obtain ⟨j, hjP, _⟩ := hP.existsUnique_port r ports
  have hportInc : G.Incident (ports i).val r :=
    (mem_incidentEdges G r (ports i).val).1 (ports i).property
  have hroot : G.FactorReachable Pᶜ root r :=
    hpi.reachable_incident hportInc
  have hrv : G.FactorReachable Pᶜ r v := hroot.symm.trans hv
  have hjmask : j ∈ G.vertexRootMask r ports v :=
    (mem_vertexRootMask G r ports v j).2 ⟨P, hP, hjP, hrv⟩
  refine ⟨j, hjmask, ?_⟩
  intro hji
  subst j
  exact (Finset.mem_compl.mp hpi.1) hjP

/-- Vertex form of the manuscript's two-admissible-ports lemma. -/
theorem HasEEP.vertexRootMask_card_ge_two
    {G : BipartiteMultigraph X Y E} (hEEP : G.HasEEP) (hG : G.IsCubic)
    (r : X ⊕ Y) (ports : G.PortEnumeration r) (v : X ⊕ Y) :
    2 ≤ (G.vertexRootMask r ports v).card := by
  obtain ⟨j, hj, _⟩ := hEEP.exists_vertexRootMask_port_ne hG r ports v 0
  obtain ⟨k, hk, hkj⟩ := hEEP.exists_vertexRootMask_port_ne hG r ports v j
  have hcard : 1 < (G.vertexRootMask r ports v).card := by
    rw [Finset.one_lt_card]
    exact ⟨j, hj, k, hk, Ne.symm hkj⟩
  omega

/-- Canonical-port version supplied directly by cubicity. -/
theorem HasEEP.vertexRootMask_card_ge_two_of_cubic
    {G : BipartiteMultigraph X Y E} (hEEP : G.HasEEP) (hG : G.IsCubic)
    (r v : X ⊕ Y) :
    2 ≤ (G.vertexRootMask r (G.portsOfCubic hG r) v).card :=
  hEEP.vertexRootMask_card_ge_two hG r (G.portsOfCubic hG r) v

end BipartiteMultigraph
end BachThesisLean
