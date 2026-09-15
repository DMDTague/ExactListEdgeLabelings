import BachThesisLean.Cubic.Foundations

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Edge-root port masks

This file formalizes the local port-mask mechanism from manuscript v13.23.
The root ports are actual incident edge copies.  A mask records which unique
matching port can be used while a prescribed edge remains on the complementary
factor component through the root.
-/

/-- Two edge copies admit a common complementary-factor component witness. -/
def EdgePairWitness (G : BipartiteMultigraph X Y E) (e f : E) : Prop :=
  ∃ P : Finset E, ∃ root : X ⊕ Y,
    G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
      G.ComponentCarries Pᶜ root f

/-- A pointwise edge--vertex witness, separated from the global `HasEVP`
quantification. -/
def EdgeVertexWitness (G : BipartiteMultigraph X Y E)
    (e : E) (v : X ⊕ Y) : Prop :=
  ∃ P : Finset E, ∃ root : X ⊕ Y,
    G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
      G.FactorReachable Pᶜ root v

omit [Fintype X] [Fintype Y] in
/-- A selected edge incident with the chosen root is carried by the root's
component. -/
theorem componentCarries_of_mem_of_incident
    (G : BipartiteMultigraph X Y E) {S : Finset E}
    {root : X ⊕ Y} {e : E} (he : e ∈ S) (hr : G.Incident e root) :
    G.ComponentCarries S root e := by
  refine ⟨he, ?_⟩
  cases root with
  | inl x =>
      change G.left e = x at hr
      subst x
      exact G.factorReachable_refl S (.inl (G.left e))
  | inr y =>
      change G.right e = y at hr
      subst y
      exact (G.factorReachable_endpoints he).symm

omit [Fintype X] [Fintype Y] in
/-- `HasEEP` is precisely universal existence of `EdgePairWitness` for
distinct edges. -/
theorem HasEEP.edgePairWitness {G : BipartiteMultigraph X Y E}
    (h : G.HasEEP) {e f : E} (hef : e ≠ f) : G.EdgePairWitness e f :=
  h e f hef

/-- Manuscript Lemma `lem:mask-eep`, local form.  A prescribed edge `e` and
port `p_i` lie on one complementary factor component exactly when the mask of
`e` at the root contains some matching port different from `i`.

The statement itself does not need the nonincidence hypothesis on `e`; that
hypothesis enters the global EEP characterization below. -/
theorem edgePairWitness_port_iff_exists_mask_ne
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) (i : Fin 3) :
    G.EdgePairWitness e (ports i).val ↔
      ∃ j ∈ G.edgeRootMask r ports e, j ≠ i := by
  constructor
  · rintro ⟨P, root, hP, he, hpi⟩
    obtain ⟨j, hjP, _⟩ := hP.existsUnique_port r ports
    have hportInc : G.Incident (ports i).val r :=
      (mem_incidentEdges G r (ports i).val).1 (ports i).property
    have hroot : G.FactorReachable Pᶜ root r :=
      hpi.reachable_incident hportInc
    have heRoot : G.ComponentCarries Pᶜ r e :=
      ⟨he.1, hroot.symm.trans he.2⟩
    refine ⟨j, (mem_edgeRootMask G r ports e j).2 ⟨P, hP, hjP, heRoot⟩, ?_⟩
    intro hji
    subst j
    exact (Finset.mem_compl.mp hpi.1) hjP
  · rintro ⟨j, hjmask, hji⟩
    obtain ⟨P, hP, hjP, heRoot⟩ :=
      (mem_edgeRootMask G r ports e j).1 hjmask
    have hiNotP : (ports i).val ∉ P := by
      intro hiP
      obtain ⟨k, hkP, hkUnique⟩ := hP.existsUnique_port r ports
      have hik : i = k := hkUnique i hiP
      have hjk : j = k := hkUnique j hjP
      exact hji (hjk.trans hik.symm)
    have hiCompl : (ports i).val ∈ Pᶜ := Finset.mem_compl.mpr hiNotP
    have hportInc : G.Incident (ports i).val r :=
      (mem_incidentEdges G r (ports i).val).1 (ports i).property
    exact ⟨P, r, hP, heRoot,
      G.componentCarries_of_mem_of_incident hiCompl hportInc⟩

/-- Finset-difference form of the local port-mask characterization appearing
verbatim in the manuscript. -/
theorem edgePairWitness_port_iff_mask_sdiff_nonempty
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) (i : Fin 3) :
    G.EdgePairWitness e (ports i).val ↔
      (G.edgeRootMask r ports e \ {i}).Nonempty := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ :=
      (G.edgePairWitness_port_iff_exists_mask_ne r ports e i).1 h
    exact ⟨j, by simp [hj, hji]⟩
  · rintro ⟨j, hj⟩
    have hj' : j ∈ G.edgeRootMask r ports e ∧ j ≠ i := by
      simpa using hj
    exact (G.edgePairWitness_port_iff_exists_mask_ne r ports e i).2
      ⟨j, hj'.1, hj'.2⟩

/-- A mask is nonempty exactly when the corresponding pointwise edge--vertex
problem has a witness. -/
theorem edgeRootMask_nonempty_iff_edgeVertexWitness
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) :
    (G.edgeRootMask r ports e).Nonempty ↔ G.EdgeVertexWitness e r := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨P, hP, hjP, heRoot⟩ :=
      (mem_edgeRootMask G r ports e j).1 hj
    exact ⟨P, r, hP, heRoot, G.factorReachable_refl Pᶜ r⟩
  · rintro ⟨P, root, hP, he, hr⟩
    obtain ⟨j, hjP, _⟩ := hP.existsUnique_port r ports
    have heRoot : G.ComponentCarries Pᶜ r e :=
      ⟨he.1, hr.symm.trans he.2⟩
    exact ⟨j, (mem_edgeRootMask G r ports e j).2
      ⟨P, hP, hjP, heRoot⟩⟩

/-- The manuscript's zero-mask consequence: a zero mask is exactly failure of
the pointwise edge--vertex property at `(e,r)`. -/
theorem edgeRootMask_card_eq_zero_iff_not_edgeVertexWitness
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) :
    (G.edgeRootMask r ports e).card = 0 ↔ ¬ G.EdgeVertexWitness e r := by
  rw [Finset.card_eq_zero]
  constructor
  · intro hempty hEV
    have hne : (G.edgeRootMask r ports e).Nonempty :=
      (G.edgeRootMask_nonempty_iff_edgeVertexWitness r ports e).2 hEV
    simpa [hempty] using hne
  · intro hEV
    by_contra hne
    have hnonempty : (G.edgeRootMask r ports e).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hne
    exact hEV ((G.edgeRootMask_nonempty_iff_edgeVertexWitness r ports e).1 hnonempty)

/-- EEP forces at least two admissible matching ports for every nonincident
edge--root pair.  This is the reverse implication in the manuscript's boxed
port-mask characterization. -/
theorem HasEEP.edgeRootMask_card_ge_two
    {G : BipartiteMultigraph X Y E} (hEEP : G.HasEEP)
    (r : X ⊕ Y) (ports : G.PortEnumeration r) (e : E)
    (hne : ¬ G.Incident e r) :
    2 ≤ (G.edgeRootMask r ports e).card := by
  have havoid : ∀ i : Fin 3, ∃ j ∈ G.edgeRootMask r ports e, j ≠ i := by
    intro i
    have hei : e ≠ (ports i).val := by
      intro h
      apply hne
      rw [h]
      exact (mem_incidentEdges G r (ports i).val).1 (ports i).property
    exact (G.edgePairWitness_port_iff_exists_mask_ne r ports e i).1
      (hEEP.edgePairWitness hei)
  obtain ⟨j, hj, _⟩ := havoid 0
  obtain ⟨k, hk, hkj⟩ := havoid j
  have hcard : 1 < (G.edgeRootMask r ports e).card := by
    rw [Finset.one_lt_card]
    exact ⟨j, hj, k, hk, Ne.symm hkj⟩
  omega

/-- Cubicity supplies the port enumeration used by the preceding theorem. -/
theorem HasEEP.edgeRootMask_card_ge_two_of_cubic
    {G : BipartiteMultigraph X Y E} (hEEP : G.HasEEP) (hG : G.IsCubic)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r) :
    2 ≤ (G.edgeRootMask r (G.portsOfCubic hG r) e).card :=
  hEEP.edgeRootMask_card_ge_two r (G.portsOfCubic hG r) e hne

end BipartiteMultigraph
end BachThesisLean
