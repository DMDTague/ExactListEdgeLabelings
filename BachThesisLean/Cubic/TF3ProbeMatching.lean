import BachThesisLean.Cubic.TF3ProbeSeparation

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- An old probe edge is incident with an embedded old vertex exactly when its
source copy is incident with that source vertex. -/
theorem edgeProbe_old_incident_iff
    (G : BipartiteMultigraph X Y E) (e : E) (f : {f : E // f ≠ e})
    (z : X ⊕ Y) :
    (G.edgeProbe e).Incident (.inl f) (edgeProbeVertexMap z) ↔
      G.Incident f.1 z := by
  cases z <;> simp [Incident, edgeProbeVertexMap]

/-- Restrict a probe edge set to its old edge copies.  The deleted copy `e`
can never occur in this restriction. -/
noncomputable def edgeProbeRestrict
    (G : BipartiteMultigraph X Y E) (e : E)
    (P : Finset (EdgeProbeEdge e)) : Finset E := by
  classical
  exact Finset.univ.filter fun f =>
    ∃ h : f ≠ e, (.inl ⟨f, h⟩ : EdgeProbeEdge e) ∈ P

@[simp] theorem mem_edgeProbeRestrict
    (G : BipartiteMultigraph X Y E) (e : E)
    (P : Finset (EdgeProbeEdge e)) (f : E) :
    f ∈ G.edgeProbeRestrict e P ↔
      ∃ h : f ≠ e, (.inl ⟨f, h⟩ : EdgeProbeEdge e) ∈ P := by
  classical
  simp [edgeProbeRestrict]

/-- Membership can be tested using any chosen proof that the old copy differs
from the deleted one; proof irrelevance makes the choice immaterial. -/
theorem mem_edgeProbeRestrict_iff_old_mem
    (G : BipartiteMultigraph X Y E) (e : E)
    (P : Finset (EdgeProbeEdge e)) {f : E} (hfe : f ≠ e) :
    f ∈ G.edgeProbeRestrict e P ↔
      (.inl ⟨f, hfe⟩ : EdgeProbeEdge e) ∈ P := by
  constructor
  · intro hf
    obtain ⟨h, hm⟩ := (G.mem_edgeProbeRestrict e P f).1 hf
    simpa using hm
  · intro hm
    exact (G.mem_edgeProbeRestrict e P f).2 ⟨hfe, hm⟩

/-- The replaced edge itself is absent from every restricted probe edge set. -/
@[simp] theorem edgeProbeRestrict_not_mem_deleted
    (G : BipartiteMultigraph X Y E) (e : E)
    (P : Finset (EdgeProbeEdge e)) :
    e ∉ G.edgeProbeRestrict e P := by
  intro he
  obtain ⟨hne, _⟩ := (G.mem_edgeProbeRestrict e P e).1 he
  exact hne rfl

/-- If neither join is selected, every embedded old vertex has a unique
selected old edge copy, and that copy is exactly an incident selected copy in
the restricted source edge set. -/
theorem edgeProbeRestrict_existsUnique_incident
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hP : (G.edgeProbe e).IsPerfectMatching P)
    (hxEta : (.inr .xEta : EdgeProbeEdge e) ∉ P)
    (hyXi : (.inr .yXi : EdgeProbeEdge e) ∉ P)
    (z : X ⊕ Y) :
    ∃! f : E, f ∈ G.edgeProbeRestrict e P ∧ G.Incident f z := by
  obtain ⟨g, hg, huniq⟩ := hP.existsUnique_incident (edgeProbeVertexMap z)
  have gold : ∃ f : {f : E // f ≠ e}, g = .inl f := by
    rcases g with f | fresh
    · exact ⟨f, rfl⟩
    · cases fresh with
      | xEta => exact False.elim (hxEta hg.1)
      | yXi => exact False.elim (hyXi hg.1)
      | pole0 =>
          cases z <;> simp [Incident, edgeProbeVertexMap] at hg
      | pole1 =>
          cases z <;> simp [Incident, edgeProbeVertexMap] at hg
  obtain ⟨f, rfl⟩ := gold
  have hfMem : f.1 ∈ G.edgeProbeRestrict e P :=
    (G.mem_edgeProbeRestrict_iff_old_mem e P f.2).2 hg.1
  have hfInc : G.Incident f.1 z :=
    (G.edgeProbe_old_incident_iff e f z).1 hg.2
  refine ⟨f.1, ⟨hfMem, hfInc⟩, ?_⟩
  intro q hq
  have hqe : q ≠ e := by
    intro h
    subst q
    exact G.edgeProbeRestrict_not_mem_deleted e P hq.1
  have hqMem : (.inl ⟨q, hqe⟩ : EdgeProbeEdge e) ∈ P :=
    (G.mem_edgeProbeRestrict_iff_old_mem e P hqe).1 hq.1
  have hqInc :
      (G.edgeProbe e).Incident (.inl ⟨q, hqe⟩)
        (edgeProbeVertexMap z) :=
    (G.edgeProbe_old_incident_iff e ⟨q, hqe⟩ z).2 hq.2
  have heq : (.inl ⟨q, hqe⟩ : EdgeProbeEdge e) = .inl f :=
    huniq _ ⟨hqMem, hqInc⟩
  exact congrArg Subtype.val (Sum.inl.inj heq)

/-- With both joins absent, restricting a probe perfect matching gives a
perfect matching of the original graph. -/
theorem edgeProbeRestrict_isPerfectMatching
    (G : BipartiteMultigraph X Y E) (e : E) {P : Finset (EdgeProbeEdge e)}
    (hP : (G.edgeProbe e).IsPerfectMatching P)
    (hxEta : (.inr .xEta : EdgeProbeEdge e) ∉ P)
    (hyXi : (.inr .yXi : EdgeProbeEdge e) ∉ P) :
    G.IsPerfectMatching (G.edgeProbeRestrict e P) := by
  intro z
  obtain ⟨f, hf, huniq⟩ :=
    G.edgeProbeRestrict_existsUnique_incident e hP hxEta hyXi z
  have hset :
      G.selectedIncident (G.edgeProbeRestrict e P) z = {f} := by
    ext q
    rw [G.mem_selectedIncident]
    simp only [Finset.mem_singleton]
    constructor
    · intro hq
      exact huniq q hq
    · intro hq
      subst q
      exact hf
  rw [hset]
  simp

end BipartiteMultigraph
end BachThesisLean
