import BachThesisLean.Cubic.TF3ProbeGraph

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- On the left shore, replace the deleted original copy by the `x-eta` join. -/
def edgeProbeLeftLift
    (G : BipartiteMultigraph X Y E) (e f : E) : EdgeProbeEdge e :=
  if h : f = e then .inr .xEta else .inl ⟨f, h⟩

/-- Recover the original copy from the old copies and the `x-eta` join. -/
def edgeProbeLeftRecover
    (G : BipartiteMultigraph X Y E) (e : E) : EdgeProbeEdge e → Option E
  | .inl f => some f.1
  | .inr .xEta => some e
  | .inr .yXi => none
  | .inr .pole0 => none
  | .inr .pole1 => none

@[simp] theorem edgeProbeLeftRecover_lift
    (G : BipartiteMultigraph X Y E) (e f : E) :
    G.edgeProbeLeftRecover e (G.edgeProbeLeftLift e f) = some f := by
  classical
  by_cases h : f = e
  · subst f
    simp [edgeProbeLeftLift, edgeProbeLeftRecover]
  · simp [edgeProbeLeftLift, edgeProbeLeftRecover, h]

theorem edgeProbeLeftLift_injective
    (G : BipartiteMultigraph X Y E) (e : E) :
    Function.Injective (G.edgeProbeLeftLift e) := by
  intro f g h
  have h' := congrArg (G.edgeProbeLeftRecover e) h
  simpa using h'

@[simp] theorem edgeProbeLeftLift_left
    (G : BipartiteMultigraph X Y E) (e f : E) :
    (G.edgeProbe e).left (G.edgeProbeLeftLift e f) = .inl (G.left f) := by
  classical
  by_cases h : f = e
  · subst f
    simp [edgeProbeLeftLift]
  · simp [edgeProbeLeftLift, h]

/-- On the right shore, replace the deleted original copy by the `y-xi` join. -/
def edgeProbeRightLift
    (G : BipartiteMultigraph X Y E) (e f : E) : EdgeProbeEdge e :=
  if h : f = e then .inr .yXi else .inl ⟨f, h⟩

/-- Recover the original copy from the old copies and the `y-xi` join. -/
def edgeProbeRightRecover
    (G : BipartiteMultigraph X Y E) (e : E) : EdgeProbeEdge e → Option E
  | .inl f => some f.1
  | .inr .yXi => some e
  | .inr .xEta => none
  | .inr .pole0 => none
  | .inr .pole1 => none

@[simp] theorem edgeProbeRightRecover_lift
    (G : BipartiteMultigraph X Y E) (e f : E) :
    G.edgeProbeRightRecover e (G.edgeProbeRightLift e f) = some f := by
  classical
  by_cases h : f = e
  · subst f
    simp [edgeProbeRightLift, edgeProbeRightRecover]
  · simp [edgeProbeRightLift, edgeProbeRightRecover, h]

theorem edgeProbeRightLift_injective
    (G : BipartiteMultigraph X Y E) (e : E) :
    Function.Injective (G.edgeProbeRightLift e) := by
  intro f g h
  have h' := congrArg (G.edgeProbeRightRecover e) h
  simpa using h'

@[simp] theorem edgeProbeRightLift_right
    (G : BipartiteMultigraph X Y E) (e f : E) :
    (G.edgeProbe e).right (G.edgeProbeRightLift e f) = .inl (G.right f) := by
  classical
  by_cases h : f = e
  · subst f
    simp [edgeProbeRightLift]
  · simp [edgeProbeRightLift, h]

/-- Degrees at old left vertices are unchanged by the probe replacement. -/
theorem edgeProbe_leftIncident_old_card
    (G : BipartiteMultigraph X Y E) (e : E) (x : X) :
    ((G.edgeProbe e).leftIncident (.inl x)).card =
      (G.leftIncident x).card := by
  classical
  symm
  refine Finset.card_nbij (G.edgeProbeLeftLift e) ?_ ?_ ?_
  · intro f hf
    apply ((G.edgeProbe e).mem_leftIncident (.inl x)
      (G.edgeProbeLeftLift e f)).2
    rw [G.edgeProbeLeftLift_left e f]
    exact congrArg Sum.inl ((G.mem_leftIncident x f).1 hf)
  · intro f hf g hg hfg
    exact G.edgeProbeLeftLift_injective e hfg
  · intro s hs
    have hsleft := ((G.edgeProbe e).mem_leftIncident (.inl x) s).1 hs
    rcases s with f | fresh
    · have hleft : G.left f.1 = x := by simpa using hsleft
      refine ⟨f.1, (G.mem_leftIncident x f.1).2 hleft, ?_⟩
      simp [edgeProbeLeftLift, f.2]
    · cases fresh with
      | xEta =>
          have hleft : G.left e = x := by simpa using hsleft
          refine ⟨e, (G.mem_leftIncident x e).2 hleft, ?_⟩
          simp [edgeProbeLeftLift]
      | yXi => simp at hsleft
      | pole0 => simp at hsleft
      | pole1 => simp at hsleft

/-- Degrees at old right vertices are unchanged by the probe replacement. -/
theorem edgeProbe_rightIncident_old_card
    (G : BipartiteMultigraph X Y E) (e : E) (y : Y) :
    ((G.edgeProbe e).rightIncident (.inl y)).card =
      (G.rightIncident y).card := by
  classical
  symm
  refine Finset.card_nbij (G.edgeProbeRightLift e) ?_ ?_ ?_
  · intro f hf
    apply ((G.edgeProbe e).mem_rightIncident (.inl y)
      (G.edgeProbeRightLift e f)).2
    rw [G.edgeProbeRightLift_right e f]
    exact congrArg Sum.inl ((G.mem_rightIncident y f).1 hf)
  · intro f hf g hg hfg
    exact G.edgeProbeRightLift_injective e hfg
  · intro s hs
    have hsright := ((G.edgeProbe e).mem_rightIncident (.inl y) s).1 hs
    rcases s with f | fresh
    · have hright : G.right f.1 = y := by simpa using hsright
      refine ⟨f.1, (G.mem_rightIncident y f.1).2 hright, ?_⟩
      simp [edgeProbeRightLift, f.2]
    · cases fresh with
      | yXi =>
          have hright : G.right e = y := by simpa using hsright
          refine ⟨e, (G.mem_rightIncident y e).2 hright, ?_⟩
          simp [edgeProbeRightLift]
      | xEta => simp at hsright
      | pole0 => simp at hsright
      | pole1 => simp at hsright

/-- The new left pole has the join `y-xi` and the two parallel pole copies. -/
theorem edgeProbe_leftIncident_xi_card
    (G : BipartiteMultigraph X Y E) (e : E) :
    ((G.edgeProbe e).leftIncident (probeXi : EdgeProbeLeft X)).card = 3 := by
  classical
  have hset :
      (G.edgeProbe e).leftIncident (probeXi : EdgeProbeLeft X) =
        {(.inr .yXi : EdgeProbeEdge e), .inr .pole0, .inr .pole1} := by
    ext s
    rw [(G.edgeProbe e).mem_leftIncident]
    rcases s with f | fresh
    · simp [probeXi]
    · cases fresh <;> simp [probeXi]
  rw [hset]
  simp

/-- The new right pole has the join `x-eta` and the two parallel pole copies. -/
theorem edgeProbe_rightIncident_eta_card
    (G : BipartiteMultigraph X Y E) (e : E) :
    ((G.edgeProbe e).rightIncident (probeEta : EdgeProbeRight Y)).card = 3 := by
  classical
  have hset :
      (G.edgeProbe e).rightIncident (probeEta : EdgeProbeRight Y) =
        {(.inr .xEta : EdgeProbeEdge e), .inr .pole0, .inr .pole1} := by
    ext s
    rw [(G.edgeProbe e).mem_rightIncident]
    rcases s with f | fresh
    · simp [probeEta]
    · cases fresh <;> simp [probeEta]
  rw [hset]
  simp

/-- Replacing one edge by the two-vertex probe preserves cubicity. -/
theorem edgeProbe_isCubic
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (e : E) :
    (G.edgeProbe e).IsCubic := by
  intro z
  rcases z with xl | yr
  · rw [(G.edgeProbe e).incidentEdges_inl]
    rcases xl with x | unit
    · rw [G.edgeProbe_leftIncident_old_card e x]
      simpa using hG (.inl x)
    · cases unit
      exact G.edgeProbe_leftIncident_xi_card e
  · rw [(G.edgeProbe e).incidentEdges_inr]
    rcases yr with y | unit
    · rw [G.edgeProbe_rightIncident_old_card e y]
      simpa using hG (.inr y)
    · cases unit
      exact G.edgeProbe_rightIncident_eta_card e

end BipartiteMultigraph
end BachThesisLean
