import BachThesisLean.Cubic.SquareSmoothingFactor

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Degree bookkeeping for the lifted square factor

At every surviving vertex, selected incidence in the smoothing is carried
bijectively to selected incidence in the lifted original factor by the recovery
maps from `SquareSmoothing`.  The four deleted square vertices are handled
locally afterwards.
-/

@[simp] theorem mem_liftFactor_leftSpoke (swap i : Bool)
    (S : Finset Q.SmoothEdge) :
    Q.leftSpoke i ∈ Q.liftFactor swap S ↔
      Q.freshSelected S (squarePair swap i) := by
  simpa using
    (Q.mem_liftFactor_leftSpoke_paired swap (squarePair swap i) S)

/-- The three displayed copies are exactly the incidences at a square-left
vertex. -/
theorem incidentEdges_leftVertex_eq (i : Bool) :
    G.incidentEdges (.inl (Q.leftVertex i)) =
      {Q.square i false, Q.square i true, Q.leftSpoke i} := by
  classical
  ext e
  constructor
  · intro he
    have hleft : G.left e = Q.leftVertex i := by
      simpa [Incident] using
        (mem_incidentEdges G (.inl (Q.leftVertex i)) e).1 he
    rcases Q.left_saturated e i hleft with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h
    · subst e
      exact (mem_incidentEdges G (.inl (Q.leftVertex i)) _).2 (by
        simpa [Incident] using Q.square_left i false)
    · subst e
      exact (mem_incidentEdges G (.inl (Q.leftVertex i)) _).2 (by
        simpa [Incident] using Q.square_left i true)
    · subst e
      exact (mem_incidentEdges G (.inl (Q.leftVertex i)) _).2 (by
        simpa [Incident] using Q.leftSpoke_left i)

/-- The three displayed copies are exactly the incidences at a square-right
vertex. -/
theorem incidentEdges_rightVertex_eq (j : Bool) :
    G.incidentEdges (.inr (Q.rightVertex j)) =
      {Q.square false j, Q.square true j, Q.rightSpoke j} := by
  classical
  ext e
  constructor
  · intro he
    have hright : G.right e = Q.rightVertex j := by
      simpa [Incident] using
        (mem_incidentEdges G (.inr (Q.rightVertex j)) e).1 he
    rcases Q.right_saturated e j hright with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h
    · subst e
      exact (mem_incidentEdges G (.inr (Q.rightVertex j)) _).2 (by
        simpa [Incident] using Q.square_right false j)
    · subst e
      exact (mem_incidentEdges G (.inr (Q.rightVertex j)) _).2 (by
        simpa [Incident] using Q.square_right true j)
    · subst e
      exact (mem_incidentEdges G (.inr (Q.rightVertex j)) _).2 (by
        simpa [Incident] using Q.rightSpoke_right j)

/-- On a surviving left vertex, the recovery map identifies the selected
incidences of the smoothing with those of its lifted factor. -/
theorem recoverLeft_selectedIncident_image
    (swap : Bool) (S : Finset Q.SmoothEdge) (x : Q.ReducedLeft) :
    ((Q.smooth swap).selectedIncident S (.inl x)).image Q.recoverLeft =
      G.selectedIncident (Q.liftFactor swap S) (.inl x.val) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
    have ha' :=
      (mem_selectedIncident (Q.smooth swap) S (.inl x) a).1 ha
    have hLift : Q.recoverLeft a ∈ Q.liftFactor swap S := by
      cases a with
      | inl a =>
          exact (Q.mem_liftFactor_old swap S a).2 ha'.1
      | inr i =>
          exact (Q.mem_liftFactor_rightSpoke swap i S).2 (by
            simpa [freshSelected] using ha'.1)
    have hInc : G.Incident (Q.recoverLeft a) (.inl x.val) := by
      change G.left (Q.recoverLeft a) = x.val
      have hax : (Q.smooth swap).left a = x := by
        simpa [Incident] using ha'.2
      exact (Q.recoverLeft_left swap a).trans (congrArg Subtype.val hax)
    have hsel :=
      (mem_selectedIncident G (Q.liftFactor swap S) (.inl x.val)
        (Q.recoverLeft a)).2 ⟨hLift, hInc⟩
    simpa [hae] using hsel
  · intro he
    have he' :=
      (mem_selectedIncident G (Q.liftFactor swap S) (.inl x.val) e).1 he
    have heInc : e ∈ G.incidentEdges (.inl x.val) :=
      (mem_incidentEdges G (.inl x.val) e).2 he'.2
    rw [← Q.recoverLeft_incidence_image swap x] at heInc
    obtain ⟨a, haInc, hae⟩ := Finset.mem_image.mp heInc
    have hRecLift : Q.recoverLeft a ∈ Q.liftFactor swap S := by
      rw [hae]
      exact he'.1
    have haS : a ∈ S := by
      cases a with
      | inl a =>
          exact (Q.mem_liftFactor_old swap S a).1 hRecLift
      | inr i =>
          have hi := (Q.mem_liftFactor_rightSpoke swap i S).1 hRecLift
          simpa [freshSelected] using hi
    refine Finset.mem_image.mpr ⟨a, ?_, hae⟩
    exact (mem_selectedIncident (Q.smooth swap) S (.inl x) a).2
      ⟨haS, (mem_incidentEdges (Q.smooth swap) (.inl x) a).1 haInc⟩

/-- On a surviving right vertex, the right recovery map identifies selected
incidences in the same way. -/
theorem recoverRight_selectedIncident_image
    (swap : Bool) (S : Finset Q.SmoothEdge) (y : Q.ReducedRight) :
    ((Q.smooth swap).selectedIncident S (.inr y)).image (Q.recoverRight swap) =
      G.selectedIncident (Q.liftFactor swap S) (.inr y.val) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
    have ha' :=
      (mem_selectedIncident (Q.smooth swap) S (.inr y) a).1 ha
    have hLift : Q.recoverRight swap a ∈ Q.liftFactor swap S := by
      cases a with
      | inl a =>
          exact (Q.mem_liftFactor_old swap S a).2 ha'.1
      | inr i =>
          exact (Q.mem_liftFactor_leftSpoke_paired swap i S).2 (by
            simpa [freshSelected] using ha'.1)
    have hInc : G.Incident (Q.recoverRight swap a) (.inr y.val) := by
      change G.right (Q.recoverRight swap a) = y.val
      have hay : (Q.smooth swap).right a = y := by
        simpa [Incident] using ha'.2
      exact (Q.recoverRight_right swap a).trans (congrArg Subtype.val hay)
    have hsel :=
      (mem_selectedIncident G (Q.liftFactor swap S) (.inr y.val)
        (Q.recoverRight swap a)).2 ⟨hLift, hInc⟩
    simpa [hae] using hsel
  · intro he
    have he' :=
      (mem_selectedIncident G (Q.liftFactor swap S) (.inr y.val) e).1 he
    have heInc : e ∈ G.incidentEdges (.inr y.val) :=
      (mem_incidentEdges G (.inr y.val) e).2 he'.2
    rw [← Q.recoverRight_incidence_image swap y] at heInc
    obtain ⟨a, haInc, hae⟩ := Finset.mem_image.mp heInc
    have hRecLift : Q.recoverRight swap a ∈ Q.liftFactor swap S := by
      rw [hae]
      exact he'.1
    have haS : a ∈ S := by
      cases a with
      | inl a =>
          exact (Q.mem_liftFactor_old swap S a).1 hRecLift
      | inr i =>
          have hi :=
            (Q.mem_liftFactor_leftSpoke_paired swap i S).1 hRecLift
          simpa [freshSelected] using hi
    refine Finset.mem_image.mpr ⟨a, ?_, hae⟩
    exact (mem_selectedIncident (Q.smooth swap) S (.inr y) a).2
      ⟨haS, (mem_incidentEdges (Q.smooth swap) (.inr y) a).1 haInc⟩

/-- Selected degree is preserved at every surviving left vertex. -/
theorem liftFactor_selectedIncident_left_card
    (swap : Bool) (S : Finset Q.SmoothEdge) (x : Q.ReducedLeft) :
    (G.selectedIncident (Q.liftFactor swap S) (.inl x.val)).card =
      ((Q.smooth swap).selectedIncident S (.inl x)).card := by
  have h := congrArg Finset.card
    (Q.recoverLeft_selectedIncident_image swap S x)
  rw [Finset.card_image_of_injective _ Q.recoverLeft_injective] at h
  exact h.symm

/-- Selected degree is preserved at every surviving right vertex. -/
theorem liftFactor_selectedIncident_right_card
    (swap : Bool) (S : Finset Q.SmoothEdge) (y : Q.ReducedRight) :
    (G.selectedIncident (Q.liftFactor swap S) (.inr y.val)).card =
      ((Q.smooth swap).selectedIncident S (.inr y)).card := by
  have h := congrArg Finset.card
    (Q.recoverRight_selectedIncident_image swap S y)
  rw [Finset.card_image_of_injective _ (Q.recoverRight_injective swap)] at h
  exact h.symm

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
