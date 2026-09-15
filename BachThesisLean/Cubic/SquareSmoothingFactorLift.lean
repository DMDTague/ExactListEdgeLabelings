import BachThesisLean.Cubic.SquareSmoothingFactorDegrees

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# The lifted edge set is a spanning two-factor

The surviving vertices inherit selected degree from the smoothing by the
recovery bijections. At each deleted square vertex, the local truth table for
the two tagged smoothing copies leaves exactly two of the three incident
original copies selected.
-/

@[simp] theorem square_same_left_ne (i : Bool) :
    Q.square i false ≠ Q.square i true := by
  intro h
  have hp : (i, false) = (i, true) := Q.square_injective h
  have hj := congrArg Prod.snd hp
  cases hj

@[simp] theorem square_same_right_ne (j : Bool) :
    Q.square false j ≠ Q.square true j := by
  intro h
  have hp : (false, j) = (true, j) := Q.square_injective h
  have hi := congrArg Prod.fst hp
  cases hi

/-- The corrected four-case lift selects exactly two incident copies at every
left vertex of the deleted square. -/
theorem liftFactor_squareLeft_card_two
    (swap : Bool) (S : Finset Q.SmoothEdge) (i : Bool) :
    (G.selectedIncident (Q.liftFactor swap S) (.inl (Q.leftVertex i))).card = 2 := by
  classical
  have hsel :
      G.selectedIncident (Q.liftFactor swap S) (.inl (Q.leftVertex i)) =
        (G.incidentEdges (.inl (Q.leftVertex i))).filter
          (fun e => e ∈ Q.liftFactor swap S) := by
    ext e
    simp only [mem_selectedIncident, Finset.mem_filter, mem_incidentEdges]
    tauto
  rw [hsel, Q.incidentEdges_leftVertex_eq i]
  have hsq : Q.square i false ≠ Q.square i true := Q.square_same_left_ne i
  have hs0 : Q.square i false ≠ Q.leftSpoke i :=
    Q.square_ne_leftSpoke i false i
  have hs1 : Q.square i true ≠ Q.leftSpoke i :=
    Q.square_ne_leftSpoke i true i
  cases swap <;> cases i <;>
    by_cases h0 : (Sum.inr false : Q.SmoothEdge) ∈ S <;>
    by_cases h1 : (Sum.inr true : Q.SmoothEdge) ∈ S <;>
    simp only [Finset.filter_insert, Finset.filter_singleton] <;>
    simp [Q.mem_liftFactor_square, Q.mem_liftFactor_leftSpoke_paired,
      squareSelected, freshSelected, squarePair, h0, h1, hsq, hs0, hs1]

/-- The same local truth table gives selected degree two at every deleted
square-right vertex. -/
theorem liftFactor_squareRight_card_two
    (swap : Bool) (S : Finset Q.SmoothEdge) (j : Bool) :
    (G.selectedIncident (Q.liftFactor swap S) (.inr (Q.rightVertex j))).card = 2 := by
  classical
  have hsel :
      G.selectedIncident (Q.liftFactor swap S) (.inr (Q.rightVertex j)) =
        (G.incidentEdges (.inr (Q.rightVertex j))).filter
          (fun e => e ∈ Q.liftFactor swap S) := by
    ext e
    simp only [mem_selectedIncident, Finset.mem_filter, mem_incidentEdges]
    tauto
  rw [hsel, Q.incidentEdges_rightVertex_eq j]
  have hsq : Q.square false j ≠ Q.square true j := Q.square_same_right_ne j
  have hs0 : Q.square false j ≠ Q.rightSpoke j :=
    Q.square_ne_rightSpoke false j j
  have hs1 : Q.square true j ≠ Q.rightSpoke j :=
    Q.square_ne_rightSpoke true j j
  cases swap <;> cases j <;>
    by_cases h0 : (Sum.inr false : Q.SmoothEdge) ∈ S <;>
    by_cases h1 : (Sum.inr true : Q.SmoothEdge) ∈ S <;>
    simp only [Finset.filter_insert, Finset.filter_singleton] <;>
    simp [Q.mem_liftFactor_square, Q.mem_liftFactor_rightSpoke,
      squareSelected, freshSelected, squarePair, h0, h1, hsq, hs0, hs1]

/-- Every spanning two-factor of either smoothing lifts to a spanning
edge-copy two-factor of the original graph. -/
theorem liftFactor_isTwoFactor
    (swap : Bool) {S : Finset Q.SmoothEdge}
    (hS : (Q.smooth swap).IsTwoFactor S) :
    G.IsTwoFactor (Q.liftFactor swap S) := by
  intro v
  cases v with
  | inl x =>
      by_cases h0 : x = Q.leftVertex false
      · subst x
        exact Q.liftFactor_squareLeft_card_two swap S false
      by_cases h1 : x = Q.leftVertex true
      · subst x
        exact Q.liftFactor_squareLeft_card_two swap S true
      let xr : Q.ReducedLeft := ⟨x, by
        intro i
        cases i
        · exact h0
        · exact h1⟩
      rw [Q.liftFactor_selectedIncident_left_card swap S xr]
      exact hS (.inl xr)
  | inr y =>
      by_cases h0 : y = Q.rightVertex false
      · subst y
        exact Q.liftFactor_squareRight_card_two swap S false
      by_cases h1 : y = Q.rightVertex true
      · subst y
        exact Q.liftFactor_squareRight_card_two swap S true
      let yr : Q.ReducedRight := ⟨y, by
        intro j
        cases j
        · exact h0
        · exact h1⟩
      rw [Q.liftFactor_selectedIncident_right_card swap S yr]
      exact hS (.inr yr)

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
