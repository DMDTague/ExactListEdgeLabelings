import BachThesisLean.Cubic.MinimalEEPCounterexample

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Size lower bounds for minimal EEP counterexamples

The finite one- and two-vertex-per-shore cases are already excluded by the
minimal-counterexample reduction.  Cubic regularity makes the two shores
equinumerous, so the same lower bound holds on the right shore.  The standard
edge-copy degree count then gives at least nine actual edge copies.
-/

namespace IsMinimalEEPCounterexample

/-- A minimal EEP counterexample has at least three vertices on its right
shore as well as on its left shore. -/
theorem three_le_card_right (hmin : G.IsMinimalEEPCounterexample) :
    3 ≤ Fintype.card Y := by
  rw [← G.card_left_eq_card_right_of_cubic hmin.cubic]
  exact hmin.three_le_card_left

/-- A minimal EEP counterexample has at least six vertices in total. -/
theorem six_le_vertexCard (hmin : G.IsMinimalEEPCounterexample) :
    6 ≤ G.vertexCard := by
  rw [vertexCard, ← G.card_left_eq_card_right_of_cubic hmin.cubic]
  have hleft := hmin.three_le_card_left
  omega

/-- A minimal EEP counterexample has at least nine actual edge copies. -/
theorem nine_le_edgeCard (hmin : G.IsMinimalEEPCounterexample) :
    9 ≤ Fintype.card E := by
  rw [G.edgeCard_eq_three_mul_leftCard_of_cubic hmin.cubic]
  have hleft := hmin.three_le_card_left
  omega

/-- The two shores of a minimal EEP counterexample have equal cardinality,
with the common value at least three. -/
theorem shore_cardinality_structure (hmin : G.IsMinimalEEPCounterexample) :
    3 ≤ Fintype.card X ∧
      3 ≤ Fintype.card Y ∧
      Fintype.card X = Fintype.card Y := by
  exact ⟨hmin.three_le_card_left, hmin.three_le_card_right,
    G.card_left_eq_card_right_of_cubic hmin.cubic⟩

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
