import BachThesisLean.Uncrossing.FibreStructure

namespace BachThesisLean

open BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq E]

/-!
# Transition-side alternation

The local degree-two structure rules out a line-graph step that shares both
shores whenever the walk continues through a third distinct edge copy. This
turns the unordered adjacency disjunction into a deterministic alternation of
right-sharing and left-sharing transitions along a simple path.
-/

/-- If `e,f,g` are distinct consecutive edge copies, the first transition
cannot simultaneously share both endpoints. -/
theorem fibreLineGraph_adj_not_both_of_next
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f g : E}
    (hef : (fibreLineGraph G).Adj e f)
    (hfg : (fibreLineGraph G).Adj f g)
    (heg : e ≠ g) :
    ¬ (G.left e = G.left f ∧ G.right e = G.right f) := by
  intro hboth
  rcases hfg.2 with hfgL | hfgR
  · exact no_three_distinct_same_left G hleft hef.1 hfg.1 heg hboth.1 hfgL
  · exact no_three_distinct_same_right G hright hef.1 hfg.1 heg hboth.2 hfgR

/-- If one transition uses the right shore, the next transition of a simple
degree-two path uses the left shore. -/
theorem fibreLineGraph_next_left_of_current_right
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f g : E}
    (hef : (fibreLineGraph G).Adj e f)
    (hfg : (fibreLineGraph G).Adj f g)
    (heg : e ≠ g)
    (hR : G.right e = G.right f) :
    G.left f = G.left g := by
  rcases fibreLineGraph_adj_sides_alternate G hleft hright hef hfg heg with hLR | hRL
  · exact (fibreLineGraph_adj_not_both_of_next G hleft hright hef hfg heg
      ⟨hLR.1, hR⟩).elim
  · exact hRL.2

/-- If one transition uses the left shore, the next transition of a simple
degree-two path uses the right shore. -/
theorem fibreLineGraph_next_right_of_current_left
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f g : E}
    (hef : (fibreLineGraph G).Adj e f)
    (hfg : (fibreLineGraph G).Adj f g)
    (heg : e ≠ g)
    (hL : G.left e = G.left f) :
    G.right f = G.right g := by
  rcases fibreLineGraph_adj_sides_alternate G hleft hright hef hfg heg with hLR | hRL
  · exact hLR.2
  · exact (fibreLineGraph_adj_not_both_of_next G hleft hright hef hfg heg
      ⟨hL, hRL.1⟩).elim

end BachThesisLean
