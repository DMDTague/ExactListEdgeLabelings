import BachThesisLean.Uncrossing.FibreQR
import BachThesisLean.Uncrossing.FibreStructure
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Topological local structure of the q/r residual components

`FibreQR` already proves the exact degree-profile split used in the surplus
exponent.  This file records the local graph-theoretic consequences needed to
turn those profiles into literal cycle/path witnesses without losing parallel
edge copies.

The key distinction is the genuine two-parallel-edge cycle.  Its two edge
copies are distinct vertices of `fibreLineGraph`, but that line graph component
is `K₂`, so each of its vertices has line-graph degree one.  Thus a proof which
simply calls every q-component a simple line-graph cycle would be wrong.  The
lemmas below isolate exactly that obstruction.
-/

/-- The explicit edge-copy neighbor finset agrees with Mathlib's neighbor
finset for the fibre line graph. -/
theorem fibreNeighbors_eq_neighborFinset
    (G : BipartiteMultigraph X Y E) (e : E) :
    fibreNeighbors G e = (fibreLineGraph G).neighborFinset e := by
  classical
  ext f
  simp

/-- A represented right degree-one endpoint of a free component is an actual
leaf of the edge-copy line graph: it has exactly one neighboring edge copy.
The unique neighbor comes from its degree-two left endpoint. -/
theorem freeComponent_rightEndpoint_fibreNeighbors_card_eq_one
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2))
    (c : FreeTwoLabelComponent L) (e : E)
    (he : (fibreLineGraph G).connectedComponentMk e = c.val)
    (hright : G.rightDegree (G.right e) = 1) :
    (fibreNeighbors G e).card = 1 := by
  classical
  have hleft : G.leftDegree (G.left e) = 2 :=
    freeComponent_leftDegree_eq_two G L c e he
  have heL : e ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) e).2 rfl
  have heR : e ∈ G.rightIncident (G.right e) :=
    (G.mem_rightIncident (G.right e) e).2 rfl
  have hLcard : (G.leftIncident (G.left e)).card = 2 := by
    simpa only [leftDegree] using hleft
  have hRcard : (G.rightIncident (G.right e)).card = 1 := by
    simpa only [rightDegree] using hright
  have hLerase : ((G.leftIncident (G.left e)).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem heL, hLcard]
  have hRerase : ((G.rightIncident (G.right e)).erase e).card = 0 := by
    rw [Finset.card_erase_of_mem heR, hRcard]
  have hRempty : (G.rightIncident (G.right e)).erase e = ∅ :=
    Finset.card_eq_zero.mp hRerase
  unfold fibreNeighbors
  rw [hRempty, Finset.union_empty, hLerase]

/-- Right endpoints in a free residual component are literally degree-one
vertices of the edge-copy line graph. -/
theorem freeComponent_rightEndpoint_lineDegree_eq_one
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2))
    (c : FreeTwoLabelComponent L) (e : E)
    (he : (fibreLineGraph G).connectedComponentMk e = c.val)
    (hright : G.rightDegree (G.right e) = 1) :
    (fibreLineGraph G).degree e = 1 := by
  classical
  change ((fibreLineGraph G).neighborFinset e).card = 1
  rw [← fibreNeighbors_eq_neighborFinset G e]
  exact freeComponent_rightEndpoint_fibreNeighbors_card_eq_one G L c e he hright

/-- In a q-profile component, each represented edge copy has one or two
line-graph neighbors.  The degree-one alternative is retained because it is
exactly where the two-parallel-edge multigraph cycle can occur. -/
theorem freeComponent_noRightEndpoint_fibreNeighbors_card_eq_one_or_two
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    (c : FreeTwoLabelComponent L)
    (hno : ¬ HasRightEndpoint G c.val)
    (e : E) (he : (fibreLineGraph G).connectedComponentMk e = c.val) :
    (fibreNeighbors G e).card = 1 ∨ (fibreNeighbors G e).card = 2 := by
  classical
  have hleft : G.leftDegree (G.left e) = 2 :=
    freeComponent_leftDegree_eq_two G L c e he
  have hrightTwo : G.rightDegree (G.right e) = 2 :=
    (freeComponent_noRightEndpoint_iff_all_rightDegree_two G L hright c).1 hno e he
  have heL : e ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) e).2 rfl
  have heR : e ∈ G.rightIncident (G.right e) :=
    (G.mem_rightIncident (G.right e) e).2 rfl
  have hLcard : (G.leftIncident (G.left e)).card = 2 := by
    simpa only [leftDegree] using hleft
  have hRcard : (G.rightIncident (G.right e)).card = 2 := by
    simpa only [rightDegree] using hrightTwo
  have hLerase : ((G.leftIncident (G.left e)).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem heL, hLcard]
  have hRerase : ((G.rightIncident (G.right e)).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem heR, hRcard]
  have hpos : 0 < (fibreNeighbors G e).card := by
    have hsub : (G.leftIncident (G.left e)).erase e ⊆ fibreNeighbors G e := by
      intro f hf
      exact Finset.mem_union_left _ hf
    have hle := Finset.card_le_card hsub
    omega
  have hle : (fibreNeighbors G e).card ≤ 2 := by
    unfold fibreNeighbors
    calc
      ((G.leftIncident (G.left e)).erase e ∪
          (G.rightIncident (G.right e)).erase e).card ≤
          ((G.leftIncident (G.left e)).erase e).card +
            ((G.rightIncident (G.right e)).erase e).card :=
        Finset.card_union_le _ _
      _ = 2 := by rw [hLerase, hRerase]
  omega

/-- The degree-one alternative inside a q-profile component can occur only
because the same second edge copy is seen from both shores.  Thus it produces
an actual parallel mate, which is precisely the local signature of the
length-two multigraph cycle that a simple line graph cannot itself display as
a cycle. -/
theorem freeComponent_noRightEndpoint_card_one_has_parallelMate
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    (c : FreeTwoLabelComponent L)
    (hno : ¬ HasRightEndpoint G c.val)
    (e : E) (he : (fibreLineGraph G).connectedComponentMk e = c.val)
    (hone : (fibreNeighbors G e).card = 1) :
    ∃ f : E, f ≠ e ∧ G.left f = G.left e ∧ G.right f = G.right e := by
  classical
  have hleft : G.leftDegree (G.left e) = 2 :=
    freeComponent_leftDegree_eq_two G L c e he
  have hrightTwo : G.rightDegree (G.right e) = 2 :=
    (freeComponent_noRightEndpoint_iff_all_rightDegree_two G L hright c).1 hno e he
  have heL : e ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) e).2 rfl
  have heR : e ∈ G.rightIncident (G.right e) :=
    (G.mem_rightIncident (G.right e) e).2 rfl
  have hLcard : (G.leftIncident (G.left e)).card = 2 := by
    simpa only [leftDegree] using hleft
  have hRcard : (G.rightIncident (G.right e)).card = 2 := by
    simpa only [rightDegree] using hrightTwo
  have hLerase : ((G.leftIncident (G.left e)).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem heL, hLcard]
  have hRerase : ((G.rightIncident (G.right e)).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem heR, hRcard]
  obtain ⟨f, hfL⟩ := Finset.card_eq_one.mp hLerase
  obtain ⟨g, hgR⟩ := Finset.card_eq_one.mp hRerase
  have hfUnion : f ∈ fibreNeighbors G e := by
    unfold fibreNeighbors
    rw [hfL]
    simp
  have hgUnion : g ∈ fibreNeighbors G e := by
    unfold fibreNeighbors
    rw [hgR]
    simp
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  have hfa : f = a := by
    rw [ha] at hfUnion
    simpa using hfUnion
  have hga : g = a := by
    rw [ha] at hgUnion
    simpa using hgUnion
  have hfg : f = g := hfa.trans hga.symm
  have hfErase : f ∈ (G.leftIncident (G.left e)).erase e := by
    rw [hfL]
    simp
  have hgErase : g ∈ (G.rightIncident (G.right e)).erase e := by
    rw [hgR]
    simp
  have hfne : f ≠ e := (Finset.mem_erase.mp hfErase).1
  have hfleft : G.left f = G.left e :=
    (G.mem_leftIncident (G.left e) f).1 (Finset.mem_erase.mp hfErase).2
  have hgright : G.right g = G.right e :=
    (G.mem_rightIncident (G.right e) g).1 (Finset.mem_erase.mp hgErase).2
  refine ⟨f, hfne, hfleft, ?_⟩
  simpa [hfg] using hgright

end BachThesisLean
