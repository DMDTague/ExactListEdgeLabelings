import BachThesisLean.Uncrossing.ResidualSurplus

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq E]

/-!
# Cycle/right--right-path exponent bookkeeping

In a contributing two-label residual fibre every active component has left and
right degrees at most two. A free component has full two-label lists on every
left endpoint, hence every left degree is exactly two. Consequently its only
possible path endpoints are on the right shore. The manuscript's `q` and `r`
therefore split the free components according to whether a right degree-one
endpoint is absent or present.
-/

/-- A connected edge-copy component has a right endpoint when it contains an
actual edge copy whose right endpoint has residual degree one. -/
def HasRightEndpoint
    (G : BipartiteMultigraph X Y E)
    (c : (fibreLineGraph G).ConnectedComponent) : Prop :=
  ∃ e : E, (fibreLineGraph G).connectedComponentMk e = c ∧
    G.rightDegree (G.right e) = 1

/-- Manuscript `q`: free components with no right endpoint. Under the
contributing-fibre degree bound these are exactly the even-cycle components. -/
noncomputable def freeEvenCycleComponentCount
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2)) : ℕ := by
  classical
  exact Fintype.card
    {c : FreeTwoLabelComponent L // ¬ HasRightEndpoint G c.val}

/-- Manuscript `r`: free components with a right endpoint. Since a free
component has no left endpoint, under the degree-two residual hypotheses these
are exactly the right--right path components. -/
noncomputable def freeRightRightPathComponentCount
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2)) : ℕ := by
  classical
  exact Fintype.card
    {c : FreeTwoLabelComponent L // HasRightEndpoint G c.val}

/-- Every actual edge copy witnesses positive degree at each of its endpoints. -/
theorem rightDegree_pos_at_edge
    (G : BipartiteMultigraph X Y E) (e : E) :
    0 < G.rightDegree (G.right e) := by
  classical
  unfold rightDegree
  apply Finset.card_pos.mpr
  exact ⟨e, (G.mem_rightIncident (G.right e) e).2 rfl⟩

/-- On a right-degree-at-most-two residual graph, every actual edge copy sees
right degree one or two. -/
theorem rightDegree_eq_one_or_two_at_edge
    (G : BipartiteMultigraph X Y E)
    (hright : ∀ y, G.rightDegree y ≤ 2) (e : E) :
    G.rightDegree (G.right e) = 1 ∨ G.rightDegree (G.right e) = 2 := by
  have hpos := rightDegree_pos_at_edge G e
  have hle := hright (G.right e)
  omega

/-- A free component has left degree two at every represented edge copy. -/
theorem freeComponent_leftDegree_eq_two
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2))
    (c : FreeTwoLabelComponent L) (e : E)
    (he : (fibreLineGraph G).connectedComponentMk e = c.val) :
    G.leftDegree (G.left e) = 2 := by
  apply (twoLabel_labels_eq_univ_iff L (G.left e)).1
  exact c.property e he

/-- Under the contributing-fibre right-degree bound, absence of a right
endpoint is equivalent to the degree profile of a cycle component: every
right endpoint in the connected free component also has degree two. Together
with `freeComponent_leftDegree_eq_two`, this is the bipartite even-cycle
profile, including the two-parallel-edge cycle. -/
theorem freeComponent_noRightEndpoint_iff_all_rightDegree_two
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    (c : FreeTwoLabelComponent L) :
    ¬ HasRightEndpoint G c.val ↔
      ∀ e : E, (fibreLineGraph G).connectedComponentMk e = c.val →
        G.rightDegree (G.right e) = 2 := by
  constructor
  · intro hno e he
    rcases rightDegree_eq_one_or_two_at_edge G hright e with h1 | h2
    · exact (hno ⟨e, he, h1⟩).elim
    · exact h2
  · intro hall ⟨e, he, h1⟩
    have h2 := hall e he
    omega

/-- The free binary factors split exactly into the manuscript cycle factors
and right--right-path factors. This identity itself needs no admissibility
assumption; the degree bound is used by the preceding theorem to identify the
first summand with the graphical cycle class. -/
theorem freeTwoLabelComponentCount_eq_cycle_add_rightPath
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G (Fin 2)) :
    freeTwoLabelComponentCount L =
      freeEvenCycleComponentCount G L + freeRightRightPathComponentCount G L := by
  classical
  let p : FreeTwoLabelComponent L → Prop := fun c => HasRightEndpoint G c.val
  let e : FreeTwoLabelComponent L ≃
      {c : FreeTwoLabelComponent L // p c} ⊕
        {c : FreeTwoLabelComponent L // ¬ p c} :=
    (Equiv.sumCompl p).symm
  unfold freeTwoLabelComponentCount freeEvenCycleComponentCount
    freeRightRightPathComponentCount
  rw [Fintype.card_congr e, Fintype.card_sum]
  change Fintype.card {c : FreeTwoLabelComponent L // p c} +
      Fintype.card {c : FreeTwoLabelComponent L // ¬ p c} =
    Fintype.card {c : FreeTwoLabelComponent L // ¬ HasRightEndpoint G c.val} +
      Fintype.card {c : FreeTwoLabelComponent L // HasRightEndpoint G c.val}
  simp [p, Nat.add_comm]

end BachThesisLean
