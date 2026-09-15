import BachThesisLean.Uncrossing.FibreGraph

namespace BachThesisLean

open BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq E]

/-!
# Alternating-side structure in the degree-two fibre

A path in the edge-copy line graph alternates between sharing a left endpoint
and sharing a right endpoint. The key local fact is that three distinct edge
copies cannot all meet the same endpoint when the corresponding degree is at
most two.
-/

/-- Three pairwise distinct edge copies cannot share one left endpoint if all
left degrees are at most two. -/
theorem no_three_distinct_same_left
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    {e f g : E} (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hefL : G.left e = G.left f) (hfgL : G.left f = G.left g) : False := by
  classical
  let S : Finset E := {e, f, g}
  have hsub : S ⊆ G.leftIncident (G.left f) := by
    intro a ha
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · subst a
      exact (G.mem_leftIncident (G.left f) e).2 hefL
    · subst a
      exact (G.mem_leftIncident (G.left f) f).2 rfl
    · subst a
      exact (G.mem_leftIncident (G.left f) g).2 hfgL.symm
  have hcardS : S.card = 3 := by
    simp [S, hef, hfg, heg]
  have hle := Finset.card_le_card hsub
  rw [hcardS] at hle
  exact Nat.not_succ_le_self 2 (hle.trans (hleft (G.left f)))

/-- Three pairwise distinct edge copies cannot share one right endpoint if all
right degrees are at most two. -/
theorem no_three_distinct_same_right
    (G : BipartiteMultigraph X Y E)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f g : E} (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hefR : G.right e = G.right f) (hfgR : G.right f = G.right g) : False := by
  classical
  let S : Finset E := {e, f, g}
  have hsub : S ⊆ G.rightIncident (G.right f) := by
    intro a ha
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · subst a
      exact (G.mem_rightIncident (G.right f) e).2 hefR
    · subst a
      exact (G.mem_rightIncident (G.right f) f).2 rfl
    · subst a
      exact (G.mem_rightIncident (G.right f) g).2 hfgR.symm
  have hcardS : S.card = 3 := by
    simp [S, hef, hfg, heg]
  have hle := Finset.card_le_card hsub
  rw [hcardS] at hle
  exact Nat.not_succ_le_self 2 (hle.trans (hright (G.right f)))

/-- For three distinct consecutive vertices of a line-graph walk, the two
adjacencies must use opposite shores when both endpoint degrees are at most
two. -/
theorem fibreLineGraph_adj_sides_alternate
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f g : E}
    (hef : (fibreLineGraph G).Adj e f)
    (hfg : (fibreLineGraph G).Adj f g)
    (heg : e ≠ g) :
    (G.left e = G.left f ∧ G.right f = G.right g) ∨
      (G.right e = G.right f ∧ G.left f = G.left g) := by
  rcases hef with ⟨hef_ne, hefL | hefR⟩
  · rcases hfg with ⟨hfg_ne, hfgL | hfgR⟩
    · exact (no_three_distinct_same_left G hleft hef_ne hfg_ne heg hefL hfgL).elim
    · exact Or.inl ⟨hefL, hfgR⟩
  · rcases hfg with ⟨hfg_ne, hfgL | hfgR⟩
    · exact Or.inr ⟨hefR, hfgL⟩
    · exact (no_three_distinct_same_right G hright hef_ne hfg_ne heg hefR hfgR).elim

/-- At an edge copy whose left endpoint has degree one, every line-graph
neighbor is reached through the right endpoint. -/
theorem fibreLineGraph_adj_right_of_leftDegree_eq_one
    (G : BipartiteMultigraph X Y E) {e f : E}
    (hdeg : G.leftDegree (G.left e) = 1)
    (hef : (fibreLineGraph G).Adj e f) :
    G.right e = G.right f := by
  rcases hef with ⟨hef_ne, hleft | hright⟩
  · classical
    have he : e ∈ G.leftIncident (G.left e) :=
      (G.mem_leftIncident (G.left e) e).2 rfl
    have hf : f ∈ G.leftIncident (G.left e) :=
      (G.mem_leftIncident (G.left e) f).2 hleft.symm
    have hcard : (G.leftIncident (G.left e)).card = 1 := by
      simpa only [leftDegree] using hdeg
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    rw [ha] at he hf
    simp only [Finset.mem_singleton] at he hf
    exact (hef_ne (he.trans hf.symm)).elim
  · exact hright

/-- A degree-one left endpoint cannot also be shared by a distinct line-graph
neighbor. This is the endpoint exclusivity needed to read off path parity. -/
theorem fibreLineGraph_adj_left_ne_of_leftDegree_eq_one
    (G : BipartiteMultigraph X Y E) {e f : E}
    (hdeg : G.leftDegree (G.left e) = 1)
    (hef : (fibreLineGraph G).Adj e f) :
    G.left e ≠ G.left f := by
  intro hleft
  classical
  have he : e ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) e).2 rfl
  have hf : f ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) f).2 hleft.symm
  have hcard : (G.leftIncident (G.left e)).card = 1 := by
    simpa only [leftDegree] using hdeg
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  rw [ha] at he hf
  simp only [Finset.mem_singleton] at he hf
  exact hef.1 (he.trans hf.symm)

/-- Symmetrically, at an edge copy whose right endpoint has degree one, every
line-graph neighbor is reached through the left endpoint. -/
theorem fibreLineGraph_adj_left_of_rightDegree_eq_one
    (G : BipartiteMultigraph X Y E) {e f : E}
    (hdeg : G.rightDegree (G.right e) = 1)
    (hef : (fibreLineGraph G).Adj e f) :
    G.left e = G.left f := by
  rcases hef with ⟨hef_ne, hleft | hright⟩
  · exact hleft
  · classical
    have he : e ∈ G.rightIncident (G.right e) :=
      (G.mem_rightIncident (G.right e) e).2 rfl
    have hf : f ∈ G.rightIncident (G.right e) :=
      (G.mem_rightIncident (G.right e) f).2 hright.symm
    have hcard : (G.rightIncident (G.right e)).card = 1 := by
      simpa only [rightDegree] using hdeg
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    rw [ha] at he hf
    simp only [Finset.mem_singleton] at he hf
    exact (hef_ne (he.trans hf.symm)).elim

end BachThesisLean
