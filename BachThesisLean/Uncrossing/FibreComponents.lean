import BachThesisLean.Uncrossing.FibrePathParity

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq E]

/-!
# Connected components of the two-label fibre

For the local uncrossing injection we flip all two-label colors on exactly
those edge-copy line-graph components that contain a `B \ A` left endpoint.
The path-parity theorem shows that an admissible uncrossed coloring prevents
such a component from also containing an `A \ B` endpoint.
-/

/-- Under an admissible uncrossed coloring, opposite symmetric-difference
left endpoints cannot lie in the same line-graph component. -/
theorem no_reachable_opposite_sdiff_of_uncrossed_admissible
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {σ : E → Fin 2}
    (hσ : (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ)
    {e f : E}
    (heA : G.left e ∈ A) (heB : G.left e ∉ B)
    (hfB : G.left f ∈ B) (hfA : G.left f ∉ A) :
    ¬ (fibreLineGraph G).Reachable e f := by
  intro hreach
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hef : e ≠ f := by
    intro h
    subst f
    exact hfA heA
  have hodd := twoLabel_opposite_sdiff_path_odd
    G A B hdeg hright p hp hef heA heB hfB hfA
  exact (no_uncrossed_admissible_of_odd_walk_between_opposite_sdiff
    G A B hdeg p hodd heA heB hfB hfA) hσ

/-- The component predicate used by the canonical flip: an edge copy is in a
component containing a `B \ A` endpoint. -/
def reachesRightSdiffEndpoint
    (G : BipartiteMultigraph X Y E) (A B : Finset X) (e : E) : Prop :=
  ∃ f : E, (fibreLineGraph G).Reachable e f ∧
    G.left f ∈ B ∧ G.left f ∉ A

/-- The component predicate is constant across a line-graph edge. -/
theorem reachesRightSdiffEndpoint_adj_iff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    {e f : E} (hef : (fibreLineGraph G).Adj e f) :
    reachesRightSdiffEndpoint G A B e ↔
      reachesRightSdiffEndpoint G A B f := by
  constructor
  · rintro ⟨g, heg, hgB, hgA⟩
    exact ⟨g, hef.symm.reachable.trans heg, hgB, hgA⟩
  · rintro ⟨g, hfg, hgB, hgA⟩
    exact ⟨g, hef.reachable.trans hfg, hgB, hgA⟩

/-- Hence the component predicate is constant on edge copies sharing a left
endpoint. -/
theorem reachesRightSdiffEndpoint_same_left_iff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    {e f : E} (hefL : G.left e = G.left f) :
    reachesRightSdiffEndpoint G A B e ↔
      reachesRightSdiffEndpoint G A B f := by
  by_cases hef : e = f
  · subst f
    rfl
  · exact reachesRightSdiffEndpoint_adj_iff G A B
      ⟨hef, Or.inl hefL⟩

/-- Likewise the component predicate is constant on edge copies sharing a
right endpoint. -/
theorem reachesRightSdiffEndpoint_same_right_iff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    {e f : E} (hefR : G.right e = G.right f) :
    reachesRightSdiffEndpoint G A B e ↔
      reachesRightSdiffEndpoint G A B f := by
  by_cases hef : e = f
  · subst f
    rfl
  · exact reachesRightSdiffEndpoint_adj_iff G A B
      ⟨hef, Or.inr hefR⟩

/-- Every edge copy incident with a `B \ A` endpoint is in a component marked
for flipping, by reflexive reachability. -/
theorem reachesRightSdiffEndpoint_of_right_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X) {e : E}
    (hB : G.left e ∈ B) (hA : G.left e ∉ A) :
    reachesRightSdiffEndpoint G A B e := by
  exact ⟨e, SimpleGraph.Reachable.rfl, hB, hA⟩

/-- Under an admissible uncrossed coloring, an `A \ B` endpoint component is
not marked for flipping. -/
theorem not_reachesRightSdiffEndpoint_of_left_sdiff
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {σ : E → Fin 2}
    (hσ : (twoLabelLists G (A ∪ B) (A ∩ B)
      (uncrossed_twoLabel_degree G A B hdeg)).IsAdmissible σ)
    {e : E} (hA : G.left e ∈ A) (hB : G.left e ∉ B) :
    ¬ reachesRightSdiffEndpoint G A B e := by
  rintro ⟨f, hef, hfB, hfA⟩
  exact no_reachable_opposite_sdiff_of_uncrossed_admissible
    G A B hdeg hright hσ hA hB hfB hfA hef

end BachThesisLean
