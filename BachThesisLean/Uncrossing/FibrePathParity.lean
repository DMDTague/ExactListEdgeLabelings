import BachThesisLean.Uncrossing.FibreAlternation
import BachThesisLean.Uncrossing.FibreParity

namespace BachThesisLean

open BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq E]

/-!
# Parity of simple degree-two fibre paths

Starting at a left-degree-one endpoint, the first line-graph transition must
share the right endpoint. Transition sides then alternate along a simple path.
Consequently a simple path whose two endpoint edge copies both meet
left-degree-one vertices has odd line-graph length.
-/

/-- Two vertices two steps apart in a simple path are distinct. -/
theorem fibreLineGraph_path_getVert_ne_add_two
    (G : BipartiteMultigraph X Y E) {e f : E}
    (p : (fibreLineGraph G).Walk e f) (hp : p.IsPath)
    {i : ℕ} (hi : i + 2 ≤ p.length) :
    p.getVert i ≠ p.getVert (i + 2) := by
  intro hEq
  have hi0 : i ∈ {j : ℕ | j ≤ p.length} := by
    change i ≤ p.length
    omega
  have hi2 : i + 2 ∈ {j : ℕ | j ≤ p.length} := by
    change i + 2 ≤ p.length
    exact hi
  have hidx := hp.getVert_injOn hi0 hi2 hEq
  omega

/-- Along a simple degree-two line-graph path that starts at a left-degree-one
edge copy, even-indexed transitions share the right shore and odd-indexed
transitions share the left shore. -/
theorem fibreLineGraph_path_transition_parity
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hp : p.IsPath)
    (hstart : G.leftDegree (G.left e) = 1) :
    ∀ i, i < p.length →
      (i % 2 = 0 →
        G.right (p.getVert i) = G.right (p.getVert (i + 1))) ∧
      (i % 2 = 1 →
        G.left (p.getVert i) = G.left (p.getVert (i + 1))) := by
  intro i
  induction i with
  | zero =>
      intro hi
      have hadj0 : (fibreLineGraph G).Adj e (p.getVert 1) := by
        simpa using p.adj_getVert_succ (i := 0) hi
      have hR0 := fibreLineGraph_adj_right_of_leftDegree_eq_one G hstart hadj0
      constructor
      · intro _
        simpa using hR0
      · intro hmod
        omega
  | succ i ih =>
      intro hi
      have hiprev : i < p.length := by omega
      have hprev := ih hiprev
      have hadjPrev := p.adj_getVert_succ (i := i) hiprev
      have hadjNext := p.adj_getVert_succ (i := i + 1) (by omega)
      have hne : p.getVert i ≠ p.getVert (i + 2) :=
        fibreLineGraph_path_getVert_ne_add_two G p hp (by omega)
      constructor
      · intro hmod
        have hprevOdd : i % 2 = 1 := by omega
        have hL := hprev.2 hprevOdd
        have hR := fibreLineGraph_next_right_of_current_left
          G hleft hright hadjPrev hadjNext hne hL
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hR
      · intro hmod
        have hprevEven : i % 2 = 0 := by omega
        have hR := hprev.1 hprevEven
        have hL := fibreLineGraph_next_left_of_current_right
          G hleft hright hadjPrev hadjNext hne hR
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hL

/-- A simple path between distinct edge copies whose left endpoints both have
degree one has odd length in the edge-copy line graph. -/
theorem fibreLineGraph_path_odd_of_leftDegree_one_ends
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hp : p.IsPath)
    (hef : e ≠ f)
    (hstart : G.leftDegree (G.left e) = 1)
    (hend : G.leftDegree (G.left f) = 1) :
    Odd p.length := by
  have hlenpos : 0 < p.length := by
    by_contra hnot
    have hzero : p.length = 0 := Nat.eq_zero_of_not_pos hnot
    have heq : e = f := by
      calc
        e = p.getVert 0 := by simp
        _ = p.getVert p.length := by rw [hzero]
        _ = f := by simp
    exact hef heq
  have hlastlt : p.length - 1 < p.length := by omega
  have hadjLast0 := p.adj_getVert_succ (i := p.length - 1) hlastlt
  have hadjLast :
      (fibreLineGraph G).Adj (p.getVert (p.length - 1)) f := by
    have hidx : p.length - 1 + 1 = p.length := by omega
    simpa [hidx] using hadjLast0
  have hnotLeftRev :=
    fibreLineGraph_adj_left_ne_of_leftDegree_eq_one G hend hadjLast.symm
  have hnotLeft :
      G.left (p.getVert (p.length - 1)) ≠ G.left f := by
    exact Ne.symm hnotLeftRev
  have hpar := fibreLineGraph_path_transition_parity
    G hleft hright p hp hstart (p.length - 1) hlastlt
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hlenmod : p.length % 2 = 0 := Nat.even_iff.mp heven
  have hpredmod : (p.length - 1) % 2 = 1 := by omega
  have hL0 := hpar.2 hpredmod
  have hidx : p.length - 1 + 1 = p.length := by omega
  have hL : G.left (p.getVert (p.length - 1)) = G.left f := by
    simpa [hidx] using hL0
  exact hnotLeft hL

/-- In a two-label fibre with right degree at most two, any simple line-graph
path joining an `A \ B` endpoint edge to a `B \ A` endpoint edge has odd
length. -/
theorem twoLabel_opposite_sdiff_path_odd
    [DecidableEq X]
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hp : p.IsPath)
    (hef : e ≠ f)
    (heA : G.left e ∈ A) (heB : G.left e ∉ B)
    (hfB : G.left f ∈ B) (hfA : G.left f ∉ A) :
    Odd p.length := by
  apply fibreLineGraph_path_odd_of_leftDegree_one_ends
    G (twoLabel_leftDegree_le_two G A B hdeg) hright p hp hef
  · exact (twoLabel_leftDegree_eq_one_iff G A B hdeg (G.left e)).2
      (Or.inl ⟨heA, heB⟩)
  · exact (twoLabel_leftDegree_eq_one_iff G A B hdeg (G.left f)).2
      (Or.inr ⟨hfA, hfB⟩)

/-- Therefore such a simple left--left path component forces the uncrossed
local completion count to vanish. This is the manuscript's zero entry for an
opposite-type left--left path. -/
theorem twoLabelUncrossedCount_eq_zero_of_opposite_sdiff_path
    [DecidableEq X]
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2)
    {e f : E} (p : (fibreLineGraph G).Walk e f) (hp : p.IsPath)
    (hef : e ≠ f)
    (heA : G.left e ∈ A) (heB : G.left e ∉ B)
    (hfB : G.left f ∈ B) (hfA : G.left f ∉ A) :
    twoLabelUncrossedCount G A B hdeg = 0 := by
  apply twoLabelUncrossedCount_eq_zero_of_odd_walk_between_opposite_sdiff
    G A B hdeg p
  · exact twoLabel_opposite_sdiff_path_odd
      G A B hdeg hright p hp hef heA heB hfB hfA
  · exact heA
  · exact heB
  · exact hfB
  · exact hfA

end BachThesisLean
