import BachThesisLean.Uncrossing.GlobalPairGraph

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# Parity in a globally frozen pair fibre

The full admissible labeling freezes every label except `a,b`.  On the active
pair graph, a left endpoint lying outside `S a ∩ S b` is forced to carry `a`
after uncrossing.  The same alternating-side argument used in the local fibre
therefore applies without changing the ambient edge-copy type.
-/

/-- An active edge whose left endpoint is not in both original supports must
carry the union label `a` in an admissible uncrossed full labeling. -/
theorem uncrossed_active_eq_a_of_not_inter
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e : E} (heP : e ∈ pairEdges σ a b)
    (hnot : ¬ (G.left e ∈ S a ∧ G.left e ∈ S b)) :
    σ e = a := by
  rcases (mem_pairEdges σ a b e).1 heP with hea | heb
  · exact hea
  · have hm := hσ.label_mem e
    change σ e ∈ listsOfSupports (uncross S a b) (G.left e) at hm
    rw [mem_listsOfSupports] at hm
    rw [heb, uncross_at_right S hab] at hm
    exact (hnot (Finset.mem_inter.mp hm)).elim

/-- At a nonintersection left endpoint, an active-pair adjacency cannot use
the left shore; it must use the right shore. -/
theorem pairEdgeGraph_adj_right_of_not_inter
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e f : E}
    (hnot : ¬ (G.left e ∈ S a ∧ G.left e ∈ S b))
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f) :
    G.right e = G.right f := by
  rcases hef with ⟨hef_ne, heP, hfP, hL | hR⟩
  · have hnotf : ¬ (G.left f ∈ S a ∧ G.left f ∈ S b) := by
      intro hf
      apply hnot
      rw [hL]
      exact hf
    have heqA := uncrossed_active_eq_a_of_not_inter
      G S hab hinc hσ heP hnot
    have hfqA := uncrossed_active_eq_a_of_not_inter
      G S hab hinc hσ hfP hnotf
    have heq : e = f := hσ.left_injOn (G.left e)
      ((G.mem_leftIncident (G.left e) e).2 rfl)
      ((G.mem_leftIncident (G.left e) f).2 hL.symm)
      (heqA.trans hfqA.symm)
    exact (hef_ne heq).elim
  · exact hR

/-- The same endpoint condition forbids sharing the left shore with any
distinct active neighbor. -/
theorem pairEdgeGraph_adj_left_ne_of_not_inter
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e f : E}
    (hnot : ¬ (G.left e ∈ S a ∧ G.left e ∈ S b))
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f) :
    G.left e ≠ G.left f := by
  intro hL
  rcases hef with ⟨hef_ne, heP, hfP, _⟩
  have hnotf : ¬ (G.left f ∈ S a ∧ G.left f ∈ S b) := by
    intro hf
    apply hnot
    rw [hL]
    exact hf
  have heqA := uncrossed_active_eq_a_of_not_inter
    G S hab hinc hσ heP hnot
  have hfqA := uncrossed_active_eq_a_of_not_inter
    G S hab hinc hσ hfP hnotf
  have heq : e = f := hσ.left_injOn (G.left e)
    ((G.mem_leftIncident (G.left e) e).2 rfl)
    ((G.mem_leftIncident (G.left e) f).2 hL.symm)
    (heqA.trans hfqA.symm)
  exact hef_ne heq

/-- A transition cannot share both shores if a simple active path continues
through a third distinct edge copy. -/
theorem pairEdgeGraph_adj_not_both_of_next
    {G : BipartiteMultigraph X Y E} {L : ExactLeftLists G Λ}
    {σ : E → Λ} (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b)
    {e f g : E}
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f)
    (hfg : (pairEdgeGraph G (pairEdges σ a b)).Adj f g)
    (heg : e ≠ g) :
    ¬ (G.left e = G.left f ∧ G.right e = G.right f) := by
  intro hboth
  rcases hef with ⟨hef_ne, heP, hfP, _⟩
  rcases hfg with ⟨hfg_ne, _, hgP, hfgL | hfgR⟩
  · exact no_three_active_same_left G hσ hab heP hfP hgP
      hef_ne hfg_ne heg hboth.1 hfgL
  · exact no_three_active_same_right G hσ hab heP hfP hgP
      hef_ne hfg_ne heg hboth.2 hfgR

/-- A right-sharing transition is followed by a left-sharing transition. -/
theorem pairEdgeGraph_next_left_of_current_right
    {G : BipartiteMultigraph X Y E} {L : ExactLeftLists G Λ}
    {σ : E → Λ} (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b)
    {e f g : E}
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f)
    (hfg : (pairEdgeGraph G (pairEdges σ a b)).Adj f g)
    (heg : e ≠ g) (hR : G.right e = G.right f) :
    G.left f = G.left g := by
  rcases pairEdgeGraph_adj_sides_alternate G hσ hab hef hfg heg with hLR | hRL
  · exact (pairEdgeGraph_adj_not_both_of_next hσ hab hef hfg heg
      ⟨hLR.1, hR⟩).elim
  · exact hRL.2

/-- A left-sharing transition is followed by a right-sharing transition. -/
theorem pairEdgeGraph_next_right_of_current_left
    {G : BipartiteMultigraph X Y E} {L : ExactLeftLists G Λ}
    {σ : E → Λ} (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b)
    {e f g : E}
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f)
    (hfg : (pairEdgeGraph G (pairEdges σ a b)).Adj f g)
    (heg : e ≠ g) (hL : G.left e = G.left f) :
    G.right f = G.right g := by
  rcases pairEdgeGraph_adj_sides_alternate G hσ hab hef hfg heg with hLR | hRL
  · exact hLR.2
  · exact (pairEdgeGraph_adj_not_both_of_next hσ hab hef hfg heg
      ⟨hL, hRL.1⟩).elim

/-- Two vertices two transitions apart in a simple active-pair path are
distinct. -/
theorem pairEdgeGraph_path_getVert_ne_add_two
    (G : BipartiteMultigraph X Y E) (P : Finset E)
    {e f : E} (p : (pairEdgeGraph G P).Walk e f) (hp : p.IsPath)
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

/-- Starting at a nonintersection left endpoint, even-indexed active-pair
transitions share the right shore and odd-indexed transitions share the left
shore. -/
theorem pairEdgeGraph_path_transition_parity
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e f : E}
    (p : (pairEdgeGraph G (pairEdges σ a b)).Walk e f) (hp : p.IsPath)
    (hstart : ¬ (G.left e ∈ S a ∧ G.left e ∈ S b)) :
    ∀ i, i < p.length →
      (i % 2 = 0 → G.right (p.getVert i) = G.right (p.getVert (i + 1))) ∧
      (i % 2 = 1 → G.left (p.getVert i) = G.left (p.getVert (i + 1))) := by
  intro i
  induction i with
  | zero =>
      intro hi
      have hadj0 : (pairEdgeGraph G (pairEdges σ a b)).Adj e (p.getVert 1) := by
        simpa using p.adj_getVert_succ (i := 0) hi
      have hR0 := pairEdgeGraph_adj_right_of_not_inter
        G S hab hinc hσ hstart hadj0
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
        pairEdgeGraph_path_getVert_ne_add_two G (pairEdges σ a b) p hp (by omega)
      constructor
      · intro hmod
        have hprevOdd : i % 2 = 1 := by omega
        have hL := hprev.2 hprevOdd
        have hR := pairEdgeGraph_next_right_of_current_left
          hσ hab hadjPrev hadjNext hne hL
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hR
      · intro hmod
        have hprevEven : i % 2 = 0 := by omega
        have hR := hprev.1 hprevEven
        have hL := pairEdgeGraph_next_left_of_current_right
          hσ hab hadjPrev hadjNext hne hR
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hL

/-- A simple active-pair path between two nonintersection left endpoints has
odd length. -/
theorem pairEdgeGraph_path_odd_of_noninter_ends
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e f : E}
    (p : (pairEdgeGraph G (pairEdges σ a b)).Walk e f) (hp : p.IsPath)
    (hef : e ≠ f)
    (hstart : ¬ (G.left e ∈ S a ∧ G.left e ∈ S b))
    (hend : ¬ (G.left f ∈ S a ∧ G.left f ∈ S b)) :
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
  have hidx : p.length - 1 + 1 = p.length := by omega
  have hadjLast : (pairEdgeGraph G (pairEdges σ a b)).Adj
      (p.getVert (p.length - 1)) f := by
    simpa [hidx] using hadjLast0
  have hnotLeftRev := pairEdgeGraph_adj_left_ne_of_not_inter
    G S hab hinc hσ hend hadjLast.symm
  have hnotLeft : G.left (p.getVert (p.length - 1)) ≠ G.left f :=
    Ne.symm hnotLeftRev
  have hpar := pairEdgeGraph_path_transition_parity
    G S hab hinc hσ p hp hstart (p.length - 1) hlastlt
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hlenmod : p.length % 2 = 0 := Nat.even_iff.mp heven
  have hpredmod : (p.length - 1) % 2 = 1 := by omega
  have hL0 := hpar.2 hpredmod
  have hL : G.left (p.getVert (p.length - 1)) = G.left f := by
    simpa [hidx] using hL0
  exact hnotLeft hL

/-- Opposite symmetric-difference endpoints cannot lie in one active-pair
component of an admissible uncrossed full labeling. -/
theorem no_reachable_opposite_sdiff_global
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e f : E}
    (heP : e ∈ pairEdges σ a b) (hfP : f ∈ pairEdges σ a b)
    (heA : G.left e ∈ S a) (heB : G.left e ∉ S b)
    (hfB : G.left f ∈ S b) (hfA : G.left f ∉ S a) :
    ¬ (pairEdgeGraph G (pairEdges σ a b)).Reachable e f := by
  intro hreach
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hef : e ≠ f := by
    intro h
    subst f
    exact hfA heA
  have hodd := pairEdgeGraph_path_odd_of_noninter_ends
    G S hab hinc hσ p hp hef
    (by exact fun hboth => heB hboth.2)
    (by exact fun hboth => hfA hboth.1)
  have hne := finTwoColoring_ne_of_odd_walk
    (admissiblePairColoring G σ hσ hab) p hodd
  have hea := uncrossed_active_eq_a_of_not_inter G S hab hinc hσ heP
    (by exact fun hboth => heB hboth.2)
  have hfa := uncrossed_active_eq_a_of_not_inter G S hab hinc hσ hfP
    (by exact fun hboth => hfA hboth.1)
  apply hne
  change pairCode σ a e = pairCode σ a f
  simp [pairCode, hea, hfa]

end BachThesisLean
