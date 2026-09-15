import BachThesisLean.Cubic.BadPairSeparation
import BachThesisLean.Cubic.MinimalCounterexampleSize

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# The three-vertex-per-shore brace case

A simple cubic bipartite multigraph with three vertices on each shore has one
edge in every endpoint cell: at each left vertex the three incident copies have
three distinct right endpoints, and there are only three right vertices.

For a cubic brace on these shores, this full-support description discharges
EEP directly.  Adjacent prescribed copies are handled by the common-vertex
lemma.  For an endpoint-disjoint pair, use the two cross edges and
2-extendability to force a perfect matching through them.  The two edges from
the prescribed left endpoints to the third right vertex then lie outside that
matching and give the explicit complementary-factor bridge.
-/

/-- At a fixed left vertex of a simple cubic graph, the three incident edge
copies have three distinct right endpoints. -/
theorem rightNeighborSet_card_eq_three_of_simple_cubic
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (x : X) : (G.rightNeighborSet x).card = 3 := by
  classical
  have hinj : Set.InjOn G.right (G.leftIncident x) := by
    intro e he f hf hright
    apply hsimple
    apply Prod.ext
    · exact ((G.mem_leftIncident x e).1 he).trans
        ((G.mem_leftIncident x f).1 hf).symm
    · exact hright
  have hcardImage :
      ((G.leftIncident x).image G.right).card = (G.leftIncident x).card :=
    Finset.card_image_iff.mpr hinj
  rw [rightNeighborSet, hcardImage]
  simpa using hG (.inl x)

/-- A simple cubic graph with three left vertices has an actual edge copy in
every left/right endpoint cell. -/
theorem fullSupport_of_simple_cubic_card_left_eq_three
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (hX : Fintype.card X = 3) :
    ∀ x y, ∃ e : E, G.left e = x ∧ G.right e = y := by
  classical
  have hY : Fintype.card Y = 3 := by
    calc
      Fintype.card Y = Fintype.card X :=
        (G.card_left_eq_card_right_of_cubic hG).symm
      _ = 3 := hX
  intro x y
  have hN : (G.rightNeighborSet x).card = 3 :=
    G.rightNeighborSet_card_eq_three_of_simple_cubic hsimple hG x
  have hy : y ∈ G.rightNeighborSet x := by
    by_contra hmissing
    have hsub :
        G.rightNeighborSet x ⊆ (Finset.univ : Finset Y).erase y := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨by
        intro hzy
        subst z
        exact hmissing hz, Finset.mem_univ z⟩
    have hcard := Finset.card_le_card hsub
    have herase : ((Finset.univ : Finset Y).erase y).card = 2 := by
      simp [hY]
    rw [hN, herase] at hcard
    omega
  obtain ⟨e, heI, heR⟩ := (mem_rightNeighborSet G x y).1 hy
  exact ⟨e, (G.mem_leftIncident x e).1 heI, heR⟩

/-- In a three-element finite type, two distinct elements have a third
companion. -/
private theorem exists_third_of_card_eq_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 3) {a b : α} (hab : a ≠ b) :
    ∃ c : α, c ≠ a ∧ c ≠ b := by
  classical
  by_contra hnone
  have hall : ∀ c : α, c = a ∨ c = b := by
    intro c
    by_cases hca : c = a
    · exact Or.inl hca
    by_cases hcb : c = b
    · exact Or.inr hcb
    exact (hnone ⟨c, hca, hcb⟩).elim
  have hsub : (Finset.univ : Finset α) ⊆ ({a, b} : Finset α) := by
    intro c _
    rcases hall c with rfl | rfl <;> simp
  have hle := Finset.card_le_card hsub
  have hp : ({a, b} : Finset α).card = 2 := by simp [hab]
  simp only [Finset.card_univ, hcard, hp] at hle
  omega

/-- Every cubic brace with three vertices on its left shore has EEP.  This is
the first simple terminal size beyond the nonsimple one- and two-shore cases. -/
theorem IsBrace.hasEEP_of_card_left_eq_three
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : Fintype.card X = 3) : G.HasEEP := by
  classical
  have hthree : 3 ≤ Fintype.card X := by omega
  have hsimple : G.IsSimple :=
    hbrace.isSimple_of_three_le_card_left hG hthree
  have hsupport : ∀ x y, ∃ e : E, G.left e = x ∧ G.right e = y :=
    G.fullSupport_of_simple_cubic_card_left_eq_three hsimple hG hX
  have hY : Fintype.card Y = 3 := by
    calc
      Fintype.card Y = Fintype.card X :=
        (G.card_left_eq_card_right_of_cubic hG).symm
      _ = 3 := hX
  intro e f hef
  by_cases hleft : G.left e = G.left f
  · exact hbrace.1.edgePairWitness_of_common_vertex hG hef
      (r := .inl (G.left e)) rfl (by
        change G.left f = G.left e
        exact hleft.symm)
  by_cases hright : G.right e = G.right f
  · exact hbrace.1.edgePairWitness_of_common_vertex hG hef
      (r := .inr (G.right e)) rfl (by
        change G.right f = G.right e
        exact hright.symm)
  obtain ⟨p, hpL, hpR⟩ := hsupport (G.left e) (G.right f)
  obtain ⟨q, hqL, hqR⟩ := hsupport (G.left f) (G.right e)
  have hpqLeft : G.left p ≠ G.left q := by
    rw [hpL, hqL]
    exact hleft
  have hpqRight : G.right p ≠ G.right q := by
    rw [hpR, hqR]
    intro h
    exact hright h.symm
  obtain ⟨P, hP, hpP, hqP⟩ :=
    hbrace.exists_perfectMatching_containing_two_edges
      hG p q hpqLeft hpqRight
  have hep : e ≠ p := by
    intro hEq
    have hr := congrArg G.right hEq
    rw [hpR] at hr
    exact hright hr
  have hfq : f ≠ q := by
    intro hEq
    have hr := congrArg G.right hEq
    rw [hqR] at hr
    exact hright hr.symm
  have heNot : e ∉ P := by
    intro heP
    exact hep
      ((G.isMatching_iff P).1 hP.isMatching
        e heP p hpP (.inl (G.left e)) rfl hpL)
  have hfNot : f ∉ P := by
    intro hfP
    exact hfq
      ((G.isMatching_iff P).1 hP.isMatching
        f hfP q hqP (.inl (G.left f)) rfl hqL)
  obtain ⟨y3, hy3e, hy3f⟩ :=
    exists_third_of_card_eq_three (α := Y) hY hright
  obtain ⟨a, haL, haR⟩ := hsupport (G.left e) y3
  obtain ⟨b, hbL, hbR⟩ := hsupport (G.left f) y3
  have hap : a ≠ p := by
    intro hEq
    have hr := congrArg G.right hEq
    rw [haR, hpR] at hr
    exact hy3f hr
  have hbq : b ≠ q := by
    intro hEq
    have hr := congrArg G.right hEq
    rw [hbR, hqR] at hr
    exact hy3e hr
  have haNot : a ∉ P := by
    intro haP
    exact hap
      ((G.isMatching_iff P).1 hP.isMatching
        a haP p hpP (.inl (G.left e)) haL hpL)
  have hbNot : b ∉ P := by
    intro hbP
    exact hbq
      ((G.isMatching_iff P).1 hP.isMatching
        b hbP q hqP (.inl (G.left f)) hbL hqL)
  apply edgePairWitness_of_bridgeCertificate G
  exact ⟨P, hP, heNot, hfNot, Or.inr
    ⟨a, b, haNot, hbNot, haL, hbL, haR.trans hbR.symm⟩⟩

namespace IsMinimalEEPCounterexample

/-- The three-vertex-per-shore brace case is not a minimal counterexample, so
a minimal EEP counterexample has at least four vertices on its left shore. -/
theorem four_le_card_left (hmin : G.IsMinimalEEPCounterexample) :
    4 ≤ Fintype.card X := by
  by_contra hfour
  have hlt : Fintype.card X < 4 := Nat.lt_of_not_ge hfour
  have hX : Fintype.card X = 3 := by
    have hthree := hmin.three_le_card_left
    omega
  exact hmin.failsEEP
    (hmin.isBrace.hasEEP_of_card_left_eq_three hmin.cubic hX)

/-- The same lower bound holds on the right shore. -/
theorem four_le_card_right (hmin : G.IsMinimalEEPCounterexample) :
    4 ≤ Fintype.card Y := by
  rw [← G.card_left_eq_card_right_of_cubic hmin.cubic]
  exact hmin.four_le_card_left

/-- Therefore a minimal EEP counterexample has at least eight vertices. -/
theorem eight_le_vertexCard (hmin : G.IsMinimalEEPCounterexample) :
    8 ≤ G.vertexCard := by
  rw [vertexCard, ← G.card_left_eq_card_right_of_cubic hmin.cubic]
  have hleft := hmin.four_le_card_left
  omega

/-- Therefore a minimal EEP counterexample has at least twelve actual edge
copies. -/
theorem twelve_le_edgeCard (hmin : G.IsMinimalEEPCounterexample) :
    12 ≤ Fintype.card E := by
  rw [G.edgeCard_eq_three_mul_leftCard_of_cubic hmin.cubic]
  have hleft := hmin.four_le_card_left
  omega

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
