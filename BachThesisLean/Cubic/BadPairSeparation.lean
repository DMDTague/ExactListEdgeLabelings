import BachThesisLean.Cubic.SquareBadPair

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Separation of bad edge pairs

In a cubic matching-covered graph, two distinct edge copies incident with the
same vertex automatically have an EEP witness.  The third incident copy can be
placed in a perfect matching; both prescribed copies then lie in the
complement and are carried by the component rooted at their common vertex.
Thus any genuinely bad pair in a minimal counterexample is vertex-disjoint.
-/

/-- Two distinct copies incident with the same vertex admit an edge-pair
witness in every cubic matching-covered bipartite multigraph. -/
theorem IsMatchingCovered.edgePairWitness_of_common_vertex
    (hMC : G.IsMatchingCovered) (hG : G.IsCubic)
    {e f : E} (hef : e ≠ f) {r : X ⊕ Y}
    (her : G.Incident e r) (hfr : G.Incident f r) :
    G.EdgePairWitness e f := by
  classical
  let S : Finset E := {e, f}
  have hselected : G.selectedIncident S r = S := by
    ext g
    rw [G.mem_selectedIncident]
    constructor
    · exact fun h => h.1
    · intro hg
      refine ⟨hg, ?_⟩
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact her
      · exact hfr
  have hselectedCard : (G.selectedIncident S r).card = 2 := by
    rw [hselected]
    simp [S, hef]
  have hcomplCard : (G.selectedIncident Sᶜ r).card = 1 := by
    have h := G.selectedIncident_compl_card S r
    rw [hG r, hselectedCard] at h
    omega
  have hcomplPos : 0 < (G.selectedIncident Sᶜ r).card := by
    rw [hcomplCard]
    omega
  obtain ⟨g, hgSel⟩ := Finset.card_pos.mp hcomplPos
  have hgData := (G.mem_selectedIncident Sᶜ r g).1 hgSel
  have hgNot : g ∉ S := Finset.mem_compl.mp hgData.1
  have hge : e ≠ g := by
    intro h
    subst g
    exact hgNot (by simp [S])
  have hgf : f ≠ g := by
    intro h
    subst g
    exact hgNot (by simp [S])
  obtain ⟨P, hP, hgP⟩ := hMC.2.2 g
  have heNot : e ∉ P := by
    intro heP
    exact hge
      ((G.isMatching_iff P).1 hP.isMatching
        e heP g hgP r her hgData.2)
  have hfNot : f ∉ P := by
    intro hfP
    exact hgf
      ((G.isMatching_iff P).1 hP.isMatching
        f hfP g hgP r hfr hgData.2)
  exact ⟨P, r, hP,
    G.componentCarries_of_mem_of_incident (Finset.mem_compl.mpr heNot) her,
    G.componentCarries_of_mem_of_incident (Finset.mem_compl.mpr hfNot) hfr⟩

/-- A bad pair in a cubic matching-covered graph has distinct left endpoints. -/
theorem IsMatchingCovered.badPair_left_ne
    (hMC : G.IsMatchingCovered) (hG : G.IsCubic)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f) :
    G.left e ≠ G.left f := by
  intro hleft
  apply hbad
  exact hMC.edgePairWitness_of_common_vertex hG hef
    (r := .inl (G.left e)) rfl (by
      change G.left f = G.left e
      exact hleft.symm)

/-- A bad pair in a cubic matching-covered graph has distinct right endpoints. -/
theorem IsMatchingCovered.badPair_right_ne
    (hMC : G.IsMatchingCovered) (hG : G.IsCubic)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f) :
    G.right e ≠ G.right f := by
  intro hright
  apply hbad
  exact hMC.edgePairWitness_of_common_vertex hG hef
    (r := .inr (G.right e)) rfl (by
      change G.right f = G.right e
      exact hright.symm)

/-- Endpoint separation packaged for braces. -/
theorem IsBrace.badPair_endpoint_disjoint
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f) :
    G.left e ≠ G.left f ∧ G.right e ≠ G.right f :=
  ⟨hbrace.1.badPair_left_ne hG hef hbad,
    hbrace.1.badPair_right_ne hG hef hbad⟩

/-- In particular, any bad pair witnessing failure of EEP in a minimal
counterexample is vertex-disjoint. -/
theorem IsMinimalEEPCounterexample.badPair_endpoint_disjoint
    (hmin : G.IsMinimalEEPCounterexample)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f) :
    G.left e ≠ G.left f ∧ G.right e ≠ G.right f :=
  hmin.isBrace.badPair_endpoint_disjoint hmin.cubic hef hbad

/-- A minimal EEP counterexample admits a single bad pair exposing the two
local structural restrictions proved so far: its endpoint copies are disjoint,
and every displayed four-cycle contains exactly one member of the pair. -/
theorem IsMinimalEEPCounterexample.exists_structured_badPair
    (hmin : G.IsMinimalEEPCounterexample) :
    ∃ e f : E,
      e ≠ f ∧
      ¬ G.EdgePairWitness e f ∧
      G.left e ≠ G.left f ∧
      G.right e ≠ G.right f ∧
      ∀ Q : SquareFrame G,
        (¬ Q.OutsideSquare e ∧ Q.OutsideSquare f) ∨
          (Q.OutsideSquare e ∧ ¬ Q.OutsideSquare f) := by
  obtain ⟨e, f, hef, hbad⟩ := hmin.exists_badPair
  have hsep := hmin.badPair_endpoint_disjoint hef hbad
  refine ⟨e, f, hef, hbad, hsep.1, hsep.2, ?_⟩
  intro Q
  exact
    SquareFrame.IsMinimalEEPCounterexample.badPair_meets_square_exactly_one
      hmin Q hef hbad

end BipartiteMultigraph
end BachThesisLean
