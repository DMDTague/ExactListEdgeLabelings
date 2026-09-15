import BachThesisLean.Cubic.BraceTwoExtendable
import BachThesisLean.Cubic.MinimalEEPCounterexample

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Bad pairs on a square

The square-smoothing induction proves that a bad pair in a minimal
counterexample meets every displayed square.  The missing converse local fact
is that both marked copies cannot lie on one square.  Adjacent square copies
are joined in the complement of a matching through the third incident spoke.
For opposite square copies, 2-extendability forces one left spoke and the
opposite right spoke into a perfect matching; the remaining cross-square copy
then joins the two prescribed copies in the complementary two-factor.
-/

/-- In a perfect matching, a different edge incident with the same vertex as a
selected edge cannot also be selected. -/
theorem IsPerfectMatching.not_mem_of_mem_of_incident_ne
    {P : Finset E} (hP : G.IsPerfectMatching P)
    {chosen other : E} {v : X ⊕ Y}
    (hchosen : chosen ∈ P)
    (hchosenInc : G.Incident chosen v)
    (hotherInc : G.Incident other v)
    (hne : other ≠ chosen) : other ∉ P := by
  intro hother
  exact hne
    ((G.isMatching_iff P).1 hP.isMatching
      other hother chosen hchosen v hotherInc hchosenInc)

/-- Any two square copies in the same square row admit an edge-pair witness. -/
theorem IsBrace.edgePairWitness_square_same_left
    (hbrace : G.IsBrace) (Q : SquareFrame G)
    (i j k : Bool) :
    G.EdgePairWitness (Q.square i j) (Q.square i k) := by
  classical
  obtain ⟨P, hP, hspoke⟩ := hbrace.1.2.2 (Q.leftSpoke i)
  have hspokeInc : G.Incident (Q.leftSpoke i) (.inl (Q.leftVertex i)) := by
    change G.left (Q.leftSpoke i) = Q.leftVertex i
    exact Q.leftSpoke_left i
  have hjInc : G.Incident (Q.square i j) (.inl (Q.leftVertex i)) := by
    change G.left (Q.square i j) = Q.leftVertex i
    exact Q.square_left i j
  have hkInc : G.Incident (Q.square i k) (.inl (Q.leftVertex i)) := by
    change G.left (Q.square i k) = Q.leftVertex i
    exact Q.square_left i k
  have hjNot : Q.square i j ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hspoke hspokeInc hjInc (Q.square_ne_leftSpoke i j i)
  have hkNot : Q.square i k ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hspoke hspokeInc hkInc (Q.square_ne_leftSpoke i k i)
  have hjCompl : Q.square i j ∈ Pᶜ := Finset.mem_compl.mpr hjNot
  have hkCompl : Q.square i k ∈ Pᶜ := Finset.mem_compl.mpr hkNot
  exact ⟨P, .inl (Q.leftVertex i), hP,
    G.componentCarries_of_mem_of_incident hjCompl hjInc,
    G.componentCarries_of_mem_of_incident hkCompl hkInc⟩

/-- Any two square copies in the same square column admit an edge-pair witness. -/
theorem IsBrace.edgePairWitness_square_same_right
    (hbrace : G.IsBrace) (Q : SquareFrame G)
    (i k j : Bool) :
    G.EdgePairWitness (Q.square i j) (Q.square k j) := by
  classical
  obtain ⟨P, hP, hspoke⟩ := hbrace.1.2.2 (Q.rightSpoke j)
  have hspokeInc : G.Incident (Q.rightSpoke j) (.inr (Q.rightVertex j)) := by
    change G.right (Q.rightSpoke j) = Q.rightVertex j
    exact Q.rightSpoke_right j
  have hiInc : G.Incident (Q.square i j) (.inr (Q.rightVertex j)) := by
    change G.right (Q.square i j) = Q.rightVertex j
    exact Q.square_right i j
  have hkInc : G.Incident (Q.square k j) (.inr (Q.rightVertex j)) := by
    change G.right (Q.square k j) = Q.rightVertex j
    exact Q.square_right k j
  have hiNot : Q.square i j ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hspoke hspokeInc hiInc (Q.square_ne_rightSpoke i j j)
  have hkNot : Q.square k j ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hspoke hspokeInc hkInc (Q.square_ne_rightSpoke k j j)
  have hiCompl : Q.square i j ∈ Pᶜ := Finset.mem_compl.mpr hiNot
  have hkCompl : Q.square k j ∈ Pᶜ := Finset.mem_compl.mpr hkNot
  exact ⟨P, .inr (Q.rightVertex j), hP,
    G.componentCarries_of_mem_of_incident hiCompl hiInc,
    G.componentCarries_of_mem_of_incident hkCompl hkInc⟩

/-- Opposite square copies admit an edge-pair witness in a cubic brace.  Force
the left spoke at the first row and the right spoke at the opposite column;
the cross square copy remains in the complementary factor and joins the two
prescribed copies. -/
theorem IsBrace.edgePairWitness_square_opposite
    (hbrace : G.IsBrace) (hG : G.IsCubic) (Q : SquareFrame G)
    (i j : Bool) :
    G.EdgePairWitness (Q.square i j)
      (Q.square (squarePair true i) (squarePair true j)) := by
  classical
  let i' := squarePair true i
  let j' := squarePair true j
  have hleft : G.left (Q.leftSpoke i) ≠ G.left (Q.rightSpoke j') := by
    rw [Q.leftSpoke_left, Q.rightSpoke_left]
    exact (Q.externalLeft_ne j' i).symm
  have hright : G.right (Q.leftSpoke i) ≠ G.right (Q.rightSpoke j') := by
    rw [Q.leftSpoke_right, Q.rightSpoke_right]
    exact Q.externalRight_ne i j'
  obtain ⟨P, hP, hleftSpokeP, hrightSpokeP⟩ :=
    hbrace.exists_perfectMatching_containing_two_edges hG
      (Q.leftSpoke i) (Q.rightSpoke j') hleft hright
  have hleftSpokeInc :
      G.Incident (Q.leftSpoke i) (.inl (Q.leftVertex i)) := by
    change G.left (Q.leftSpoke i) = Q.leftVertex i
    exact Q.leftSpoke_left i
  have hrightSpokeInc :
      G.Incident (Q.rightSpoke j') (.inr (Q.rightVertex j')) := by
    change G.right (Q.rightSpoke j') = Q.rightVertex j'
    exact Q.rightSpoke_right j'
  have heInc : G.Incident (Q.square i j) (.inl (Q.leftVertex i)) := by
    change G.left (Q.square i j) = Q.leftVertex i
    exact Q.square_left i j
  have hfInc :
      G.Incident (Q.square i' j') (.inr (Q.rightVertex j')) := by
    change G.right (Q.square i' j') = Q.rightVertex j'
    exact Q.square_right i' j'
  have hcrossInc :
      G.Incident (Q.square i j') (.inl (Q.leftVertex i)) := by
    change G.left (Q.square i j') = Q.leftVertex i
    exact Q.square_left i j'
  have heNot : Q.square i j ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hleftSpokeP hleftSpokeInc heInc (Q.square_ne_leftSpoke i j i)
  have hfNot : Q.square i' j' ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hrightSpokeP hrightSpokeInc hfInc
      (Q.square_ne_rightSpoke i' j' j')
  have hcrossNot : Q.square i j' ∉ P :=
    SquareFrame.IsPerfectMatching.not_mem_of_mem_of_incident_ne
      hP hleftSpokeP hleftSpokeInc hcrossInc
      (Q.square_ne_leftSpoke i j' i)
  have heCompl : Q.square i j ∈ Pᶜ := Finset.mem_compl.mpr heNot
  have hfCompl : Q.square i' j' ∈ Pᶜ := Finset.mem_compl.mpr hfNot
  have hcrossCompl : Q.square i j' ∈ Pᶜ := Finset.mem_compl.mpr hcrossNot
  have hcrossReach :
      G.FactorReachable Pᶜ (.inl (Q.leftVertex i))
        (.inr (Q.rightVertex j')) := by
    simpa only [Q.square_left, Q.square_right] using
      G.factorReachable_endpoints hcrossCompl
  have hfReach :
      G.FactorReachable Pᶜ (.inl (Q.leftVertex i'))
        (.inr (Q.rightVertex j')) := by
    simpa only [Q.square_left, Q.square_right] using
      G.factorReachable_endpoints hfCompl
  have hrootToF :
      G.FactorReachable Pᶜ (.inl (Q.leftVertex i))
        (.inl (Q.leftVertex i')) :=
    hcrossReach.trans hfReach.symm
  refine ⟨P, .inl (Q.leftVertex i), hP,
    G.componentCarries_of_mem_of_incident heCompl heInc, ?_⟩
  refine ⟨hfCompl, ?_⟩
  simpa only [Q.square_left] using hrootToF

/-- Every pair of copies on one displayed square admits an edge-pair witness in
a cubic brace. -/
theorem IsBrace.edgePairWitness_square
    (hbrace : G.IsBrace) (hG : G.IsCubic) (Q : SquareFrame G)
    (i j k l : Bool) :
    G.EdgePairWitness (Q.square i j) (Q.square k l) := by
  by_cases hik : i = k
  · subst k
    exact SquareFrame.IsBrace.edgePairWitness_square_same_left hbrace Q i j l
  by_cases hjl : j = l
  · subst l
    exact SquareFrame.IsBrace.edgePairWitness_square_same_right hbrace Q i k j
  have hk : k = squarePair true i := by
    cases i <;> cases k <;> simp_all [squarePair]
  have hl : l = squarePair true j := by
    cases j <;> cases l <;> simp_all [squarePair]
  subst k
  subst l
  exact SquareFrame.IsBrace.edgePairWitness_square_opposite hbrace hG Q i j

/-- Not being outside the square is exactly being one of its four distinguished
square copies. -/
theorem not_outsideSquare_iff_exists_square (Q : SquareFrame G) (e : E) :
    ¬ Q.OutsideSquare e ↔ ∃ i j : Bool, e = Q.square i j := by
  constructor
  · intro h
    by_contra hex
    apply h
    intro i j heq
    apply hex
    exact ⟨i, j, heq⟩
  · rintro ⟨i, j, rfl⟩ hout
    exact hout i j rfl

/-- A bad edge pair in a cubic brace cannot have both marked copies on one
square. -/
theorem IsBrace.badPair_not_both_on_square
    (hbrace : G.IsBrace) (hG : G.IsCubic) (Q : SquareFrame G)
    {e f : E} (hbad : ¬ G.EdgePairWitness e f) :
    ¬ (¬ Q.OutsideSquare e ∧ ¬ Q.OutsideSquare f) := by
  rintro ⟨he, hf⟩
  obtain ⟨i, j, rfl⟩ := (Q.not_outsideSquare_iff_exists_square e).1 he
  obtain ⟨k, l, rfl⟩ := (Q.not_outsideSquare_iff_exists_square f).1 hf
  exact hbad
    (SquareFrame.IsBrace.edgePairWitness_square hbrace hG Q i j k l)

/-- Therefore, for a fixed bad pair in a minimum counterexample, every
displayed square contains exactly one member of the pair. -/
theorem IsMinimalEEPCounterexample.badPair_meets_square_exactly_one
    (hmin : G.IsMinimalEEPCounterexample) (Q : SquareFrame G)
    {e f : E} (hef : e ≠ f) (hbad : ¬ G.EdgePairWitness e f) :
    (¬ Q.OutsideSquare e ∧ Q.OutsideSquare f) ∨
      (Q.OutsideSquare e ∧ ¬ Q.OutsideSquare f) := by
  have hmeet := hmin.badPair_meets_square Q hef hbad
  have hnotBoth :=
    SquareFrame.IsBrace.badPair_not_both_on_square
      hmin.isBrace hmin.cubic Q hbad
  rcases hmeet with he | hf
  · left
    refine ⟨he, ?_⟩
    by_contra hf'
    exact hnotBoth ⟨he, hf'⟩
  · right
    refine ⟨?_, hf⟩
    by_contra he'
    exact hnotBoth ⟨he', hf⟩

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
