import BachThesisLean.Cubic.SquareSmoothingFactorLift
import BachThesisLean.Cubic.SquareSmoothingFactorReachability

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Prescribed-edge witnesses across square smoothing

A perfect matching witness in a cubic smoothing is first viewed through its
complementary two-factor.  The two-factor is lifted through the square, and
complementation in the original cubic graph supplies the required perfect
matching.  Component transport is delegated to the explicit replacement-path
lemmas.
-/

/-- Generic witness lifting once the two marked smoothing copies have supplied
component-lifting maps to the two prescribed original copies. -/
theorem edgePairWitness_lift
    (hG : G.IsCubic) (swap : Bool)
    {a b : Q.SmoothEdge} {e f : E}
    (h : (Q.smooth swap).EdgePairWitness a b)
    (ha : ∀ {S : Finset Q.SmoothEdge}
      {root : Q.ReducedLeft ⊕ Q.ReducedRight},
      (Q.smooth swap).ComponentCarries S root a →
        G.ComponentCarries (Q.liftFactor swap S) (Q.liftVertex root) e)
    (hb : ∀ {S : Finset Q.SmoothEdge}
      {root : Q.ReducedLeft ⊕ Q.ReducedRight},
      (Q.smooth swap).ComponentCarries S root b →
        G.ComponentCarries (Q.liftFactor swap S) (Q.liftVertex root) f) :
    G.EdgePairWitness e f := by
  rcases h with ⟨P, root, hP, hA, hB⟩
  let F : Finset E := Q.liftFactor swap Pᶜ
  have hSmoothCubic : (Q.smooth swap).IsCubic := Q.smooth_isCubic hG swap
  have hTwoSmooth : (Q.smooth swap).IsTwoFactor Pᶜ :=
    ((Q.smooth swap).perfectMatching_compl_iff_twoFactor hSmoothCubic P).1 hP
  have hTwoLift : G.IsTwoFactor F := by
    dsimp [F]
    exact Q.liftFactor_isTwoFactor swap hTwoSmooth
  have hMatch : G.IsPerfectMatching Fᶜ := by
    apply (G.perfectMatching_compl_iff_twoFactor hG Fᶜ).2
    simpa using hTwoLift
  refine ⟨Fᶜ, Q.liftVertex root, hMatch, ?_, ?_⟩
  · simpa [F] using ha hA
  · simpa [F] using hb hB

/-- A left spoke is represented by the fresh copy whose paired right endpoint
is its external right endpoint. -/
theorem componentCarries_lift_leftSpoke
    (swap : Bool) (S : Finset Q.SmoothEdge)
    {root : Q.ReducedLeft ⊕ Q.ReducedRight} (i : Bool)
    (h : (Q.smooth swap).ComponentCarries S root
      (.inr (squarePair swap i))) :
    G.ComponentCarries (Q.liftFactor swap S) (Q.liftVertex root)
      (Q.leftSpoke i) := by
  simpa using
    (Q.componentCarries_lift_fresh_leftSpoke swap S (squarePair swap i) h)

/-- Two distinct old survivor copies remain distinct in every smoothing. -/
theorem oldRepresentatives_ne
    (e f : Q.Survivor) (hef : e.val ≠ f.val) :
    (Sum.inl e : Q.SmoothEdge) ≠ Sum.inl f := by
  intro h
  have h' : e = f := Sum.inl.inj h
  exact hef (congrArg Subtype.val h')

/-- Distinct Boolean spoke indices remain distinct as tagged fresh copies. -/
theorem freshRepresentatives_ne {i j : Bool} (hij : i ≠ j) :
    (Sum.inr i : Q.SmoothEdge) ≠ Sum.inr j := by
  intro h
  exact hij (Sum.inr.inj h)

/-- For any two distinct marked copies outside the square, one of the two
smoothings has distinct representatives and an EEP witness there lifts to an
EEP witness for the original marked copies. -/
theorem edgePairWitness_of_both_smoothings
    (hG : G.IsCubic)
    (hFalse : (Q.smooth false).HasEEP)
    (hTrue : (Q.smooth true).HasEEP)
    {e f : E} (heOut : Q.OutsideSquare e) (hfOut : Q.OutsideSquare f)
    (hef : e ≠ f) :
    G.EdgePairWitness e f := by
  rcases Q.outsideSquare_cases heOut with he | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rcases Q.outsideSquare_cases hfOut with hf | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · let ee : Q.Survivor := ⟨e, he⟩
      let ff : Q.Survivor := ⟨f, hf⟩
      have hne : (Sum.inl ee : Q.SmoothEdge) ≠ Sum.inl ff :=
        Q.oldRepresentatives_ne ee ff hef
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_old false _ ee h)
        (fun h => Q.componentCarries_lift_old false _ ff h)
    · let ee : Q.Survivor := ⟨e, he⟩
      have hne : (Sum.inl ee : Q.SmoothEdge) ≠
          (Sum.inr (squarePair false j) : Q.SmoothEdge) := by
        intro h
        cases h
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_old false _ ee h)
        (fun h => Q.componentCarries_lift_leftSpoke false _ j h)
    · let ee : Q.Survivor := ⟨e, he⟩
      have hne : (Sum.inl ee : Q.SmoothEdge) ≠ (Sum.inr j : Q.SmoothEdge) := by
        intro h
        cases h
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_old false _ ee h)
        (fun h => Q.componentCarries_lift_fresh_rightSpoke false _ j h)
  · rcases Q.outsideSquare_cases hfOut with hf | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · let ff : Q.Survivor := ⟨f, hf⟩
      have hne : (Sum.inr (squarePair false i) : Q.SmoothEdge) ≠ Sum.inl ff := by
        intro h
        cases h
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_leftSpoke false _ i h)
        (fun h => Q.componentCarries_lift_old false _ ff h)
    · have hij : i ≠ j := by
        intro hij
        subst j
        exact hef rfl
      have hne : (Sum.inr (squarePair false i) : Q.SmoothEdge) ≠
          Sum.inr (squarePair false j) := by
        intro h
        apply hij
        exact squarePair_injective false (Sum.inr.inj h)
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_leftSpoke false _ i h)
        (fun h => Q.componentCarries_lift_leftSpoke false _ j h)
    · by_cases hij : i = j
      · subst j
        have hne : (Sum.inr (squarePair true i) : Q.SmoothEdge) ≠ Sum.inr i := by
          exact Q.freshRepresentatives_ne (squarePair_true_ne i)
        have hw := hTrue.edgePairWitness hne
        exact Q.edgePairWitness_lift hG true hw
          (fun h => Q.componentCarries_lift_leftSpoke true _ i h)
          (fun h => Q.componentCarries_lift_fresh_rightSpoke true _ i h)
      · have hne : (Sum.inr (squarePair false i) : Q.SmoothEdge) ≠ Sum.inr j := by
          have hij' : squarePair false i ≠ j := by simpa using hij
          exact Q.freshRepresentatives_ne hij'
        have hw := hFalse.edgePairWitness hne
        exact Q.edgePairWitness_lift hG false hw
          (fun h => Q.componentCarries_lift_leftSpoke false _ i h)
          (fun h => Q.componentCarries_lift_fresh_rightSpoke false _ j h)
  · rcases Q.outsideSquare_cases hfOut with hf | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · let ff : Q.Survivor := ⟨f, hf⟩
      have hne : (Sum.inr i : Q.SmoothEdge) ≠ Sum.inl ff := by
        intro h
        cases h
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_fresh_rightSpoke false _ i h)
        (fun h => Q.componentCarries_lift_old false _ ff h)
    · by_cases hij : i = j
      · subst j
        have hne : (Sum.inr i : Q.SmoothEdge) ≠
            Sum.inr (squarePair true i) := by
          exact Q.freshRepresentatives_ne (squarePair_true_ne i).symm
        have hw := hTrue.edgePairWitness hne
        exact Q.edgePairWitness_lift hG true hw
          (fun h => Q.componentCarries_lift_fresh_rightSpoke true _ i h)
          (fun h => Q.componentCarries_lift_leftSpoke true _ i h)
      · have hne : (Sum.inr i : Q.SmoothEdge) ≠
            Sum.inr (squarePair false j) := by
          have hij' : i ≠ squarePair false j := by simpa using hij
          exact Q.freshRepresentatives_ne hij'
        have hw := hFalse.edgePairWitness hne
        exact Q.edgePairWitness_lift hG false hw
          (fun h => Q.componentCarries_lift_fresh_rightSpoke false _ i h)
          (fun h => Q.componentCarries_lift_leftSpoke false _ j h)
    · have hij : i ≠ j := by
        intro hij
        subst j
        exact hef rfl
      have hne : (Sum.inr i : Q.SmoothEdge) ≠ Sum.inr j :=
        Q.freshRepresentatives_ne hij
      have hw := hFalse.edgePairWitness hne
      exact Q.edgePairWitness_lift hG false hw
        (fun h => Q.componentCarries_lift_fresh_rightSpoke false _ i h)
        (fun h => Q.componentCarries_lift_fresh_rightSpoke false _ j h)

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
