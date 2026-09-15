import BachThesisLean.Cubic.SquareSmoothingPfaffianFactor
import BachThesisLean.Cubic.Isomorphism

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Identifying the two-step odd-path smoothing with square smoothing

The two successive odd-path smoothings delete exactly the four square vertices.
At the edge-copy level, an old copy survives both stages exactly when it is an
ordinary square-smoothing survivor.  The first and second fresh odd-path copies
will subsequently become the two `Bool`-tagged fresh square-smoothing copies.
-/

/-- An original edge copy that survives both odd-path smoothing stages is an
ordinary survivor of the square smoothing. -/
theorem survives_after_pairing_two_smoothings
    (swap : Bool)
    (b : (Q.firstPairingOddPathFrame swap).Survivor)
    (hsecond :
      (Q.secondPairingOddPathFrame swap).Survives
        ((Q.firstPairingOddPathFrame swap).oldEdge b)) :
    Q.Survives b.val.val := by
  let F := Q.firstPairingOddPathFrame swap
  let S := Q.secondPairingOddPathFrame swap
  let j0 : Bool := squarePair swap false
  let j1 : Bool := squarePair swap true
  have hL0 := b.property.1
  change G.left b.val.val ≠ Q.leftVertex j0 at hL0
  have hR0 := b.property.2
  change G.right b.val.val ≠ Q.rightVertex false at hR0
  have hL1 : G.left b.val.val ≠ Q.leftVertex j1 := by
    intro h
    apply hsecond.1
    apply Subtype.ext
    exact h
  have hR1 : G.right b.val.val ≠ Q.rightVertex true := by
    intro h
    apply hsecond.2
    apply Subtype.ext
    exact h
  have hcover : ∀ i : Bool, i = j0 ∨ i = j1 := by
    intro i
    cases swap <;> cases i <;> simp [j0, j1, squarePair]
  have hleft : ∀ i : Bool, G.left b.val.val ≠ Q.leftVertex i := by
    intro i hi
    rcases hcover i with rfl | rfl
    · exact hL0 hi
    · exact hL1 hi
  have hright : ∀ i : Bool, G.right b.val.val ≠ Q.rightVertex i := by
    intro i
    cases i with
    | false => exact hR0
    | true => exact hR1
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    apply hleft i
    exact (congrArg G.left h).trans (Q.square_left i j)
  · intro i h
    apply hleft i
    exact (congrArg G.left h).trans (Q.leftSpoke_left i)
  · intro i h
    apply hright i
    exact (congrArg G.right h).trans (Q.rightSpoke_right i)

/-- The nested left subtype obtained by the two odd-path smoothings is exactly
the square-smoothing left shore. -/
noncomputable def twoStepLeftEquiv (swap : Bool) :
    (Q.secondPairingOddPathFrame swap).ReducedLeft ≃ Q.ReducedLeft := by
  classical
  let F := Q.firstPairingOddPathFrame swap
  let S := Q.secondPairingOddPathFrame swap
  let j0 : Bool := squarePair swap false
  let j1 : Bool := squarePair swap true
  have hcover : ∀ i : Bool, i = j0 ∨ i = j1 := by
    intro i
    cases swap <;> cases i <;> simp [j0, j1, squarePair]
  refine
    { toFun := fun x => ⟨x.val.val, ?_⟩
      invFun := fun x =>
        ⟨⟨x.val, x.property j0⟩, by
          intro h
          exact x.property j1 (congrArg Subtype.val h)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i hi
    rcases hcover i with rfl | rfl
    · have h := x.val.property
      change x.val.val ≠ Q.leftVertex j0 at h
      exact h hi
    · apply x.property
      apply Subtype.ext
      exact hi
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    rfl

/-- The nested right subtype obtained by the two odd-path smoothings is exactly
the square-smoothing right shore. -/
noncomputable def twoStepRightEquiv (swap : Bool) :
    (Q.secondPairingOddPathFrame swap).ReducedRight ≃ Q.ReducedRight := by
  classical
  let F := Q.firstPairingOddPathFrame swap
  let S := Q.secondPairingOddPathFrame swap
  refine
    { toFun := fun y => ⟨y.val.val, ?_⟩
      invFun := fun y =>
        ⟨⟨y.val, y.property false⟩, by
          intro h
          exact y.property true (congrArg Subtype.val h)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i hi
    cases i with
    | false =>
        have h := y.val.property
        change y.val.val ≠ Q.rightVertex false at h
        exact h hi
    | true =>
        apply y.property
        apply Subtype.ext
        exact hi
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    rfl

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
