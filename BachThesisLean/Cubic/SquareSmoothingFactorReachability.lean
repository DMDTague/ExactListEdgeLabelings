import BachThesisLean.Cubic.SquareSmoothingFactor
import BachThesisLean.Cubic.FactorPathTransport

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Reachability through square-factor lifting

Each selected old smoothing copy is represented by the same old edge copy.
Each selected fresh smoothing copy is represented by a selected path through
the deleted square.  Thus factor reachability between surviving vertices lifts
without identifying any parallel edge copies.
-/

/-- Embed a surviving smoothing vertex back into the original vertex type. -/
def liftVertex : Q.ReducedLeft ⊕ Q.ReducedRight → X ⊕ Y
  | .inl x => .inl x.val
  | .inr y => .inr y.val

@[simp] theorem liftVertex_inl (x : Q.ReducedLeft) :
    Q.liftVertex (.inl x) = (.inl x.val : X ⊕ Y) := rfl

@[simp] theorem liftVertex_inr (y : Q.ReducedRight) :
    Q.liftVertex (.inr y) = (.inr y.val : X ⊕ Y) := rfl

@[simp] theorem squarePair_true_ne (i : Bool) : squarePair true i ≠ i := by
  cases i <;> simp [squarePair]

@[simp] theorem squarePair_comm_true (swap i : Bool) :
    squarePair swap (squarePair true i) =
      squarePair true (squarePair swap i) := by
  cases swap <;> cases i <;> rfl

@[simp] theorem squarePair_cross_ne (swap i : Bool) :
    squarePair swap i ≠ squarePair swap (squarePair true i) := by
  intro h
  have h' := squarePair_injective swap h
  exact squarePair_true_ne i h'.symm

/-- If the other fresh copy is absent, the two fresh copies are not both
selected. -/
theorem not_both_fresh_of_other_not
    (S : Finset Q.SmoothEdge) (i : Bool)
    (hother : ¬ Q.freshSelected S (squarePair true i)) :
    ¬ (Q.freshSelected S false ∧ Q.freshSelected S true) := by
  intro h
  cases i with
  | false =>
      exact hother (by simpa [squarePair] using h.2)
  | true =>
      exact hother (by simpa [squarePair] using h.1)

/-- When both fresh copies are selected, the directly paired square copy is
selected. -/
theorem squareSelected_paired_of_both
    (swap : Bool) (S : Finset Q.SmoothEdge) (i : Bool)
    (hi : Q.freshSelected S i)
    (hother : Q.freshSelected S (squarePair true i)) :
    Q.squareSelected swap S (squarePair swap i) i := by
  unfold squareSelected
  rw [if_pos rfl]
  intro _
  exact hother

/-- With only fresh copy `i` selected, the square edge from the other left
vertex to right vertex `i` is selected. -/
theorem squareSelected_first_of_other_not
    (swap : Bool) (S : Finset Q.SmoothEdge) (i : Bool)
    (hother : ¬ Q.freshSelected S (squarePair true i)) :
    Q.squareSelected swap S
      (squarePair true (squarePair swap i)) i := by
  unfold squareSelected
  rw [if_neg (squarePair_true_ne (squarePair swap i))]
  exact Q.not_both_fresh_of_other_not S i hother

/-- With only fresh copy `i` selected, the middle square edge of its long
replacement path is selected. -/
theorem squareSelected_middle_of_other_not
    (swap : Bool) (S : Finset Q.SmoothEdge) (i : Bool)
    (hother : ¬ Q.freshSelected S (squarePair true i)) :
    Q.squareSelected swap S
      (squarePair true (squarePair swap i)) (squarePair true i) := by
  unfold squareSelected
  rw [if_pos (squarePair_comm_true swap i).symm]
  intro h
  exact False.elim (hother h)

/-- With only fresh copy `i` selected, the final square edge of its long
replacement path is selected. -/
theorem squareSelected_last_of_other_not
    (swap : Bool) (S : Finset Q.SmoothEdge) (i : Bool)
    (hother : ¬ Q.freshSelected S (squarePair true i)) :
    Q.squareSelected swap S
      (squarePair swap i) (squarePair true i) := by
  unfold squareSelected
  rw [if_neg (squarePair_cross_ne swap i)]
  exact Q.not_both_fresh_of_other_not S i hother

/-- A selected fresh smoothing copy expands to a selected path between the
same two surviving endpoints.  If the other fresh copy is selected the path
has three edges; otherwise it traverses all four square vertices and has five
edges. -/
theorem freshReplacement_reachable
    (swap : Bool) (S : Finset Q.SmoothEdge) (i : Bool)
    (hi : Q.freshSelected S i) :
    G.FactorReachable (Q.liftFactor swap S)
      (.inl (Q.externalLeft i))
      (.inr (Q.externalRight (squarePair swap i))) := by
  have hrMem : Q.rightSpoke i ∈ Q.liftFactor swap S :=
    (Q.mem_liftFactor_rightSpoke swap i S).2 hi
  have hr :
      G.FactorReachable (Q.liftFactor swap S)
        (.inl (Q.externalLeft i)) (.inr (Q.rightVertex i)) := by
    simpa only [Q.rightSpoke_left, Q.rightSpoke_right] using
      (G.factorReachable_endpoints hrMem)
  have hlMem : Q.leftSpoke (squarePair swap i) ∈ Q.liftFactor swap S :=
    (Q.mem_liftFactor_leftSpoke_paired swap i S).2 hi
  have hl :
      G.FactorReachable (Q.liftFactor swap S)
        (.inl (Q.leftVertex (squarePair swap i)))
        (.inr (Q.externalRight (squarePair swap i))) := by
    simpa only [Q.leftSpoke_left, Q.leftSpoke_right] using
      (G.factorReachable_endpoints hlMem)
  by_cases hother : Q.freshSelected S (squarePair true i)
  · have hsMem :
        Q.square (squarePair swap i) i ∈ Q.liftFactor swap S :=
      (Q.mem_liftFactor_square swap (squarePair swap i) i S).2
        (Q.squareSelected_paired_of_both swap S i hi hother)
    have hs :
        G.FactorReachable (Q.liftFactor swap S)
          (.inr (Q.rightVertex i))
          (.inl (Q.leftVertex (squarePair swap i))) := by
      simpa only [Q.square_left, Q.square_right] using
        (G.factorReachable_endpoints hsMem).symm
    exact hr.trans (hs.trans hl)
  · have hFirstMem :
        Q.square (squarePair true (squarePair swap i)) i ∈
          Q.liftFactor swap S :=
      (Q.mem_liftFactor_square swap
        (squarePair true (squarePair swap i)) i S).2
        (Q.squareSelected_first_of_other_not swap S i hother)
    have hFirst :
        G.FactorReachable (Q.liftFactor swap S)
          (.inr (Q.rightVertex i))
          (.inl (Q.leftVertex (squarePair true (squarePair swap i)))) := by
      simpa only [Q.square_left, Q.square_right] using
        (G.factorReachable_endpoints hFirstMem).symm
    have hMiddleMem :
        Q.square (squarePair true (squarePair swap i)) (squarePair true i) ∈
          Q.liftFactor swap S :=
      (Q.mem_liftFactor_square swap
        (squarePair true (squarePair swap i)) (squarePair true i) S).2
        (Q.squareSelected_middle_of_other_not swap S i hother)
    have hMiddle :
        G.FactorReachable (Q.liftFactor swap S)
          (.inl (Q.leftVertex (squarePair true (squarePair swap i))))
          (.inr (Q.rightVertex (squarePair true i))) := by
      simpa only [Q.square_left, Q.square_right] using
        (G.factorReachable_endpoints hMiddleMem)
    have hLastMem :
        Q.square (squarePair swap i) (squarePair true i) ∈
          Q.liftFactor swap S :=
      (Q.mem_liftFactor_square swap
        (squarePair swap i) (squarePair true i) S).2
        (Q.squareSelected_last_of_other_not swap S i hother)
    have hLast :
        G.FactorReachable (Q.liftFactor swap S)
          (.inr (Q.rightVertex (squarePair true i)))
          (.inl (Q.leftVertex (squarePair swap i))) := by
      simpa only [Q.square_left, Q.square_right] using
        (G.factorReachable_endpoints hLastMem).symm
    exact hr.trans (hFirst.trans (hMiddle.trans (hLast.trans hl)))

/-- Every selected smoothing edge has a selected replacement path between the
embedded endpoints. -/
theorem selectedSmoothEdge_reachable
    (swap : Bool) (S : Finset Q.SmoothEdge)
    (e : Q.SmoothEdge) (he : e ∈ S) :
    G.FactorReachable (Q.liftFactor swap S)
      (Q.liftVertex (.inl ((Q.smooth swap).left e)))
      (Q.liftVertex (.inr ((Q.smooth swap).right e))) := by
  cases e with
  | inl e =>
      have hmem : e.val ∈ Q.liftFactor swap S :=
        (Q.mem_liftFactor_old swap S e).2 he
      simpa only [liftVertex_inl, liftVertex_inr, smooth_left_old,
        smooth_right_old] using G.factorReachable_endpoints hmem
  | inr i =>
      have hi : Q.freshSelected S i := by
        simpa [freshSelected] using he
      simpa only [liftVertex_inl, liftVertex_inr, smooth_left_fresh,
        smooth_right_fresh] using Q.freshReplacement_reachable swap S i hi

/-- Reachability in a smoothing factor lifts between the corresponding
surviving vertices of the original graph. -/
theorem factorReachable_lift
    (swap : Bool) (S : Finset Q.SmoothEdge)
    {a b : Q.ReducedLeft ⊕ Q.ReducedRight}
    (h : (Q.smooth swap).FactorReachable S a b) :
    G.FactorReachable (Q.liftFactor swap S) (Q.liftVertex a) (Q.liftVertex b) := by
  apply FactorReachable.of_edge_paths Q.liftVertex ?_ h
  intro u v huv
  rcases huv with ⟨e, he, hdir | hdir⟩
  · rcases hdir with ⟨rfl, rfl⟩
    exact Q.selectedSmoothEdge_reachable swap S e he
  · rcases hdir with ⟨rfl, rfl⟩
    exact (Q.selectedSmoothEdge_reachable swap S e he).symm

/-- A component carrying an old survivor copy in the smoothing carries the
same original edge copy after lifting. -/
theorem componentCarries_lift_old
    (swap : Bool) (S : Finset Q.SmoothEdge)
    {root : Q.ReducedLeft ⊕ Q.ReducedRight} (e : Q.Survivor)
    (h : (Q.smooth swap).ComponentCarries S root (.inl e)) :
    G.ComponentCarries (Q.liftFactor swap S) (Q.liftVertex root) e.val := by
  refine ⟨(Q.mem_liftFactor_old swap S e).2 h.1, ?_⟩
  have hr := Q.factorReachable_lift swap S h.2
  simpa only [liftVertex_inl, smooth_left_old] using hr

/-- A component carrying fresh smoothing copy `i` carries its original right
spoke after lifting. -/
theorem componentCarries_lift_fresh_rightSpoke
    (swap : Bool) (S : Finset Q.SmoothEdge)
    {root : Q.ReducedLeft ⊕ Q.ReducedRight} (i : Bool)
    (h : (Q.smooth swap).ComponentCarries S root (.inr i)) :
    G.ComponentCarries (Q.liftFactor swap S) (Q.liftVertex root)
      (Q.rightSpoke i) := by
  have hi : Q.freshSelected S i := by
    simpa [freshSelected] using h.1
  refine ⟨(Q.mem_liftFactor_rightSpoke swap i S).2 hi, ?_⟩
  have hr := Q.factorReachable_lift swap S h.2
  simpa only [liftVertex_inl, smooth_left_fresh, Q.rightSpoke_left] using hr

/-- The same lifted component also carries the original left spoke paired with
fresh copy `i`. -/
theorem componentCarries_lift_fresh_leftSpoke
    (swap : Bool) (S : Finset Q.SmoothEdge)
    {root : Q.ReducedLeft ⊕ Q.ReducedRight} (i : Bool)
    (h : (Q.smooth swap).ComponentCarries S root (.inr i)) :
    G.ComponentCarries (Q.liftFactor swap S) (Q.liftVertex root)
      (Q.leftSpoke (squarePair swap i)) := by
  have hi : Q.freshSelected S i := by
    simpa [freshSelected] using h.1
  have hlMem : Q.leftSpoke (squarePair swap i) ∈ Q.liftFactor swap S :=
    (Q.mem_liftFactor_leftSpoke_paired swap i S).2 hi
  refine ⟨hlMem, ?_⟩
  have hroot := Q.factorReachable_lift swap S h.2
  have hpath := Q.freshReplacement_reachable swap S i hi
  have hspoke :
      G.FactorReachable (Q.liftFactor swap S)
        (.inr (Q.externalRight (squarePair swap i)))
        (.inl (Q.leftVertex (squarePair swap i))) := by
    simpa only [Q.leftSpoke_left, Q.leftSpoke_right] using
      (G.factorReachable_endpoints hlMem).symm
  have hroot' :
      G.FactorReachable (Q.liftFactor swap S) (Q.liftVertex root)
        (.inl (Q.externalLeft i)) := by
    simpa only [liftVertex_inl, smooth_left_fresh] using hroot
  simpa only [Q.leftSpoke_left] using hroot'.trans (hpath.trans hspoke)

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
