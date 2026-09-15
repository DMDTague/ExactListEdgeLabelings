import BachThesisLean.Cubic.DeletionConnectivity
import BachThesisLean.Cubic.SquareSmoothingConnectivity

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Connectivity of square smoothings from a cut lower bound

The four square vertices have only the four displayed spokes on their external
boundary.  Consequently a global lower bound of three on every proper
nonempty edge cut implies that deleting the square leaves a connected
surviving core: a disconnected deletion would need two disjoint cuts of size
at least three inside a boundary of size at most four.
-/

/-- The four vertices of the displayed square. -/
noncomputable def squareVertices : Finset (X ⊕ Y) := by
  classical
  exact Finset.univ.filter fun v =>
    match v with
    | .inl x => ∃ i : Bool, x = Q.leftVertex i
    | .inr y => ∃ i : Bool, y = Q.rightVertex i

@[simp] theorem mem_squareVertices_inl (x : X) :
    (Sum.inl x : X ⊕ Y) ∈ Q.squareVertices ↔
      ∃ i : Bool, x = Q.leftVertex i := by
  classical
  simp [squareVertices]

@[simp] theorem mem_squareVertices_inr (y : Y) :
    (Sum.inr y : X ⊕ Y) ∈ Q.squareVertices ↔
      ∃ i : Bool, y = Q.rightVertex i := by
  classical
  simp [squareVertices]

/-- Every reduced vertex really lies outside the deleted square. -/
theorem liftVertex_not_mem_squareVertices
    (v : Q.ReducedLeft ⊕ Q.ReducedRight) :
    Q.liftVertex v ∉ Q.squareVertices := by
  cases v with
  | inl x =>
      rw [Q.liftVertex_inl, Q.mem_squareVertices_inl]
      intro h
      obtain ⟨i, hi⟩ := h
      exact x.property i hi
  | inr y =>
      rw [Q.liftVertex_inr, Q.mem_squareVertices_inr]
      intro h
      obtain ⟨i, hi⟩ := h
      exact y.property i hi

/-- Avoiding the four deleted square vertices is exactly the previously defined
survivor condition on old edge copies. -/
theorem edgesAvoidingVertices_squareVertices_eq_survivorEdges :
    G.edgesAvoidingVertices Q.squareVertices = Q.survivorEdges := by
  classical
  ext e
  rw [G.mem_edgesAvoidingVertices, Q.mem_survivorEdges]
  constructor
  · intro hav
    have hleft : ∀ i : Bool, G.left e ≠ Q.leftVertex i := by
      intro i hi
      apply hav.1
      exact (Q.mem_squareVertices_inl (G.left e)).2 ⟨i, hi⟩
    have hright : ∀ i : Bool, G.right e ≠ Q.rightVertex i := by
      intro i hi
      apply hav.2
      exact (Q.mem_squareVertices_inr (G.right e)).2 ⟨i, hi⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      apply hleft i
      rw [hij]
      exact Q.square_left i j
    · intro i hi
      apply hleft i
      rw [hi]
      exact Q.leftSpoke_left i
    · intro i hi
      apply hright i
      rw [hi]
      exact Q.rightSpoke_right i
  · intro hs
    let es : Q.Survivor := ⟨e, hs⟩
    constructor
    · intro hmem
      rw [Q.mem_squareVertices_inl] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact Q.survivor_left_ne es i hi
    · intro hmem
      rw [Q.mem_squareVertices_inr] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact Q.survivor_right_ne es i hi

/-- The four displayed spoke copies, with no quotienting of parallel copies. -/
noncomputable def spokeEdges : Finset E := by
  classical
  exact (Finset.univ.image Q.leftSpoke) ∪
    (Finset.univ.image Q.rightSpoke)

/-- Every boundary copy of the square is one of the four displayed spokes. -/
theorem edgeCut_squareVertices_subset_spokeEdges :
    G.edgeCut Q.squareVertices ⊆ Q.spokeEdges := by
  classical
  intro e he
  have hcut :
      ((Sum.inl (G.left e) : X ⊕ Y) ∈ Q.squareVertices ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∉ Q.squareVertices) ∨
      ((Sum.inl (G.left e) : X ⊕ Y) ∉ Q.squareVertices ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∈ Q.squareVertices) := by
    simpa only [edgeCut, Finset.mem_filter, Finset.mem_univ, true_and] using he
  rcases hcut with hLR | hRL
  · rw [Q.mem_squareVertices_inl] at hLR
    obtain ⟨i, hi⟩ := hLR.1
    rcases Q.left_saturated e i hi with hs | hs | hs
    · exfalso
      apply hLR.2
      exact (Q.mem_squareVertices_inr (G.right e)).2
        ⟨false, by rw [hs]; exact Q.square_right i false⟩
    · exfalso
      apply hLR.2
      exact (Q.mem_squareVertices_inr (G.right e)).2
        ⟨true, by rw [hs]; exact Q.square_right i true⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ i, hs.symm⟩
  · rw [Q.mem_squareVertices_inr] at hRL
    obtain ⟨j, hj⟩ := hRL.2
    rcases Q.right_saturated e j hj with hs | hs | hs
    · exfalso
      apply hRL.1
      exact (Q.mem_squareVertices_inl (G.left e)).2
        ⟨false, by rw [hs]; exact Q.square_left false j⟩
    · exfalso
      apply hRL.1
      exact (Q.mem_squareVertices_inl (G.left e)).2
        ⟨true, by rw [hs]; exact Q.square_left true j⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨j, Finset.mem_univ j, hs.symm⟩

/-- The boundary of the deleted square has at most four edge copies. -/
theorem edgeCut_squareVertices_card_le_four :
    (G.edgeCut Q.squareVertices).card ≤ 4 := by
  classical
  have hcut : (G.edgeCut Q.squareVertices).card ≤ Q.spokeEdges.card :=
    Finset.card_le_card Q.edgeCut_squareVertices_subset_spokeEdges
  have hL : ((Finset.univ : Finset Bool).image Q.leftSpoke).card ≤ 2 := by
    calc
      ((Finset.univ : Finset Bool).image Q.leftSpoke).card ≤
          (Finset.univ : Finset Bool).card := Finset.card_image_le
      _ = 2 := by decide
  have hR : ((Finset.univ : Finset Bool).image Q.rightSpoke).card ≤ 2 := by
    calc
      ((Finset.univ : Finset Bool).image Q.rightSpoke).card ≤
          (Finset.univ : Finset Bool).card := Finset.card_image_le
      _ = 2 := by decide
  have hspokes : Q.spokeEdges.card ≤ 4 := by
    calc
      Q.spokeEdges.card ≤
          ((Finset.univ : Finset Bool).image Q.leftSpoke).card +
            ((Finset.univ : Finset Bool).image Q.rightSpoke).card := by
              simpa [spokeEdges] using
                Finset.card_union_le
                  ((Finset.univ : Finset Bool).image Q.leftSpoke)
                  ((Finset.univ : Finset Bool).image Q.rightSpoke)
      _ ≤ 2 + 2 := Nat.add_le_add hL hR
      _ = 4 := by decide
  exact hcut.trans hspokes

/-- In particular the four-square boundary is strictly smaller than twice a
three-edge global cut lower bound. -/
theorem edgeCut_squareVertices_card_lt_six :
    (G.edgeCut Q.squareVertices).card < 2 * 3 := by
  have h := Q.edgeCut_squareVertices_card_le_four
  omega

/-- A global three-edge cut lower bound makes the old surviving core connected. -/
theorem survivorCoreConnected_of_minCut_three
    (hmin : ∀ W : Finset (X ⊕ Y), W.Nonempty → Wᶜ.Nonempty →
      3 ≤ (G.edgeCut W).card) :
    Q.SurvivorCoreConnected := by
  intro a b
  have ha : Q.liftVertex a ∉ Q.squareVertices :=
    Q.liftVertex_not_mem_squareVertices a
  have hb : Q.liftVertex b ∉ Q.squareVertices :=
    Q.liftVertex_not_mem_squareVertices b
  have hreach :=
    G.factorReachable_edgesAvoidingVertices_of_boundary_lt_twice_minCut
      Q.squareVertices 3 hmin Q.edgeCut_squareVertices_card_lt_six ha hb
  rw [Q.edgesAvoidingVertices_squareVertices_eq_survivorEdges] at hreach
  exact hreach

/-- Hence each of the two terminal pairings is connected under the same global
three-edge cut lower bound. -/
theorem smooth_isConnected_of_minCut_three
    (hmin : ∀ W : Finset (X ⊕ Y), W.Nonempty → Wᶜ.Nonempty →
      3 ≤ (G.edgeCut W).card)
    (swap : Bool) :
    (Q.smooth swap).IsConnected :=
  Q.smooth_isConnected_of_survivorCoreConnected
    (Q.survivorCoreConnected_of_minCut_three hmin) swap

/-- Both square smoothings are connected under a global cut lower bound of
three edge copies. -/
theorem both_smoothings_connected_of_minCut_three
    (hmin : ∀ W : Finset (X ⊕ Y), W.Nonempty → Wᶜ.Nonempty →
      3 ≤ (G.edgeCut W).card) :
    (Q.smooth false).IsConnected ∧ (Q.smooth true).IsConnected :=
  Q.both_smoothings_connected_of_survivorCoreConnected
    (Q.survivorCoreConnected_of_minCut_three hmin)

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
