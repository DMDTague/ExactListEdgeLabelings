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
# Connectivity of square smoothings from the surviving core

The difficult graph-theoretic input for square smoothing is precisely that the
graph left after deleting the square vertices is connected. This file isolates
that input. `survivorEdges` contains exactly the untouched old edge copies,
and `SurvivorCoreConnected` says that every pair of surviving vertices is
connected using only those copies. Under that hypothesis either smoothing is
connected, independently of the chosen terminal pairing.
-/

/-- The old edge copies untouched by deletion of the square and its spokes. -/
noncomputable def survivorEdges : Finset E := by
  classical
  exact Finset.univ.filter Q.Survives

@[simp] theorem mem_survivorEdges (e : E) :
    e ∈ Q.survivorEdges ↔ Q.Survives e := by
  classical
  simp [survivorEdges]

/-- Total reduction of an original vertex to the smoothed vertex type. On
square vertices it uses a fixed external fallback; on every endpoint of a
surviving edge it is the evident subtype inclusion. -/
noncomputable def reduceVertex : X ⊕ Y → Q.ReducedLeft ⊕ Q.ReducedRight := by
  classical
  intro v
  cases v with
  | inl x =>
      by_cases h : ∀ i, x ≠ Q.leftVertex i
      · exact .inl ⟨x, h⟩
      · exact .inl ⟨Q.externalLeft false, fun i => Q.externalLeft_ne false i⟩
  | inr y =>
      by_cases h : ∀ i, y ≠ Q.rightVertex i
      · exact .inr ⟨y, h⟩
      · exact .inr ⟨Q.externalRight false, fun i => Q.externalRight_ne false i⟩

@[simp] theorem reduceVertex_liftVertex
    (v : Q.ReducedLeft ⊕ Q.ReducedRight) :
    Q.reduceVertex (Q.liftVertex v) = v := by
  classical
  cases v with
  | inl x => simp [reduceVertex, liftVertex, x.property]
  | inr y => simp [reduceVertex, liftVertex, y.property]

/-- A survivor edge has exactly the expected reduced left endpoint. -/
@[simp] theorem reduceVertex_survivor_left (e : Q.Survivor) :
    Q.reduceVertex (.inl (G.left e.val)) =
      (.inl ⟨G.left e.val, Q.survivor_left_ne e⟩ :
        Q.ReducedLeft ⊕ Q.ReducedRight) := by
  classical
  simp [reduceVertex, Q.survivor_left_ne e]

/-- A survivor edge has exactly the expected reduced right endpoint. -/
@[simp] theorem reduceVertex_survivor_right (e : Q.Survivor) :
    Q.reduceVertex (.inr (G.right e.val)) =
      (.inr ⟨G.right e.val, Q.survivor_right_ne e⟩ :
        Q.ReducedLeft ⊕ Q.ReducedRight) := by
  classical
  simp [reduceVertex, Q.survivor_right_ne e]

/-- Every selected adjacency in the survivor core becomes a one-edge path in
either smoothing. -/
theorem survivorSelectedAdjacent_reachable_smooth
    (swap : Bool) {a b : X ⊕ Y}
    (h : G.SelectedAdjacent Q.survivorEdges a b) :
    (Q.smooth swap).FactorReachable Finset.univ
      (Q.reduceVertex a) (Q.reduceVertex b) := by
  rcases h with ⟨e, he, hdir⟩
  have hs : Q.Survives e := (Q.mem_survivorEdges e).1 he
  let es : Q.Survivor := ⟨e, hs⟩
  have hedge : (Sum.inl es : Q.SmoothEdge) ∈ (Finset.univ : Finset Q.SmoothEdge) := by
    simp
  have hp := (Q.smooth swap).factorReachable_endpoints hedge
  rcases hdir with hdir | hdir
  · rcases hdir with ⟨rfl, rfl⟩
    rw [show Q.reduceVertex (.inl (G.left e)) =
        (.inl ⟨G.left e, Q.survivor_left_ne es⟩ :
          Q.ReducedLeft ⊕ Q.ReducedRight) by
          simpa [es] using Q.reduceVertex_survivor_left es]
    rw [show Q.reduceVertex (.inr (G.right e)) =
        (.inr ⟨G.right e, Q.survivor_right_ne es⟩ :
          Q.ReducedLeft ⊕ Q.ReducedRight) by
          simpa [es] using Q.reduceVertex_survivor_right es]
    simpa [es] using hp
  · rcases hdir with ⟨rfl, rfl⟩
    rw [show Q.reduceVertex (.inr (G.right e)) =
        (.inr ⟨G.right e, Q.survivor_right_ne es⟩ :
          Q.ReducedLeft ⊕ Q.ReducedRight) by
          simpa [es] using Q.reduceVertex_survivor_right es]
    rw [show Q.reduceVertex (.inl (G.left e)) =
        (.inl ⟨G.left e, Q.survivor_left_ne es⟩ :
          Q.ReducedLeft ⊕ Q.ReducedRight) by
          simpa [es] using Q.reduceVertex_survivor_left es]
    simpa [es] using hp.symm

/-- Any path using only survivor copies transports to either smoothing. -/
theorem survivorReachable_smooth
    (swap : Bool) {a b : X ⊕ Y}
    (h : G.FactorReachable Q.survivorEdges a b) :
    (Q.smooth swap).FactorReachable Finset.univ
      (Q.reduceVertex a) (Q.reduceVertex b) := by
  exact h.of_edge_paths Q.reduceVertex
    (fun _ _ hab => Q.survivorSelectedAdjacent_reachable_smooth swap hab)

/-- The exact connectivity input needed from deletion of the four square
vertices. -/
abbrev SurvivorCoreConnected : Prop :=
  ∀ a b : Q.ReducedLeft ⊕ Q.ReducedRight,
    G.FactorReachable Q.survivorEdges (Q.liftVertex a) (Q.liftVertex b)

/-- Connectivity of the surviving core implies connectivity of either terminal
pairing. Fresh smoothing edges are not needed for this implication. -/
theorem smooth_isConnected_of_survivorCoreConnected
    (hcore : Q.SurvivorCoreConnected) (swap : Bool) :
    (Q.smooth swap).IsConnected := by
  constructor
  · exact ⟨.inl ⟨Q.externalLeft false, fun i => Q.externalLeft_ne false i⟩⟩
  · intro a b
    have h := Q.survivorReachable_smooth swap (hcore a b)
    simpa using h

/-- Consequently both pairings are connected under the same deletion-core
hypothesis. -/
theorem both_smoothings_connected_of_survivorCoreConnected
    (hcore : Q.SurvivorCoreConnected) :
    (Q.smooth false).IsConnected ∧ (Q.smooth true).IsConnected :=
  ⟨Q.smooth_isConnected_of_survivorCoreConnected hcore false,
    Q.smooth_isConnected_of_survivorCoreConnected hcore true⟩

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
