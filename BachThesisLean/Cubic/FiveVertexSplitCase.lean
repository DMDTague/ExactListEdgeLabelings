import BachThesisLean.Cubic.FiveVertexCycleCase
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Pi

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# A canonical five-by-five cubic case: complement `C₄ ⊔ C₆`

The second two-regular complement type on five vertices per shore is the
disjoint union of a four-cycle and a six-cycle.  This file fixes a canonical
representative and proves EEP by a bounded finite certificate.

For this representative an especially cheap deterministic selector suffices:
choose the first listed perfect matching that avoids the two prescribed edge
copies.  A finite theorem verifies that the selected complement always supplies
the bounded four-edge bridge required by `EdgePairFourBridgeCertificate`.
-/

/-- The three present neighbours in each row when the missing-cell graph is
`C₄ ⊔ C₆`. -/
def fiveSplitRight : Fin 5 → Fin 3 → Fin 5 :=
  ![![2, 3, 4],
    ![2, 3, 4],
    ![0, 1, 4],
    ![0, 1, 2],
    ![0, 1, 3]]

abbrev FiveSplitEdge := Fin 5 × Fin 3

/-- Canonical cubic graph whose missing-cell graph is `C₄ ⊔ C₆`. -/
def fiveSplitGraph : BipartiteMultigraph (Fin 5) (Fin 5) FiveSplitEdge where
  left e := e.1
  right e := fiveSplitRight e.1 e.2

@[simp] theorem fiveSplitGraph_left (e : FiveSplitEdge) :
    fiveSplitGraph.left e = e.1 := rfl

@[simp] theorem fiveSplitGraph_right (e : FiveSplitEdge) :
    fiveSplitGraph.right e = fiveSplitRight e.1 e.2 := rfl

/-- The twelve perfect matchings of the canonical graph, encoded by one slot
choice in each left row. -/
def fiveSplitMatchingSlots : Fin 12 → Fin 5 → Fin 3 :=
  ![![0, 1, 2, 0, 1],
    ![0, 1, 2, 1, 0],
    ![0, 2, 0, 1, 2],
    ![0, 2, 1, 0, 2],
    ![1, 0, 2, 0, 1],
    ![1, 0, 2, 1, 0],
    ![1, 2, 0, 2, 1],
    ![1, 2, 1, 2, 0],
    ![2, 0, 0, 1, 2],
    ![2, 0, 1, 0, 2],
    ![2, 1, 0, 2, 1],
    ![2, 1, 1, 2, 0]]

/-- The indexed five-edge perfect matching. -/
def fiveSplitIndexedMatching (k : Fin 12) : Finset FiveSplitEdge :=
  {(0, fiveSplitMatchingSlots k 0),
    (1, fiveSplitMatchingSlots k 1),
    (2, fiveSplitMatchingSlots k 2),
    (3, fiveSplitMatchingSlots k 3),
    (4, fiveSplitMatchingSlots k 4)}

/-- Every listed row-slot choice is genuinely a perfect matching. -/
theorem fiveSplitIndexedMatching_isPerfectMatching (k : Fin 12) :
    fiveSplitGraph.IsPerfectMatching (fiveSplitIndexedMatching k) := by
  fin_cases k <;> decide

/-- Cheap selector predicate: the indexed perfect matching omits both marked
copies. -/
def FiveSplitMatchingAvoids (k : Fin 12) (e f : FiveSplitEdge) : Prop :=
  let P := fiveSplitIndexedMatching k
  e ∉ P ∧ f ∉ P

instance (k : Fin 12) (e f : FiveSplitEdge) :
    Decidable (FiveSplitMatchingAvoids k e f) := by
  unfold FiveSplitMatchingAvoids
  infer_instance

/-- Full bounded bridge condition for one indexed matching. -/
def FiveSplitMatchingWorks (k : Fin 12) (e f : FiveSplitEdge) : Prop :=
  let P := fiveSplitIndexedMatching k
  e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 5, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        fiveSplitRight e.1 s0 = fiveSplitRight x s1 ∧
        fiveSplitRight x s2 = fiveSplitRight f.1 s3)

instance (k : Fin 12) (e f : FiveSplitEdge) :
    Decidable (FiveSplitMatchingWorks k e f) := by
  unfold FiveSplitMatchingWorks
  infer_instance

/-- Deterministically choose the first listed perfect matching avoiding both
prescribed copies. -/
def fiveSplitChosenMatchingIndex (e f : FiveSplitEdge) : Fin 12 :=
  if FiveSplitMatchingAvoids 0 e f then 0
  else if FiveSplitMatchingAvoids 1 e f then 1
  else if FiveSplitMatchingAvoids 2 e f then 2
  else if FiveSplitMatchingAvoids 3 e f then 3
  else if FiveSplitMatchingAvoids 4 e f then 4
  else if FiveSplitMatchingAvoids 5 e f then 5
  else if FiveSplitMatchingAvoids 6 e f then 6
  else if FiveSplitMatchingAvoids 7 e f then 7
  else if FiveSplitMatchingAvoids 8 e f then 8
  else if FiveSplitMatchingAvoids 9 e f then 9
  else if FiveSplitMatchingAvoids 10 e f then 10
  else 11

private instance decidableForallFintypeTwoFiveSplit
    {α β : Type*} [Fintype α] [Fintype β]
    {p : α → β → Prop} [∀ a b, Decidable (p a b)] :
    Decidable (∀ a b, p a b) := by
  letI : DecidablePred (fun a : α => ∀ b : β, p a b) := fun a => by
    letI : DecidablePred (p a) := fun b => inferInstance
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
/-- For every distinct prescribed pair, the first listed matching avoiding the
pair also has a complementary bridge of length at most four. -/
theorem fiveSplit_chosenMatching_works :
    ∀ e f : FiveSplitEdge, e ≠ f →
      FiveSplitMatchingWorks (fiveSplitChosenMatchingIndex e f) e f := by
  decide

/-- The selected finite witness is a generic four-edge bridge certificate. -/
theorem fiveSplit_fourBridgeCertificate
    (e f : FiveSplitEdge) (hef : e ≠ f) :
    fiveSplitGraph.EdgePairFourBridgeCertificate e f := by
  let k := fiveSplitChosenMatchingIndex e f
  let P := fiveSplitIndexedMatching k
  have hP : fiveSplitGraph.IsPerfectMatching P := by
    simpa [P] using fiveSplitIndexedMatching_isPerfectMatching k
  have hworks : FiveSplitMatchingWorks k e f := by
    simpa [k] using fiveSplit_chosenMatching_works e f hef
  change e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 5, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        fiveSplitRight e.1 s0 = fiveSplitRight x s1 ∧
        fiveSplitRight x s2 = fiveSplitRight f.1 s3) at hworks
  rcases hworks with ⟨heP, hfP, hleft | hpath⟩
  · exact ⟨P, hP, heP, hfP, Or.inl hleft⟩
  · rcases hpath with ⟨x, s0, s1, s2, s3, haP, hbP, hcP, hdP, hab, hcd⟩
    let a : FiveSplitEdge := (e.1, s0)
    let b : FiveSplitEdge := (x, s1)
    let c : FiveSplitEdge := (x, s2)
    let d : FiveSplitEdge := (f.1, s3)
    refine ⟨P, hP, heP, hfP,
      Or.inr ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa [a] using haP
    · simpa [b] using hbP
    · simpa [c] using hcP
    · simpa [d] using hdP
    · rfl
    · simpa [a, b] using hab
    · rfl
    · simpa [c, d] using hcd
    · rfl

/-- The canonical five-by-five graph with `C₄ ⊔ C₆` complement has EEP. -/
theorem fiveSplitGraph_hasEEP : fiveSplitGraph.HasEEP := by
  intro e f hef
  exact edgePairWitness_of_fourBridgeCertificate fiveSplitGraph
    (fiveSplit_fourBridgeCertificate e f hef)

end BipartiteMultigraph
end BachThesisLean
