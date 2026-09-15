import BachThesisLean.Cubic.FourVertexBraceCase
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Pi

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# A canonical five-by-five cubic case: complement a ten-cycle

A simple cubic bipartite graph on five vertices per shore has a two-regular
complement in `K₅,₅`.  One possible complement type is a single ten-cycle.
This file fixes a canonical representative of that type and proves EEP by a
bounded certificate.

As in the four-by-four cube case, we list only genuine perfect matchings.  For
each prescribed pair, a deterministic selector chooses the first matching
whose complementary two-factor joins the marked left endpoints within four
edge copies.  The finite check is then converted to the genuine
`FactorReachable` relation by `edgePairWitness_of_fourBridgeCertificate`.
-/

/-- The three present neighbours in each row when the two missing cells are
`(i,i)` and `(i,i+1 mod 5)`. -/
def fiveCycleRight : Fin 5 → Fin 3 → Fin 5 :=
  ![![2, 3, 4],
    ![0, 3, 4],
    ![0, 1, 4],
    ![0, 1, 2],
    ![1, 2, 3]]

abbrev FiveCycleEdge := Fin 5 × Fin 3

/-- Canonical cubic graph whose missing-cell graph is a single `C₁₀`. -/
def fiveCycleGraph : BipartiteMultigraph (Fin 5) (Fin 5) FiveCycleEdge where
  left e := e.1
  right e := fiveCycleRight e.1 e.2

@[simp] theorem fiveCycleGraph_left (e : FiveCycleEdge) :
    fiveCycleGraph.left e = e.1 := rfl

@[simp] theorem fiveCycleGraph_right (e : FiveCycleEdge) :
    fiveCycleGraph.right e = fiveCycleRight e.1 e.2 := rfl

/-- The thirteen perfect matchings of the canonical graph, encoded by one slot
choice in each left row. -/
def fiveCycleMatchingSlots : Fin 13 → Fin 5 → Fin 3 :=
  ![![0, 0, 2, 1, 2],
    ![0, 1, 2, 0, 0],
    ![0, 2, 0, 1, 2],
    ![0, 2, 1, 0, 2],
    ![1, 0, 2, 1, 1],
    ![1, 0, 2, 2, 0],
    ![1, 2, 0, 1, 1],
    ![1, 2, 0, 2, 0],
    ![1, 2, 1, 0, 1],
    ![2, 0, 1, 2, 2],
    ![2, 1, 0, 1, 1],
    ![2, 1, 0, 2, 0],
    ![2, 1, 1, 0, 1]]

/-- The indexed five-edge perfect matching. -/
def fiveCycleIndexedMatching (k : Fin 13) : Finset FiveCycleEdge :=
  {(0, fiveCycleMatchingSlots k 0),
    (1, fiveCycleMatchingSlots k 1),
    (2, fiveCycleMatchingSlots k 2),
    (3, fiveCycleMatchingSlots k 3),
    (4, fiveCycleMatchingSlots k 4)}

/-- Every listed row-slot choice is genuinely a perfect matching. -/
theorem fiveCycleIndexedMatching_isPerfectMatching (k : Fin 13) :
    fiveCycleGraph.IsPerfectMatching (fiveCycleIndexedMatching k) := by
  fin_cases k <;> decide

/-- For one listed matching, the bounded condition sufficient for the generic
four-edge bridge certificate. -/
def FiveCycleMatchingWorks (k : Fin 13) (e f : FiveCycleEdge) : Prop :=
  let P := fiveCycleIndexedMatching k
  e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 5, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        fiveCycleRight e.1 s0 = fiveCycleRight x s1 ∧
        fiveCycleRight x s2 = fiveCycleRight f.1 s3)

instance (k : Fin 13) (e f : FiveCycleEdge) :
    Decidable (FiveCycleMatchingWorks k e f) := by
  unfold FiveCycleMatchingWorks
  infer_instance

/-- Deterministically choose the first listed matching with the required
bounded complementary bridge. -/
def fiveCycleChosenMatchingIndex (e f : FiveCycleEdge) : Fin 13 :=
  if FiveCycleMatchingWorks 0 e f then 0
  else if FiveCycleMatchingWorks 1 e f then 1
  else if FiveCycleMatchingWorks 2 e f then 2
  else if FiveCycleMatchingWorks 3 e f then 3
  else if FiveCycleMatchingWorks 4 e f then 4
  else if FiveCycleMatchingWorks 5 e f then 5
  else if FiveCycleMatchingWorks 6 e f then 6
  else if FiveCycleMatchingWorks 7 e f then 7
  else if FiveCycleMatchingWorks 8 e f then 8
  else if FiveCycleMatchingWorks 9 e f then 9
  else if FiveCycleMatchingWorks 10 e f then 10
  else if FiveCycleMatchingWorks 11 e f then 11
  else 12

private instance decidableForallFintypeTwoFiveCycle
    {α β : Type*} [Fintype α] [Fintype β]
    {p : α → β → Prop} [∀ a b, Decidable (p a b)] :
    Decidable (∀ a b, p a b) := by
  letI : DecidablePred (fun a : α => ∀ b : β, p a b) := fun a => by
    letI : DecidablePred (p a) := fun b => inferInstance
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
/-- The deterministic selector succeeds for every distinct pair of actual edge
copies. -/
theorem fiveCycle_chosenMatching_works :
    ∀ e f : FiveCycleEdge, e ≠ f →
      FiveCycleMatchingWorks (fiveCycleChosenMatchingIndex e f) e f := by
  decide

/-- The selected finite witness is a generic four-edge bridge certificate. -/
theorem fiveCycle_fourBridgeCertificate
    (e f : FiveCycleEdge) (hef : e ≠ f) :
    fiveCycleGraph.EdgePairFourBridgeCertificate e f := by
  let k := fiveCycleChosenMatchingIndex e f
  let P := fiveCycleIndexedMatching k
  have hP : fiveCycleGraph.IsPerfectMatching P := by
    simpa [P] using fiveCycleIndexedMatching_isPerfectMatching k
  have hworks : FiveCycleMatchingWorks k e f := by
    simpa [k] using fiveCycle_chosenMatching_works e f hef
  change e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 5, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        fiveCycleRight e.1 s0 = fiveCycleRight x s1 ∧
        fiveCycleRight x s2 = fiveCycleRight f.1 s3) at hworks
  rcases hworks with ⟨heP, hfP, hleft | hpath⟩
  · exact ⟨P, hP, heP, hfP, Or.inl hleft⟩
  · rcases hpath with ⟨x, s0, s1, s2, s3, haP, hbP, hcP, hdP, hab, hcd⟩
    let a : FiveCycleEdge := (e.1, s0)
    let b : FiveCycleEdge := (x, s1)
    let c : FiveCycleEdge := (x, s2)
    let d : FiveCycleEdge := (f.1, s3)
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

/-- The canonical five-by-five graph with ten-cycle complement has EEP. -/
theorem fiveCycleGraph_hasEEP : fiveCycleGraph.HasEEP := by
  intro e f hef
  exact edgePairWitness_of_fourBridgeCertificate fiveCycleGraph
    (fiveCycle_fourBridgeCertificate e f hef)

end BipartiteMultigraph
end BachThesisLean
