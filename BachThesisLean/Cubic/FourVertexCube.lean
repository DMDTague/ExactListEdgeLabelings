import BachThesisLean.Cubic.ThreeVertexBraceCase
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Pi

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# The canonical four-by-four cubic graph

A simple cubic bipartite graph with four vertices on each shore is, after
relabeling, `K₄,₄` with one diagonal perfect matching removed.  This file first
handles that fixed graph itself.

The ordinary EEP predicate contains reflexive-transitive closure, so it is not
directly decidable.  Instead we use a bounded finite certificate.  The nine
perfect matchings of the cube are listed explicitly.  For each prescribed pair
we choose the first listed matching whose complementary factor contains a
bounded path between the marked left endpoints.  Lean then checks only the
finite path certificate and converts it explicitly to genuine
`FactorReachable`.
-/

/-- A bounded certificate joining the left endpoints of two omitted copies by
four complementary edge copies. -/
def EdgePairFourBridgeCertificate (G : BipartiteMultigraph X Y E)
    (e f : E) : Prop :=
  ∃ P : Finset E,
    G.IsPerfectMatching P ∧ e ∉ P ∧ f ∉ P ∧
      (G.left e = G.left f ∨
        ∃ a b c d : E,
          a ∉ P ∧ b ∉ P ∧ c ∉ P ∧ d ∉ P ∧
          G.left a = G.left e ∧
          G.right a = G.right b ∧
          G.left b = G.left c ∧
          G.right c = G.right d ∧
          G.left d = G.left f)

instance (G : BipartiteMultigraph X Y E) (e f : E) :
    Decidable (G.EdgePairFourBridgeCertificate e f) := by
  unfold EdgePairFourBridgeCertificate
  infer_instance

/-- A bounded four-edge certificate gives a genuine EEP witness. -/
theorem edgePairWitness_of_fourBridgeCertificate
    (G : BipartiteMultigraph X Y E) {e f : E}
    (hcert : G.EdgePairFourBridgeCertificate e f) :
    G.EdgePairWitness e f := by
  classical
  rcases hcert with ⟨P, hP, heP, hfP, hleft | hpath⟩
  · refine ⟨P, .inl (G.left e), hP, ?_, ?_⟩
    · exact ⟨Finset.mem_compl.mpr heP,
        G.factorReachable_refl Pᶜ (.inl (G.left e))⟩
    · refine ⟨Finset.mem_compl.mpr hfP, ?_⟩
      simpa [hleft] using
        G.factorReachable_refl Pᶜ (.inl (G.left e))
  · rcases hpath with
      ⟨a, b, c, d, haP, hbP, hcP, hdP, haL, habR, hbcL, hcdR, hdL⟩
    have haReach :=
      G.factorReachable_endpoints (S := Pᶜ) (e := a)
        (Finset.mem_compl.mpr haP)
    have hbReach :=
      G.factorReachable_endpoints (S := Pᶜ) (e := b)
        (Finset.mem_compl.mpr hbP)
    have hcReach :=
      G.factorReachable_endpoints (S := Pᶜ) (e := c)
        (Finset.mem_compl.mpr hcP)
    have hdReach :=
      G.factorReachable_endpoints (S := Pᶜ) (e := d)
        (Finset.mem_compl.mpr hdP)
    have hba :
        G.FactorReachable Pᶜ (.inr (G.right a)) (.inl (G.left b)) := by
      simpa [habR] using hbReach.symm
    have hbc :
        G.FactorReachable Pᶜ (.inl (G.left b)) (.inr (G.right c)) := by
      simpa [hbcL] using hcReach
    have hdc :
        G.FactorReachable Pᶜ (.inr (G.right c)) (.inl (G.left d)) := by
      simpa [hcdR] using hdReach.symm
    have hwalk := ((haReach.trans hba).trans hbc).trans hdc
    have hefReach :
        G.FactorReachable Pᶜ (.inl (G.left e)) (.inl (G.left f)) := by
      simpa [haL, hdL] using hwalk
    refine ⟨P, .inl (G.left e), hP, ?_, ?_⟩
    · exact ⟨Finset.mem_compl.mpr heP,
        G.factorReachable_refl Pᶜ (.inl (G.left e))⟩
    · exact ⟨Finset.mem_compl.mpr hfP, hefReach⟩

/-- The three right neighbours of each left vertex, in increasing order with
the diagonal value omitted. -/
def fourCubeRight : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3],
    ![0, 2, 3],
    ![0, 1, 3],
    ![0, 1, 2]]

/-- Actual edge copies of the canonical graph.  The first coordinate is the
left endpoint and the second chooses one of its three off-diagonal neighbours. -/
abbrev FourCubeEdge := Fin 4 × Fin 3

/-- The canonical graph `K₄,₄` minus its diagonal perfect matching. -/
def fourCube : BipartiteMultigraph (Fin 4) (Fin 4) FourCubeEdge where
  left e := e.1
  right e := fourCubeRight e.1 e.2

@[simp] theorem fourCube_left (e : FourCubeEdge) : fourCube.left e = e.1 := rfl
@[simp] theorem fourCube_right (e : FourCubeEdge) :
    fourCube.right e = fourCubeRight e.1 e.2 := rfl

/-- Every canonical copy is genuinely off the deleted diagonal. -/
theorem fourCube_right_ne_left (e : FourCubeEdge) :
    fourCube.right e ≠ fourCube.left e := by
  rcases e with ⟨i, s⟩
  fin_cases i <;> fin_cases s <;> decide

/-- The nine derangements of four labels, encoded by the three off-diagonal
slot choices in each row. -/
def fourCubeMatchingSlots : Fin 9 → Fin 4 → Fin 3 :=
  ![![0, 0, 2, 2],
    ![0, 1, 2, 0],
    ![0, 2, 0, 2],
    ![1, 0, 2, 1],
    ![1, 2, 0, 1],
    ![1, 2, 1, 0],
    ![2, 0, 1, 2],
    ![2, 1, 0, 1],
    ![2, 1, 1, 0]]

/-- The perfect matching indexed by one of the nine derangements. -/
def fourCubeIndexedMatching (k : Fin 9) : Finset FourCubeEdge :=
  {(0, fourCubeMatchingSlots k 0),
    (1, fourCubeMatchingSlots k 1),
    (2, fourCubeMatchingSlots k 2),
    (3, fourCubeMatchingSlots k 3)}

/-- Every indexed matching is a genuine perfect matching. -/
theorem fourCubeIndexedMatching_isPerfectMatching (k : Fin 9) :
    fourCube.IsPerfectMatching (fourCubeIndexedMatching k) := by
  fin_cases k <;> decide

/-- For a fixed indexed matching, this is the finite condition needed to turn
the prescribed pair into a four-edge bridge certificate. -/
def FourCubeMatchingWorks (k : Fin 9) (e f : FourCubeEdge) : Prop :=
  let P := fourCubeIndexedMatching k
  e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 4, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        fourCubeRight e.1 s0 = fourCubeRight x s1 ∧
        fourCubeRight x s2 = fourCubeRight f.1 s3)

instance (k : Fin 9) (e f : FourCubeEdge) :
    Decidable (FourCubeMatchingWorks k e f) := by
  unfold FourCubeMatchingWorks
  infer_instance

/-- Deterministically select the first indexed matching whose complement
supplies the required bounded bridge.  The final branch is safe for distinct
copies by the finite theorem below. -/
def fourCubeChosenMatchingIndex (e f : FourCubeEdge) : Fin 9 :=
  if FourCubeMatchingWorks 0 e f then 0
  else if FourCubeMatchingWorks 1 e f then 1
  else if FourCubeMatchingWorks 2 e f then 2
  else if FourCubeMatchingWorks 3 e f then 3
  else if FourCubeMatchingWorks 4 e f then 4
  else if FourCubeMatchingWorks 5 e f then 5
  else if FourCubeMatchingWorks 6 e f then 6
  else if FourCubeMatchingWorks 7 e f then 7
  else 8

private instance decidableForallFintypeTwo
    {α β : Type*} [Fintype α] [Fintype β]
    {p : α → β → Prop} [∀ a b, Decidable (p a b)] :
    Decidable (∀ a b, p a b) := by
  letI : DecidablePred (fun a : α => ∀ b : β, p a b) := fun a => by
    letI : DecidablePred (p a) := fun b => inferInstance
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The deterministic matching selector works for every distinct prescribed
pair.  Only nine genuine matchings and their bounded path tests are evaluated. -/
theorem fourCube_chosenMatching_works :
    ∀ e f : FourCubeEdge, e ≠ f →
      FourCubeMatchingWorks (fourCubeChosenMatchingIndex e f) e f := by
  decide

/-- Convert the deterministic finite witness into the generic four-edge bridge
certificate. -/
theorem fourCube_fourBridgeCertificate
    (e f : FourCubeEdge) (hef : e ≠ f) :
    fourCube.EdgePairFourBridgeCertificate e f := by
  let k := fourCubeChosenMatchingIndex e f
  let P := fourCubeIndexedMatching k
  have hP : fourCube.IsPerfectMatching P := by
    simpa [P] using fourCubeIndexedMatching_isPerfectMatching k
  have hworks : FourCubeMatchingWorks k e f := by
    simpa [k] using fourCube_chosenMatching_works e f hef
  change e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 4, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        fourCubeRight e.1 s0 = fourCubeRight x s1 ∧
        fourCubeRight x s2 = fourCubeRight f.1 s3) at hworks
  rcases hworks with ⟨heP, hfP, hleft | hpath⟩
  · exact ⟨P, hP, heP, hfP, Or.inl hleft⟩
  · rcases hpath with ⟨x, s0, s1, s2, s3, haP, hbP, hcP, hdP, hab, hcd⟩
    let a : FourCubeEdge := (e.1, s0)
    let b : FourCubeEdge := (x, s1)
    let c : FourCubeEdge := (x, s2)
    let d : FourCubeEdge := (f.1, s3)
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

/-- The canonical four-by-four cubic graph has EEP. -/
theorem fourCube_hasEEP : fourCube.HasEEP := by
  intro e f hef
  exact edgePairWitness_of_fourBridgeCertificate fourCube
    (fourCube_fourBridgeCertificate e f hef)

end BipartiteMultigraph
end BachThesisLean
