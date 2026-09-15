import BachThesisLean.Cubic.TightCutCubic

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Connectivity after deleting a small-boundary vertex set

This is the cut-counting lemma used by square smoothing. If every nontrivial
vertex shore has at least `k` boundary edge copies, while the deleted set has
fewer than `2*k` boundary copies, the surviving graph cannot split into two
components: the two component cuts would be disjoint subsets of the deleted
boundary and would already contribute at least `2*k` copies.
-/

/-- Edge copies having neither endpoint in the deleted vertex set. -/
noncomputable def edgesAvoidingVertices
    (G : BipartiteMultigraph X Y E) (D : Finset (X ⊕ Y)) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    (Sum.inl (G.left e) : X ⊕ Y) ∉ D ∧
      (Sum.inr (G.right e) : X ⊕ Y) ∉ D

@[simp] theorem mem_edgesAvoidingVertices
    (G : BipartiteMultigraph X Y E) (D : Finset (X ⊕ Y)) (e : E) :
    e ∈ G.edgesAvoidingVertices D ↔
      (Sum.inl (G.left e) : X ⊕ Y) ∉ D ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∉ D := by
  classical
  simp [edgesAvoidingVertices]

/-- The finite vertex set reachable from `a` through selected edge copies. -/
noncomputable def reachableVertices
    (G : BipartiteMultigraph X Y E) (S : Finset E) (a : X ⊕ Y) :
    Finset (X ⊕ Y) := by
  classical
  exact Finset.univ.filter fun v => G.FactorReachable S a v

@[simp] theorem mem_reachableVertices
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (a v : X ⊕ Y) :
    v ∈ G.reachableVertices S a ↔ G.FactorReachable S a v := by
  classical
  simp [reachableVertices]

/-- A path using only copies disjoint from `D`, starting outside `D`, never
enters `D`. -/
theorem FactorReachable.not_mem_of_edgesAvoidingVertices
    {G : BipartiteMultigraph X Y E} {D : Finset (X ⊕ Y)}
    {a v : X ⊕ Y} (ha : a ∉ D)
    (h : G.FactorReachable (G.edgesAvoidingVertices D) a v) :
    v ∉ D := by
  induction h with
  | refl => exact ha
  | @tail b c _ hstep _ =>
      rcases hstep with ⟨e, he, hdir | hdir⟩
      · have hav := (G.mem_edgesAvoidingVertices D e).1 he
        rw [hdir.2]
        exact hav.2
      · have hav := (G.mem_edgesAvoidingVertices D e).1 he
        rw [hdir.2]
        exact hav.1

/-- If `a` lies outside `D`, the cut around its surviving-edge component uses
only copies from the boundary of `D`. -/
theorem edgeCut_reachableVertices_subset_edgeCut
    (G : BipartiteMultigraph X Y E) (D : Finset (X ⊕ Y))
    (a : X ⊕ Y) (ha : a ∉ D) :
    G.edgeCut (G.reachableVertices (G.edgesAvoidingVertices D) a) ⊆
      G.edgeCut D := by
  classical
  intro e he
  have hcut :
      ((Sum.inl (G.left e) : X ⊕ Y) ∈
          G.reachableVertices (G.edgesAvoidingVertices D) a ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∉
          G.reachableVertices (G.edgesAvoidingVertices D) a) ∨
      ((Sum.inl (G.left e) : X ⊕ Y) ∉
          G.reachableVertices (G.edgesAvoidingVertices D) a ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∈
          G.reachableVertices (G.edgesAvoidingVertices D) a) := by
    simpa only [edgeCut, Finset.mem_filter, Finset.mem_univ, true_and] using he
  rcases hcut with hLR | hRL
  · have hleftReach :
        G.FactorReachable (G.edgesAvoidingVertices D) a
          (.inl (G.left e)) :=
      (G.mem_reachableVertices (G.edgesAvoidingVertices D) a _).1 hLR.1
    have hleftOut : (Sum.inl (G.left e) : X ⊕ Y) ∉ D :=
      hleftReach.not_mem_of_edgesAvoidingVertices ha
    by_cases hright : (Sum.inr (G.right e) : X ⊕ Y) ∈ D
    · simp [edgeCut, hleftOut, hright]
    · have heAvoid : e ∈ G.edgesAvoidingVertices D :=
        (G.mem_edgesAvoidingVertices D e).2 ⟨hleftOut, hright⟩
      have hrightReach := hleftReach.trans (G.factorReachable_endpoints heAvoid)
      exact False.elim (hLR.2
        ((G.mem_reachableVertices (G.edgesAvoidingVertices D) a _).2 hrightReach))
  · have hrightReach :
        G.FactorReachable (G.edgesAvoidingVertices D) a
          (.inr (G.right e)) :=
      (G.mem_reachableVertices (G.edgesAvoidingVertices D) a _).1 hRL.2
    have hrightOut : (Sum.inr (G.right e) : X ⊕ Y) ∉ D :=
      hrightReach.not_mem_of_edgesAvoidingVertices ha
    by_cases hleft : (Sum.inl (G.left e) : X ⊕ Y) ∈ D
    · simp [edgeCut, hleft, hrightOut]
    · have heAvoid : e ∈ G.edgesAvoidingVertices D :=
        (G.mem_edgesAvoidingVertices D e).2 ⟨hleft, hrightOut⟩
      have hleftReach :=
        hrightReach.trans (G.factorReachable_endpoints heAvoid).symm
      exact False.elim (hRL.1
        ((G.mem_reachableVertices (G.edgesAvoidingVertices D) a _).2 hleftReach))

/-- Distinct selected-edge components have disjoint reachable vertex sets. -/
theorem reachableVertices_disjoint_of_not_reachable
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    {a b : X ⊕ Y} (hnot : ¬ G.FactorReachable S a b) :
    Disjoint (G.reachableVertices S a) (G.reachableVertices S b) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro v hva hvb
  have hav := (G.mem_reachableVertices S a v).1 hva
  have hbv := (G.mem_reachableVertices S b v).1 hvb
  exact hnot (hav.trans hbv.symm)

/-- For two different surviving components, their cut-edge sets are disjoint.
An edge crossing both cuts would either put one endpoint in both components or
join the two components by a surviving edge. -/
theorem edgeCuts_reachableVertices_disjoint
    (G : BipartiteMultigraph X Y E) (D : Finset (X ⊕ Y))
    {a b : X ⊕ Y} (ha : a ∉ D) (hb : b ∉ D)
    (hnot : ¬ G.FactorReachable (G.edgesAvoidingVertices D) a b) :
    Disjoint
      (G.edgeCut (G.reachableVertices (G.edgesAvoidingVertices D) a))
      (G.edgeCut (G.reachableVertices (G.edgesAvoidingVertices D) b)) := by
  classical
  let S := G.edgesAvoidingVertices D
  let A := G.reachableVertices S a
  let B := G.reachableVertices S b
  have hAB : Disjoint A B := by
    exact G.reachableVertices_disjoint_of_not_reachable S hnot
  have hABmem := Finset.disjoint_left.mp hAB
  refine Finset.disjoint_left.mpr ?_
  intro e heA heB
  have hcutA :
      ((Sum.inl (G.left e) : X ⊕ Y) ∈ A ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∉ A) ∨
      ((Sum.inl (G.left e) : X ⊕ Y) ∉ A ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∈ A) := by
    simpa only [edgeCut, Finset.mem_filter, Finset.mem_univ, true_and] using heA
  have hcutB :
      ((Sum.inl (G.left e) : X ⊕ Y) ∈ B ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∉ B) ∨
      ((Sum.inl (G.left e) : X ⊕ Y) ∉ B ∧
        (Sum.inr (G.right e) : X ⊕ Y) ∈ B) := by
    simpa only [edgeCut, Finset.mem_filter, Finset.mem_univ, true_and] using heB
  rcases hcutA with hAL | hAR <;> rcases hcutB with hBL | hBR
  · exact hABmem hAL.1 hBL.1
  · have hleftReach : G.FactorReachable S a (.inl (G.left e)) := by
      simpa [A, S] using hAL.1
    have hrightReachB : G.FactorReachable S b (.inr (G.right e)) := by
      simpa [B, S] using hBR.2
    have hleftOut : (Sum.inl (G.left e) : X ⊕ Y) ∉ D := by
      exact hleftReach.not_mem_of_edgesAvoidingVertices ha
    have hrightOut : (Sum.inr (G.right e) : X ⊕ Y) ∉ D := by
      exact hrightReachB.not_mem_of_edgesAvoidingVertices hb
    have heS : e ∈ S := by
      simpa [S] using
        (G.mem_edgesAvoidingVertices D e).2 ⟨hleftOut, hrightOut⟩
    have hrightReachA := hleftReach.trans (G.factorReachable_endpoints heS)
    have hrightA : (Sum.inr (G.right e) : X ⊕ Y) ∈ A := by
      simpa [A, S] using hrightReachA
    exact hABmem hrightA hBR.2
  · have hrightReachA : G.FactorReachable S a (.inr (G.right e)) := by
      simpa [A, S] using hAR.2
    have hleftReachB : G.FactorReachable S b (.inl (G.left e)) := by
      simpa [B, S] using hBL.1
    have hrightOut : (Sum.inr (G.right e) : X ⊕ Y) ∉ D := by
      exact hrightReachA.not_mem_of_edgesAvoidingVertices ha
    have hleftOut : (Sum.inl (G.left e) : X ⊕ Y) ∉ D := by
      exact hleftReachB.not_mem_of_edgesAvoidingVertices hb
    have heS : e ∈ S := by
      simpa [S] using
        (G.mem_edgesAvoidingVertices D e).2 ⟨hleftOut, hrightOut⟩
    have hleftReachA :=
      hrightReachA.trans (G.factorReachable_endpoints heS).symm
    have hleftA : (Sum.inl (G.left e) : X ⊕ Y) ∈ A := by
      simpa [A, S] using hleftReachA
    exact hABmem hleftA hBL.1
  · exact hABmem hAR.2 hBR.2

/-- General boundary-deletion connectivity lemma. A deleted shore whose
boundary has size strictly less than twice the global minimum cut cannot split
the surviving vertices into two selected-edge components. -/
theorem factorReachable_edgesAvoidingVertices_of_boundary_lt_twice_minCut
    (G : BipartiteMultigraph X Y E) (D : Finset (X ⊕ Y)) (k : ℕ)
    (hmin : ∀ W : Finset (X ⊕ Y), W.Nonempty → Wᶜ.Nonempty →
      k ≤ (G.edgeCut W).card)
    (hboundary : (G.edgeCut D).card < 2 * k)
    {a b : X ⊕ Y} (ha : a ∉ D) (hb : b ∉ D) :
    G.FactorReachable (G.edgesAvoidingVertices D) a b := by
  classical
  by_contra hnot
  let S := G.edgesAvoidingVertices D
  let A := G.reachableVertices S a
  let B := G.reachableVertices S b
  have haA : a ∈ A := by
    exact (G.mem_reachableVertices S a a).2 (G.factorReachable_refl S a)
  have hbA : b ∉ A := by
    intro hba
    exact hnot ((G.mem_reachableVertices S a b).1 hba)
  have hbB : b ∈ B := by
    exact (G.mem_reachableVertices S b b).2 (G.factorReachable_refl S b)
  have haB : a ∉ B := by
    intro hab
    exact hnot ((G.mem_reachableVertices S b a).1 hab).symm
  have hAnonempty : A.Nonempty := ⟨a, haA⟩
  have hAcomp : Aᶜ.Nonempty := ⟨b, Finset.mem_compl.mpr hbA⟩
  have hBnonempty : B.Nonempty := ⟨b, hbB⟩
  have hBcomp : Bᶜ.Nonempty := ⟨a, Finset.mem_compl.mpr haB⟩
  have hkA : k ≤ (G.edgeCut A).card := hmin A hAnonempty hAcomp
  have hkB : k ≤ (G.edgeCut B).card := hmin B hBnonempty hBcomp
  have hAD : G.edgeCut A ⊆ G.edgeCut D := by
    simpa [A, S] using G.edgeCut_reachableVertices_subset_edgeCut D a ha
  have hBD : G.edgeCut B ⊆ G.edgeCut D := by
    simpa [B, S] using G.edgeCut_reachableVertices_subset_edgeCut D b hb
  have hdisj : Disjoint (G.edgeCut A) (G.edgeCut B) := by
    simpa [A, B, S] using G.edgeCuts_reachableVertices_disjoint D ha hb hnot
  have hunion : G.edgeCut A ∪ G.edgeCut B ⊆ G.edgeCut D :=
    Finset.union_subset hAD hBD
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  omega

end BipartiteMultigraph
end BachThesisLean
