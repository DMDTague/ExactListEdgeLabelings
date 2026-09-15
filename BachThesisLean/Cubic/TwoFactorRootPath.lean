import BachThesisLean.Cubic.FactorComponents

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Deleting a root from a finite two-factor

The manuscript's star-product argument uses the elementary fact that deleting
a root from its cycle in a complementary two-factor leaves a path between the
two unused root ports.  In the edge-copy model it is more robust to formulate
the needed content as reachability after removing the selected root edges.
The proof below uses finite bipartite degree balance, and therefore also covers
parallel edge copies and the repeated-endpoint case.
-/

/-- Remove from a selected factor exactly the selected edge copies incident
with `root`.  Removing all graph edges at `root` would give the same selected
edge set, but this formulation exposes the two-factor bookkeeping directly. -/
noncomputable def factorDeleteRoot
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) : Finset E :=
  S \ G.selectedIncident S root

@[simp] theorem mem_factorDeleteRoot
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) (e : E) :
    e ∈ G.factorDeleteRoot S root ↔
      e ∈ S ∧ e ∉ G.selectedIncident S root := by
  simp [factorDeleteRoot]

/-- The deleted root is isolated in the remaining selected factor. -/
@[simp] theorem selectedIncident_factorDeleteRoot_root
    (G : BipartiteMultigraph X Y E) (S : Finset E) (root : X ⊕ Y) :
    G.selectedIncident (G.factorDeleteRoot S root) root = ∅ := by
  classical
  ext e
  simp only [mem_selectedIncident, mem_factorDeleteRoot,
    Finset.not_mem_empty, iff_false]
  rintro ⟨⟨heS, hnot⟩, hinc⟩
  exact hnot ⟨heS, hinc⟩

/-- Reachability to an isolated target can only be the zero-length path. -/
theorem FactorReachable.eq_of_target_isolated
    {G : BipartiteMultigraph X Y E} {S : Finset E} {a b : X ⊕ Y}
    (h : G.FactorReachable S a b)
    (hb : G.selectedIncident S b = ∅) : a = b := by
  rcases Relation.ReflTransGen.cases_tail h with hba | ⟨c, hac, hcb⟩
  · exact hba.symm
  · rcases hcb with ⟨e, he, hcase | hcase⟩
    · have hinc : G.Incident e b := by
        rw [hcase.2]
        rfl
      have hmem : e ∈ G.selectedIncident S b :=
        (G.mem_selectedIncident S b e).2 ⟨he, hinc⟩
      have : False := by simpa [hb] using hmem
      exact this.elim
    · have hinc : G.Incident e b := by
        rw [hcase.2]
        rfl
      have hmem : e ∈ G.selectedIncident S b :=
        (G.mem_selectedIncident S b e).2 ⟨he, hinc⟩
      have : False := by simpa [hb] using hmem
      exact this.elim

/-- Two distinct selected root edges exhaust the selected incidence of a
spanning two-factor at that root. -/
theorem IsTwoFactor.selectedIncident_eq_pair
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {root : X ⊕ Y} {e f : E}
    (he : e ∈ G.selectedIncident S root)
    (hf : f ∈ G.selectedIncident S root) (hef : e ≠ f) :
    G.selectedIncident S root = {e, f} := by
  classical
  have hsub : ({e, f} : Finset E) ⊆ G.selectedIncident S root := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf
  have hcard : (G.selectedIncident S root).card ≤ ({e, f} : Finset E).card := by
    rw [hS root]
    simp [hef]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- At one endpoint of a deleted right-root edge, the residual selected degree
is one, provided the other root edge has a different left endpoint. -/
theorem IsTwoFactor.factorDeleteRightRoot_endpoint_card_one
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {r : Y} {e f : E}
    (he : e ∈ G.selectedIncident S (.inr r))
    (hf : f ∈ G.selectedIncident S (.inr r)) (hef : e ≠ f)
    (hleft : G.left e ≠ G.left f) :
    (G.selectedIncident (G.factorDeleteRoot S (.inr r))
      (.inl (G.left e))).card = 1 := by
  classical
  have hroot := hS.selectedIncident_eq_pair he hf hef
  have heS : e ∈ S := ((G.mem_selectedIncident S (.inr r) e).1 he).1
  have heLeft : e ∈ G.selectedIncident S (.inl (G.left e)) :=
    (G.mem_selectedIncident S (.inl (G.left e)) e).2 ⟨heS, rfl⟩
  have hEq :
      G.selectedIncident (G.factorDeleteRoot S (.inr r)) (.inl (G.left e)) =
        (G.selectedIncident S (.inl (G.left e))).erase e := by
    ext g
    simp only [mem_selectedIncident, mem_factorDeleteRoot, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hgS, hgNotRoot⟩, hgLeft⟩
      refine ⟨?_, ⟨hgS, hgLeft⟩⟩
      intro hge
      subst g
      exact hgNotRoot ((G.mem_selectedIncident S (.inr r) e).1 he)
    · rintro ⟨hgne, ⟨hgS, hgLeft⟩⟩
      refine ⟨⟨hgS, ?_⟩, hgLeft⟩
      intro hgRoot
      have hgRootMem : g ∈ G.selectedIncident S (.inr r) :=
        (G.mem_selectedIncident S (.inr r) g).2 hgRoot
      have hgPair : g = e ∨ g = f := by
        rw [hroot] at hgRootMem
        simpa using hgRootMem
      rcases hgPair with hge | hgf
      · exact hgne hge
      · subst g
        change G.left f = G.left e at hgLeft
        exact hleft hgLeft.symm
  rw [hEq, Finset.card_erase_of_mem heLeft, hS (.inl (G.left e))]

/-- Away from both left endpoints of the deleted right-root edges, residual
selected degree stays two. -/
theorem IsTwoFactor.factorDeleteRightRoot_left_card_two
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {r : Y} {e f : E}
    (he : e ∈ G.selectedIncident S (.inr r))
    (hf : f ∈ G.selectedIncident S (.inr r)) (hef : e ≠ f)
    {x : X} (hxe : x ≠ G.left e) (hxf : x ≠ G.left f) :
    (G.selectedIncident (G.factorDeleteRoot S (.inr r)) (.inl x)).card = 2 := by
  classical
  have hroot := hS.selectedIncident_eq_pair he hf hef
  have hEq :
      G.selectedIncident (G.factorDeleteRoot S (.inr r)) (.inl x) =
        G.selectedIncident S (.inl x) := by
    ext g
    simp only [mem_selectedIncident, mem_factorDeleteRoot]
    constructor
    · rintro ⟨⟨hgS, _⟩, hgLeft⟩
      exact ⟨hgS, hgLeft⟩
    · rintro ⟨hgS, hgLeft⟩
      refine ⟨⟨hgS, ?_⟩, hgLeft⟩
      intro hgRoot
      have hgRootMem : g ∈ G.selectedIncident S (.inr r) :=
        (G.mem_selectedIncident S (.inr r) g).2 hgRoot
      have hgPair : g = e ∨ g = f := by
        rw [hroot] at hgRootMem
        simpa using hgRootMem
      rcases hgPair with hge | hgf
      · subst g
        change G.left e = x at hgLeft
        exact hxe hgLeft.symm
      · subst g
        change G.left f = x at hgLeft
        exact hxf hgLeft.symm
  rw [hEq, hS (.inl x)]

/-- Deleting a right root does not change selected degree at any other right
vertex. -/
theorem IsTwoFactor.factorDeleteRightRoot_right_card_two
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {r y : Y} (hyr : y ≠ r) :
    (G.selectedIncident (G.factorDeleteRoot S (.inr r)) (.inr y)).card = 2 := by
  classical
  have hEq :
      G.selectedIncident (G.factorDeleteRoot S (.inr r)) (.inr y) =
        G.selectedIncident S (.inr y) := by
    ext g
    simp only [mem_selectedIncident, mem_factorDeleteRoot]
    constructor
    · rintro ⟨⟨hgS, _⟩, hgRight⟩
      exact ⟨hgS, hgRight⟩
    · rintro ⟨hgS, hgRight⟩
      refine ⟨⟨hgS, ?_⟩, hgRight⟩
      intro hgRoot
      have hgRoot' := hgRoot.2
      change G.right g = r at hgRoot'
      change G.right g = y at hgRight
      exact hyr (hgRight.symm.trans hgRoot')
  rw [hEq, hS (.inr y)]

/-- Right-root form of the manuscript's path-after-root-deletion statement.
If two selected two-factor edge copies meet a right root, then their opposite
(left) endpoints remain in the same component after the root edges are
deleted.  If the two edge copies have the same opposite endpoint this is the
zero-length path case. -/
theorem IsTwoFactor.factorDeleteRightRoot_reaches_between_ports
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {r : Y} {e f : E}
    (he : e ∈ G.selectedIncident S (.inr r))
    (hf : f ∈ G.selectedIncident S (.inr r)) :
    G.FactorReachable (G.factorDeleteRoot S (.inr r))
      (.inl (G.left e)) (.inl (G.left f)) := by
  classical
  by_cases hef : e = f
  · subst f
    exact G.factorReachable_refl _ _
  by_cases hleft : G.left e = G.left f
  · simpa [hleft] using
      (G.factorReachable_refl (G.factorDeleteRoot S (.inr r)) (.inl (G.left e)))
  let T := G.factorDeleteRoot S (.inr r)
  let L := G.factorComponentLeft T (.inl (G.left e))
  let R := G.factorComponentRight T (.inl (G.left e))
  by_contra hnot
  have hleL : G.left e ∈ L := by
    apply (G.mem_factorComponentLeft T (.inl (G.left e)) (G.left e)).2
    exact G.factorReachable_refl T _
  have hlfNot : G.left f ∉ L := by
    intro hmem
    apply hnot
    exact (G.mem_factorComponentLeft T (.inl (G.left e)) (G.left f)).1 hmem
  have hdegE :
      (G.selectedIncident T (.inl (G.left e))).card = 1 := by
    simpa [T] using
      hS.factorDeleteRightRoot_endpoint_card_one he hf hef hleft
  have hsumL :
      (∑ x ∈ L, (G.selectedIncident T (.inl x)).card) =
        1 + 2 * (L.erase (G.left e)).card := by
    calc
      (∑ x ∈ L, (G.selectedIncident T (.inl x)).card) =
          (G.selectedIncident T (.inl (G.left e))).card +
            ∑ x ∈ L.erase (G.left e),
              (G.selectedIncident T (.inl x)).card :=
        (Finset.add_sum_erase L
          (fun x => (G.selectedIncident T (.inl x)).card) hleL).symm
      _ = 1 + ∑ x ∈ L.erase (G.left e),
              (G.selectedIncident T (.inl x)).card := by rw [hdegE]
      _ = 1 + ∑ _x ∈ L.erase (G.left e), 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        have hxL : x ∈ L := Finset.mem_of_mem_erase hx
        have hxe : x ≠ G.left e := Finset.ne_of_mem_erase hx
        have hxf : x ≠ G.left f := by
          intro hxf
          subst x
          exact hlfNot hxL
        simpa [T] using
          hS.factorDeleteRightRoot_left_card_two he hf hef hxe hxf
      _ = 1 + 2 * (L.erase (G.left e)).card := by
        simp [Nat.mul_comm]
  have hsumR :
      (∑ y ∈ R, (G.selectedIncident T (.inr y)).card) = 2 * R.card := by
    calc
      (∑ y ∈ R, (G.selectedIncident T (.inr y)).card) =
          ∑ _y ∈ R, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyr : y ≠ r := by
          intro hyr
          subst y
          have hreach :
              G.FactorReachable T (.inl (G.left e)) (.inr r) :=
            (G.mem_factorComponentRight T (.inl (G.left e)) r).1 hy
          have heq : (Sum.inl (G.left e) : X ⊕ Y) = Sum.inr r :=
            hreach.eq_of_target_isolated (by
              simpa [T] using
                G.selectedIncident_factorDeleteRoot_root S (.inr r))
          simpa using heq
        simpa [T] using hS.factorDeleteRightRoot_right_card_two hyr
      _ = 2 * R.card := by simp [Nat.mul_comm]
  have hbal :
      (∑ x ∈ L, (G.selectedIncident T (.inl x)).card) =
        ∑ y ∈ R, (G.selectedIncident T (.inr y)).card := by
    simpa [L, R] using
      G.factorComponent_degree_sum_balance T (.inl (G.left e))
  rw [hsumL, hsumR] at hbal
  omega

end BipartiteMultigraph
end BachThesisLean
