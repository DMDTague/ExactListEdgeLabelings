import BachThesisLean.Cubic.TwoFactorRootPath

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Left-root version of the two-factor root-deletion path

This is the shore-dual of `TwoFactorRootPath.lean`.  It is kept explicit rather
than hidden behind a graph-transpose construction so that the later star-product
splicing proof can use the source endpoint maps without transport boilerplate.
-/

/-- At one endpoint of a deleted left-root edge, the residual selected degree
is one, provided the other root edge has a different right endpoint. -/
theorem IsTwoFactor.factorDeleteLeftRoot_endpoint_card_one
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {ell : X} {e f : E}
    (he : e ∈ G.selectedIncident S (.inl ell))
    (hf : f ∈ G.selectedIncident S (.inl ell)) (hef : e ≠ f)
    (hright : G.right e ≠ G.right f) :
    (G.selectedIncident (G.factorDeleteRoot S (.inl ell))
      (.inr (G.right e))).card = 1 := by
  classical
  have hroot := hS.selectedIncident_eq_pair he hf hef
  have heS : e ∈ S := ((G.mem_selectedIncident S (.inl ell) e).1 he).1
  have heRight : e ∈ G.selectedIncident S (.inr (G.right e)) :=
    (G.mem_selectedIncident S (.inr (G.right e)) e).2 ⟨heS, rfl⟩
  have hEq :
      G.selectedIncident (G.factorDeleteRoot S (.inl ell)) (.inr (G.right e)) =
        (G.selectedIncident S (.inr (G.right e))).erase e := by
    ext g
    simp only [mem_selectedIncident, mem_factorDeleteRoot, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hgS, hgNotRoot⟩, hgRight⟩
      refine ⟨?_, ⟨hgS, hgRight⟩⟩
      intro hge
      subst g
      exact hgNotRoot ((G.mem_selectedIncident S (.inl ell) e).1 he)
    · rintro ⟨hgne, ⟨hgS, hgRight⟩⟩
      refine ⟨⟨hgS, ?_⟩, hgRight⟩
      intro hgRoot
      have hgRootMem : g ∈ G.selectedIncident S (.inl ell) :=
        (G.mem_selectedIncident S (.inl ell) g).2 hgRoot
      have hgPair : g = e ∨ g = f := by
        rw [hroot] at hgRootMem
        simpa using hgRootMem
      rcases hgPair with hge | hgf
      · exact hgne hge
      · subst g
        change G.right f = G.right e at hgRight
        exact hright hgRight.symm
  rw [hEq, Finset.card_erase_of_mem heRight, hS (.inr (G.right e))]

/-- Away from both right endpoints of the deleted left-root edges, residual
selected degree stays two. -/
theorem IsTwoFactor.factorDeleteLeftRoot_right_card_two
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {ell : X} {e f : E}
    (he : e ∈ G.selectedIncident S (.inl ell))
    (hf : f ∈ G.selectedIncident S (.inl ell)) (hef : e ≠ f)
    {y : Y} (hye : y ≠ G.right e) (hyf : y ≠ G.right f) :
    (G.selectedIncident (G.factorDeleteRoot S (.inl ell)) (.inr y)).card = 2 := by
  classical
  have hroot := hS.selectedIncident_eq_pair he hf hef
  have hEq :
      G.selectedIncident (G.factorDeleteRoot S (.inl ell)) (.inr y) =
        G.selectedIncident S (.inr y) := by
    ext g
    simp only [mem_selectedIncident, mem_factorDeleteRoot]
    constructor
    · rintro ⟨⟨hgS, _⟩, hgRight⟩
      exact ⟨hgS, hgRight⟩
    · rintro ⟨hgS, hgRight⟩
      refine ⟨⟨hgS, ?_⟩, hgRight⟩
      intro hgRoot
      have hgRootMem : g ∈ G.selectedIncident S (.inl ell) :=
        (G.mem_selectedIncident S (.inl ell) g).2 hgRoot
      have hgPair : g = e ∨ g = f := by
        rw [hroot] at hgRootMem
        simpa using hgRootMem
      rcases hgPair with hge | hgf
      · subst g
        change G.right e = y at hgRight
        exact hye hgRight.symm
      · subst g
        change G.right f = y at hgRight
        exact hyf hgRight.symm
  rw [hEq, hS (.inr y)]

/-- Deleting a left root does not change selected degree at any other left
vertex. -/
theorem IsTwoFactor.factorDeleteLeftRoot_left_card_two
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {ell x : X} (hxe : x ≠ ell) :
    (G.selectedIncident (G.factorDeleteRoot S (.inl ell)) (.inl x)).card = 2 := by
  classical
  have hEq :
      G.selectedIncident (G.factorDeleteRoot S (.inl ell)) (.inl x) =
        G.selectedIncident S (.inl x) := by
    ext g
    simp only [mem_selectedIncident, mem_factorDeleteRoot]
    constructor
    · rintro ⟨⟨hgS, _⟩, hgLeft⟩
      exact ⟨hgS, hgLeft⟩
    · rintro ⟨hgS, hgLeft⟩
      refine ⟨⟨hgS, ?_⟩, hgLeft⟩
      intro hgRoot
      have hgRoot' := hgRoot.2
      change G.left g = ell at hgRoot'
      change G.left g = x at hgLeft
      exact hxe (hgLeft.symm.trans hgRoot')
  rw [hEq, hS (.inl x)]

/-- Left-root form of the manuscript's path-after-root-deletion statement. -/
theorem IsTwoFactor.factorDeleteLeftRoot_reaches_between_ports
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {ell : X} {e f : E}
    (he : e ∈ G.selectedIncident S (.inl ell))
    (hf : f ∈ G.selectedIncident S (.inl ell)) :
    G.FactorReachable (G.factorDeleteRoot S (.inl ell))
      (.inr (G.right e)) (.inr (G.right f)) := by
  classical
  by_cases hef : e = f
  · subst f
    exact G.factorReachable_refl _ _
  by_cases hright : G.right e = G.right f
  · simpa [hright] using
      (G.factorReachable_refl (G.factorDeleteRoot S (.inl ell)) (.inr (G.right e)))
  let T := G.factorDeleteRoot S (.inl ell)
  let L := G.factorComponentLeft T (.inr (G.right e))
  let R := G.factorComponentRight T (.inr (G.right e))
  by_contra hnot
  have hreR : G.right e ∈ R := by
    apply (G.mem_factorComponentRight T (.inr (G.right e)) (G.right e)).2
    exact G.factorReachable_refl T _
  have hrfNot : G.right f ∉ R := by
    intro hmem
    apply hnot
    exact (G.mem_factorComponentRight T (.inr (G.right e)) (G.right f)).1 hmem
  have hdegE :
      (G.selectedIncident T (.inr (G.right e))).card = 1 := by
    simpa [T] using
      hS.factorDeleteLeftRoot_endpoint_card_one he hf hef hright
  have hsumR :
      (∑ y ∈ R, (G.selectedIncident T (.inr y)).card) =
        1 + 2 * (R.erase (G.right e)).card := by
    calc
      (∑ y ∈ R, (G.selectedIncident T (.inr y)).card) =
          (G.selectedIncident T (.inr (G.right e))).card +
            ∑ y ∈ R.erase (G.right e),
              (G.selectedIncident T (.inr y)).card :=
        (Finset.add_sum_erase R
          (fun y => (G.selectedIncident T (.inr y)).card) hreR).symm
      _ = 1 + ∑ y ∈ R.erase (G.right e),
              (G.selectedIncident T (.inr y)).card := by rw [hdegE]
      _ = 1 + ∑ _y ∈ R.erase (G.right e), 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        have hyR : y ∈ R := Finset.mem_of_mem_erase hy
        have hye : y ≠ G.right e := Finset.ne_of_mem_erase hy
        have hyf : y ≠ G.right f := by
          intro hyf
          subst y
          exact hrfNot hyR
        simpa [T] using
          hS.factorDeleteLeftRoot_right_card_two he hf hef hye hyf
      _ = 1 + 2 * (R.erase (G.right e)).card := by
        simp [Nat.mul_comm]
  have hsumL :
      (∑ x ∈ L, (G.selectedIncident T (.inl x)).card) = 2 * L.card := by
    calc
      (∑ x ∈ L, (G.selectedIncident T (.inl x)).card) =
          ∑ _x ∈ L, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxell : x ≠ ell := by
          intro hxell
          subst x
          have hreach :
              G.FactorReachable T (.inr (G.right e)) (.inl ell) :=
            (G.mem_factorComponentLeft T (.inr (G.right e)) ell).1 hx
          have heq : (Sum.inr (G.right e) : X ⊕ Y) = Sum.inl ell :=
            hreach.eq_of_target_isolated (by
              simpa [T] using
                G.selectedIncident_factorDeleteRoot_root S (.inl ell))
          simpa using heq
        simpa [T] using hS.factorDeleteLeftRoot_left_card_two hxell
      _ = 2 * L.card := by simp [Nat.mul_comm]
  have hbal :
      (∑ x ∈ L, (G.selectedIncident T (.inl x)).card) =
        ∑ y ∈ R, (G.selectedIncident T (.inr y)).card := by
    simpa [L, R] using
      G.factorComponent_degree_sum_balance T (.inr (G.right e))
  rw [hsumL, hsumR] at hbal
  omega

end BipartiteMultigraph
end BachThesisLean
