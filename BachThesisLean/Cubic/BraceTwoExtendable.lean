import BachThesisLean.Cubic.BraceStrictHall
import BachThesisLean.Cubic.MatchingCovered

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Two-edge extendability of cubic braces

The strict Hall inequality for braces supplies exactly the two units of slack
needed to reserve the endpoints of two independent edge copies.  Hall is then
applied to a neighbour family that forces each prescribed left endpoint to its
prescribed right endpoint and removes both reserved right endpoints everywhere
else.  The resulting shore bijection is lifted back to actual edge copies.
-/

/-- Erasing two elements can reduce the cardinality of a finite set by at most
two. -/
theorem card_le_erase_erase_add_two {α : Type*} [DecidableEq α]
    (S : Finset α) (a b : α) :
    S.card ≤ ((S.erase a).erase b).card + 2 := by
  have ha : S.card ≤ (S.erase a).card + 1 := by
    by_cases h : a ∈ S
    · have hcard := Finset.card_erase_add_one h
      omega
    · rw [Finset.erase_eq_of_not_mem h]
      omega
  have hb : (S.erase a).card ≤ ((S.erase a).erase b).card + 1 := by
    by_cases h : b ∈ S.erase a
    · have hcard := Finset.card_erase_add_one h
      omega
    · rw [Finset.erase_eq_of_not_mem h]
      omega
  omega

/-- If a finite set omits two distinct ambient elements, there are at least two
more ambient elements than elements of the set. -/
theorem card_add_two_le_of_two_not_mem
    (S : Finset X) (a b : X) (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    S.card + 2 ≤ Fintype.card X := by
  classical
  let T : Finset X := insert a (insert b S)
  have hTcard : T.card = S.card + 2 := by
    simp [T, ha, hb, hab, hab.symm]
  calc
    S.card + 2 = T.card := hTcard.symm
    _ ≤ (Finset.univ : Finset X).card :=
      Finset.card_le_card (Finset.subset_univ T)
    _ = Fintype.card X := by simp

/-- Strict Hall survives deletion of two reserved right endpoints whenever the
left set avoids the two corresponding distinct left endpoints. -/
theorem IsBrace.cubic_hall_condition_avoiding_two_right
    {G : BipartiteMultigraph X Y E} (hbrace : G.IsBrace) (hG : G.IsCubic)
    (e0 e1 : E) (hleft : G.left e0 ≠ G.left e1)
    (S : Finset X) (hx0 : G.left e0 ∉ S) (hx1 : G.left e1 ∉ S) :
    S.card ≤
      (((S.biUnion G.rightNeighborSet).erase (G.right e0)).erase
        (G.right e1)).card := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hroom : S.card + 2 ≤ Fintype.card X :=
      card_add_two_le_of_two_not_mem S (G.left e0) (G.left e1)
        hx0 hx1 hleft
    have hstrict :
        S.card + 2 ≤ (S.biUnion G.rightNeighborSet).card :=
      hbrace.rightNeighbor_union_card_ge_add_two hG S hSne hroom
    have herase :=
      card_le_erase_erase_add_two (S.biUnion G.rightNeighborSet)
        (G.right e0) (G.right e1)
    omega

/-- Right-neighbour family with the endpoints of two independent edge copies
reserved for the prescribed pairs. -/
noncomputable def forcedTwoRightNeighborSet
    (G : BipartiteMultigraph X Y E) (e0 e1 : E) (x : X) : Finset Y :=
  if x = G.left e0 then {G.right e0}
  else if x = G.left e1 then {G.right e1}
  else ((G.rightNeighborSet x).erase (G.right e0)).erase (G.right e1)

/-- The two-edge forced neighbour family satisfies Hall's condition. -/
theorem IsBrace.forcedTwoRightNeighborSet_hall
    {G : BipartiteMultigraph X Y E} (hbrace : G.IsBrace) (hG : G.IsCubic)
    (e0 e1 : E) (hleft : G.left e0 ≠ G.left e1)
    (hright : G.right e0 ≠ G.right e1)
    (S : Finset X) :
    S.card ≤ (S.biUnion (G.forcedTwoRightNeighborSet e0 e1)).card := by
  classical
  let x0 : X := G.left e0
  let x1 : X := G.left e1
  let y0 : Y := G.right e0
  let y1 : Y := G.right e1
  by_cases hx0 : x0 ∈ S
  · by_cases hx1 : x1 ∈ S
    · let T : Finset X := (S.erase x0).erase x1
      let N : Finset Y :=
        ((T.biUnion G.rightNeighborSet).erase y0).erase y1
      have hx0T : G.left e0 ∉ T := by simp [T, x0]
      have hx1T : G.left e1 ∉ T := by simp [T, x1]
      have hT : T.card ≤ N.card := by
        simpa [N, y0, y1] using
          hbrace.cubic_hall_condition_avoiding_two_right hG e0 e1 hleft T
            hx0T hx1T
      have hsub : insert y0 (insert y1 N) ⊆
          S.biUnion (G.forcedTwoRightNeighborSet e0 e1) := by
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · rw [Finset.mem_biUnion]
          refine ⟨x0, hx0, ?_⟩
          simp [forcedTwoRightNeighborSet, x0, y0]
        · rw [Finset.mem_insert] at hy
          rcases hy with rfl | hyN
          · rw [Finset.mem_biUnion]
            refine ⟨x1, hx1, ?_⟩
            simp [forcedTwoRightNeighborSet, x0, x1, y1, hleft.symm]
          · have hyN' :
                y ∈ ((T.biUnion G.rightNeighborSet).erase y0).erase y1 := by
              simpa [N] using hyN
            rw [Finset.mem_erase] at hyN'
            obtain ⟨hy1ne, hyN0⟩ := hyN'
            rw [Finset.mem_erase] at hyN0
            obtain ⟨hy0ne, hyUnion⟩ := hyN0
            rw [Finset.mem_biUnion] at hyUnion
            obtain ⟨x, hxT, hyx⟩ := hyUnion
            have hx1erase := Finset.mem_erase.mp hxT
            have hx0erase := Finset.mem_erase.mp hx1erase.2
            rw [Finset.mem_biUnion]
            refine ⟨x, hx0erase.2, ?_⟩
            simp [forcedTwoRightNeighborSet, x0, x1, y0, y1,
              hx0erase.1, hx1erase.1, hy0ne, hy1ne, hyx]
      have hcard := Finset.card_le_card hsub
      have hy0N : y0 ∉ N := by simp [N]
      have hy1N : y1 ∉ N := by simp [N]
      have hy01 : y0 ≠ y1 := by simpa [y0, y1] using hright
      have hInsert : (insert y0 (insert y1 N)).card = N.card + 2 := by
        simp [hy0N, hy1N, hy01]
      have hx1Erase : x1 ∈ S.erase x0 := by
        simp [hx1, hleft.symm, x0, x1]
      have hErase0 := Finset.card_erase_add_one hx0
      have hErase1 := Finset.card_erase_add_one hx1Erase
      dsimp [T] at hT hErase1
      rw [hInsert] at hcard
      omega
    · let T : Finset X := S.erase x0
      let N : Finset Y :=
        ((T.biUnion G.rightNeighborSet).erase y0).erase y1
      have hx0T : G.left e0 ∉ T := by simp [T, x0]
      have hx1T : G.left e1 ∉ T := by
        intro hx
        exact hx1 ((Finset.mem_erase.mp hx).2)
      have hT : T.card ≤ N.card := by
        simpa [N, y0, y1] using
          hbrace.cubic_hall_condition_avoiding_two_right hG e0 e1 hleft T
            hx0T hx1T
      have hsub : insert y0 N ⊆
          S.biUnion (G.forcedTwoRightNeighborSet e0 e1) := by
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hyN
        · rw [Finset.mem_biUnion]
          refine ⟨x0, hx0, ?_⟩
          simp [forcedTwoRightNeighborSet, x0, y0]
        · have hyN' :
              y ∈ ((T.biUnion G.rightNeighborSet).erase y0).erase y1 := by
            simpa [N] using hyN
          rw [Finset.mem_erase] at hyN'
          obtain ⟨hy1ne, hyN0⟩ := hyN'
          rw [Finset.mem_erase] at hyN0
          obtain ⟨hy0ne, hyUnion⟩ := hyN0
          rw [Finset.mem_biUnion] at hyUnion
          obtain ⟨x, hxT, hyx⟩ := hyUnion
          have hxErase := Finset.mem_erase.mp hxT
          have hxx1 : x ≠ x1 := by
            intro h
            subst x
            exact hx1 hxErase.2
          rw [Finset.mem_biUnion]
          refine ⟨x, hxErase.2, ?_⟩
          simp [forcedTwoRightNeighborSet, x0, x1, y0, y1,
            hxErase.1, hxx1, hy0ne, hy1ne, hyx]
      have hcard := Finset.card_le_card hsub
      have hy0N : y0 ∉ N := by simp [N]
      have hInsert : (insert y0 N).card = N.card + 1 := by simp [hy0N]
      have hErase0 := Finset.card_erase_add_one hx0
      dsimp [T] at hT
      rw [hInsert] at hcard
      omega
  · by_cases hx1 : x1 ∈ S
    · let T : Finset X := S.erase x1
      let N : Finset Y :=
        ((T.biUnion G.rightNeighborSet).erase y0).erase y1
      have hx0T : G.left e0 ∉ T := by
        intro hx
        exact hx0 ((Finset.mem_erase.mp hx).2)
      have hx1T : G.left e1 ∉ T := by simp [T, x1]
      have hT : T.card ≤ N.card := by
        simpa [N, y0, y1] using
          hbrace.cubic_hall_condition_avoiding_two_right hG e0 e1 hleft T
            hx0T hx1T
      have hsub : insert y1 N ⊆
          S.biUnion (G.forcedTwoRightNeighborSet e0 e1) := by
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hyN
        · rw [Finset.mem_biUnion]
          refine ⟨x1, hx1, ?_⟩
          simp [forcedTwoRightNeighborSet, x0, x1, y1, hleft.symm]
        · have hyN' :
              y ∈ ((T.biUnion G.rightNeighborSet).erase y0).erase y1 := by
            simpa [N] using hyN
          rw [Finset.mem_erase] at hyN'
          obtain ⟨hy1ne, hyN0⟩ := hyN'
          rw [Finset.mem_erase] at hyN0
          obtain ⟨hy0ne, hyUnion⟩ := hyN0
          rw [Finset.mem_biUnion] at hyUnion
          obtain ⟨x, hxT, hyx⟩ := hyUnion
          have hxErase := Finset.mem_erase.mp hxT
          have hxx0 : x ≠ x0 := by
            intro h
            subst x
            exact hx0 hxErase.2
          rw [Finset.mem_biUnion]
          refine ⟨x, hxErase.2, ?_⟩
          simp [forcedTwoRightNeighborSet, x0, x1, y0, y1,
            hxx0, hxErase.1, hy0ne, hy1ne, hyx]
      have hcard := Finset.card_le_card hsub
      have hy1N : y1 ∉ N := by simp [N]
      have hInsert : (insert y1 N).card = N.card + 1 := by simp [hy1N]
      have hErase1 := Finset.card_erase_add_one hx1
      dsimp [T] at hT
      rw [hInsert] at hcard
      omega
    · let N : Finset Y :=
        ((S.biUnion G.rightNeighborSet).erase y0).erase y1
      have hN : S.card ≤ N.card := by
        simpa [N, y0, y1, x0, x1] using
          hbrace.cubic_hall_condition_avoiding_two_right hG e0 e1 hleft S
            (by simpa [x0] using hx0) (by simpa [x1] using hx1)
      have hsub : N ⊆ S.biUnion (G.forcedTwoRightNeighborSet e0 e1) := by
        intro y hyN
        have hyN' :
            y ∈ ((S.biUnion G.rightNeighborSet).erase y0).erase y1 := by
          simpa [N] using hyN
        rw [Finset.mem_erase] at hyN'
        obtain ⟨hy1ne, hyN0⟩ := hyN'
        rw [Finset.mem_erase] at hyN0
        obtain ⟨hy0ne, hyUnion⟩ := hyN0
        rw [Finset.mem_biUnion] at hyUnion
        obtain ⟨x, hxS, hyx⟩ := hyUnion
        have hxx0 : x ≠ x0 := by
          intro h
          subst x
          exact hx0 hxS
        have hxx1 : x ≠ x1 := by
          intro h
          subst x
          exact hx1 hxS
        rw [Finset.mem_biUnion]
        refine ⟨x, hxS, ?_⟩
        simp [forcedTwoRightNeighborSet, x0, x1, y0, y1,
          hxx0, hxx1, hy0ne, hy1ne, hyx]
      exact hN.trans (Finset.card_le_card hsub)

/-- Two independent edge copies in a cubic brace extend simultaneously to a
perfect matching. -/
theorem IsBrace.exists_perfectMatching_containing_two_edges
    {G : BipartiteMultigraph X Y E} (hbrace : G.IsBrace) (hG : G.IsCubic)
    (e0 e1 : E) (hleft : G.left e0 ≠ G.left e1)
    (hright : G.right e0 ≠ G.right e1) :
    ∃ P : Finset E, G.IsPerfectMatching P ∧ e0 ∈ P ∧ e1 ∈ P := by
  classical
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x : X => G.forcedTwoRightNeighborSet e0 e1 x)).1
      (hbrace.forcedTwoRightNeighborSet_hall hG e0 e1 hleft hright)
  have hf0 : f (G.left e0) = G.right e0 := by
    have h := hf_mem (G.left e0)
    simpa [forcedTwoRightNeighborSet] using h
  have hf1 : f (G.left e1) = G.right e1 := by
    have h := hf_mem (G.left e1)
    simpa [forcedTwoRightNeighborSet, hleft.symm] using h
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf_inj, G.card_left_eq_card_right_of_cubic hG⟩
  have hedge : ∀ x : X, ∃ e : E,
      G.left e = x ∧ G.right e = f x ∧
        (x = G.left e0 → e = e0) ∧ (x = G.left e1 → e = e1) := by
    intro x
    by_cases hx0 : x = G.left e0
    · subst x
      refine ⟨e0, rfl, hf0.symm, ?_, ?_⟩
      · intro _
        rfl
      · intro h
        exact (hleft h).elim
    · by_cases hx1 : x = G.left e1
      · subst x
        refine ⟨e1, rfl, hf1.symm, ?_, ?_⟩
        · intro h
          exact (hleft h.symm).elim
        · intro _
          rfl
      · have hfx :
          f x ∈ ((G.rightNeighborSet x).erase (G.right e0)).erase
            (G.right e1) := by
          simpa [forcedTwoRightNeighborSet, hx0, hx1] using hf_mem x
        have hmem : f x ∈ G.rightNeighborSet x :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hfx).2).2
        obtain ⟨e, hex, hrightEdge⟩ :=
          (mem_rightNeighborSet G x (f x)).1 hmem
        refine ⟨e, (G.mem_leftIncident x e).1 hex, hrightEdge, ?_, ?_⟩
        · intro h
          exact (hx0 h).elim
        · intro h
          exact (hx1 h).elim
  choose g hg using hedge
  have hgLeft : ∀ x : X, G.left (g x) = x := fun x => (hg x).1
  have hgRight : ∀ x : X, G.right (g x) = f x := fun x => (hg x).2.1
  have hg0 : g (G.left e0) = e0 := (hg (G.left e0)).2.2.1 rfl
  have hg1 : g (G.left e1) = e1 := (hg (G.left e1)).2.2.2 rfl
  let P : Finset E := Finset.univ.image g
  have hP : G.IsPerfectMatching P := by
    intro v
    cases v with
    | inl x =>
        have hset : G.selectedIncident P (.inl x) = {g x} := by
          ext e
          simp only [mem_selectedIncident, Finset.mem_singleton]
          constructor
          · rintro ⟨heP, heInc⟩
            have heImage : e ∈ Finset.univ.image g := by simpa [P] using heP
            obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp heImage
            change G.left (g z) = x at heInc
            have hz : z = x := (hgLeft z).symm.trans heInc
            simpa [hz]
          · intro he
            subst e
            refine ⟨?_, ?_⟩
            · simp [P]
            · exact hgLeft x
        rw [hset]
        simp
    | inr y =>
        obtain ⟨x, hfx⟩ := hf_bij.2 y
        have hset : G.selectedIncident P (.inr y) = {g x} := by
          ext e
          simp only [mem_selectedIncident, Finset.mem_singleton]
          constructor
          · rintro ⟨heP, heInc⟩
            have heImage : e ∈ Finset.univ.image g := by simpa [P] using heP
            obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp heImage
            change G.right (g z) = y at heInc
            have hfzy : f z = y := (hgRight z).symm.trans heInc
            have hfz : f z = f x := hfzy.trans hfx.symm
            have hz : z = x := hf_inj hfz
            simpa [hz]
          · intro he
            subst e
            refine ⟨?_, ?_⟩
            · simp [P]
            · change G.right (g x) = y
              exact (hgRight x).trans hfx
        rw [hset]
        simp
  have he0P : e0 ∈ P := by
    have hgmem : g (G.left e0) ∈ Finset.univ.image g := by simp
    simpa [P, hg0] using hgmem
  have he1P : e1 ∈ P := by
    have hgmem : g (G.left e1) ∈ Finset.univ.image g := by simp
    simpa [P, hg1] using hgmem
  exact ⟨P, hP, he0P, he1P⟩

end BipartiteMultigraph
end BachThesisLean
