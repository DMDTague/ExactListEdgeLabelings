import BachThesisLean.Cubic.RegularMatching

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Hall inequalities with one prescribed edge

To put a specified edge copy into a perfect matching, its left and right
endpoints are reserved for one another.  The only nontrivial Hall estimate is
therefore on left-vertex sets avoiding that left endpoint.  Edge-copy counting
gives the needed strict capacity at the reserved right endpoint: one of its
three incident copies is the prescribed edge, so at most two remaining copies
can serve such a set.
-/

/-- If a left set avoids the left endpoint of a prescribed cubic edge, then it
still has at least as many right neighbours after deleting the prescribed
right endpoint. -/
theorem cubic_hall_condition_avoiding_right
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic)
    (e0 : E) (S : Finset X) (hx0 : G.left e0 ∉ S) :
    S.card ≤ ((S.biUnion G.rightNeighborSet).erase (G.right e0)).card := by
  classical
  let y0 : Y := G.right e0
  let F : Finset E := S.biUnion G.leftIncident
  let N : Finset Y := (S.biUnion G.rightNeighborSet).erase y0
  let A : Finset E := N.biUnion G.rightIncident
  let B : Finset E := (G.rightIncident y0).erase e0
  have he0notF : e0 ∉ F := by
    intro he0F
    have he0F' : e0 ∈ S.biUnion G.leftIncident := by simpa [F] using he0F
    rw [Finset.mem_biUnion] at he0F'
    obtain ⟨x, hxS, he0x⟩ := he0F'
    have hxedge : G.left e0 = x := (G.mem_leftIncident x e0).1 he0x
    rw [← hxedge] at hxS
    exact hx0 hxS
  have hsub : F ⊆ A ∪ B := by
    intro e heF
    have heF' : e ∈ S.biUnion G.leftIncident := by simpa [F] using heF
    rw [Finset.mem_biUnion] at heF'
    obtain ⟨x, hxS, hex⟩ := heF'
    by_cases hey0 : G.right e = y0
    · apply Finset.mem_union_right
      dsimp [B]
      rw [Finset.mem_erase]
      refine ⟨?_, (G.mem_rightIncident y0 e).2 hey0⟩
      intro heq
      subst e
      exact he0notF heF
    · apply Finset.mem_union_left
      dsimp [A]
      rw [Finset.mem_biUnion]
      refine ⟨G.right e, ?_, (G.mem_rightIncident (G.right e) e).2 rfl⟩
      dsimp [N]
      rw [Finset.mem_erase]
      refine ⟨hey0, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨x, hxS, ?_⟩
      exact (mem_rightNeighborSet G x (G.right e)).2 ⟨e, hex, rfl⟩
  have hreg := (G.isCubic_iff).1 hG
  have hF : F.card = 3 * S.card := by
    simpa [F] using G.card_biUnion_leftIncident_of_regular hreg.1 S
  have hA : A.card = 3 * N.card := by
    simpa [A] using G.card_biUnion_rightIncident_of_regular hreg.2 N
  have hydeg : (G.rightIncident y0).card = 3 := by
    simpa [rightDegree] using hreg.2 y0
  have he0right : e0 ∈ G.rightIncident y0 := by
    exact (G.mem_rightIncident y0 e0).2 rfl
  have hB : B.card = 2 := by
    dsimp [B]
    rw [Finset.card_erase_of_mem he0right, hydeg]
  have hc : F.card ≤ A.card + B.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  rw [hF, hA, hB] at hc
  change S.card ≤ N.card
  omega

/-- The right-neighbour family with the endpoints of `e0` reserved for each
other. -/
noncomputable def forcedRightNeighborSet
    (G : BipartiteMultigraph X Y E) (e0 : E) (x : X) : Finset Y :=
  if x = G.left e0 then {G.right e0}
  else (G.rightNeighborSet x).erase (G.right e0)

/-- The forced neighbour family satisfies Hall's condition. -/
theorem forcedRightNeighborSet_hall
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (e0 : E)
    (S : Finset X) :
    S.card ≤ (S.biUnion (G.forcedRightNeighborSet e0)).card := by
  classical
  let x0 : X := G.left e0
  let y0 : Y := G.right e0
  by_cases hx0 : x0 ∈ S
  · let T : Finset X := S.erase x0
    let N : Finset Y := (T.biUnion G.rightNeighborSet).erase y0
    have hx0T : G.left e0 ∉ T := by simp [T, x0]
    have hT : T.card ≤ N.card := by
      simpa [N, y0] using G.cubic_hall_condition_avoiding_right hG e0 T hx0T
    have hsub : insert y0 N ⊆ S.biUnion (G.forcedRightNeighborSet e0) := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hyN
      · rw [Finset.mem_biUnion]
        refine ⟨x0, hx0, ?_⟩
        simp [forcedRightNeighborSet, x0, y0]
      · have hyN' : y ∈ (T.biUnion G.rightNeighborSet).erase y0 := by
          simpa [N] using hyN
        rw [Finset.mem_erase] at hyN'
        obtain ⟨hyne, hyUnion⟩ := hyN'
        rw [Finset.mem_biUnion] at hyUnion
        obtain ⟨x, hxT, hyx⟩ := hyUnion
        have hxErase := (Finset.mem_erase.mp hxT)
        rw [Finset.mem_biUnion]
        refine ⟨x, hxErase.2, ?_⟩
        simp [forcedRightNeighborSet, x0, y0, hxErase.1, hyne, hyx]
    have hcard := Finset.card_le_card hsub
    have hy0N : y0 ∉ N := by simp [N]
    have hS := Finset.card_erase_add_one hx0
    have hInsert : (insert y0 N).card = N.card + 1 := by simp [hy0N]
    dsimp [T] at hT
    rw [hInsert] at hcard
    omega
  · let N : Finset Y := (S.biUnion G.rightNeighborSet).erase y0
    have hN : S.card ≤ N.card := by
      simpa [N, y0, x0] using
        G.cubic_hall_condition_avoiding_right hG e0 S (by simpa [x0] using hx0)
    have hsub : N ⊆ S.biUnion (G.forcedRightNeighborSet e0) := by
      intro y hyN
      have hyN' : y ∈ (S.biUnion G.rightNeighborSet).erase y0 := by
        simpa [N] using hyN
      rw [Finset.mem_erase] at hyN'
      obtain ⟨hyne, hyUnion⟩ := hyN'
      rw [Finset.mem_biUnion] at hyUnion
      obtain ⟨x, hxS, hyx⟩ := hyUnion
      have hxne : x ≠ x0 := by
        intro hxx0
        subst x
        exact hx0 hxS
      rw [Finset.mem_biUnion]
      refine ⟨x, hxS, ?_⟩
      simp [forcedRightNeighborSet, x0, y0, hxne, hyne, hyx]
    exact hN.trans (Finset.card_le_card hsub)

end BipartiteMultigraph
end BachThesisLean
