import BachThesisLean.Cubic.ForcedHall

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Matching-coveredness of connected cubic bipartite multigraphs

The forced Hall family reserves the two endpoints of a specified edge copy for
one another. Hall then yields a bijection of the shores whose chosen edge at
the reserved left endpoint is literally the specified edge copy. This proves
the standard matching-covered fact used throughout the manuscript's cubic
section without assuming simplicity.
-/

/-- Every edge copy of a finite cubic bipartite multigraph lies in a perfect
matching. Connectedness is not needed for this extension statement. -/
theorem exists_perfectMatching_containing_edge_of_cubic
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (e0 : E) :
    ∃ P : Finset E, G.IsPerfectMatching P ∧ e0 ∈ P := by
  classical
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x : X => G.forcedRightNeighborSet e0 x)).1
      (G.forcedRightNeighborSet_hall hG e0)
  have hf0 : f (G.left e0) = G.right e0 := by
    have h := hf_mem (G.left e0)
    simpa [forcedRightNeighborSet] using h
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf_inj, G.card_left_eq_card_right_of_cubic hG⟩
  have hedge : ∀ x : X, ∃ e : E,
      G.left e = x ∧ G.right e = f x ∧
        (x = G.left e0 → e = e0) := by
    intro x
    by_cases hx : x = G.left e0
    · subst x
      refine ⟨e0, rfl, hf0.symm, ?_⟩
      intro _
      rfl
    · have hfx : f x ∈ (G.rightNeighborSet x).erase (G.right e0) := by
        simpa [forcedRightNeighborSet, hx] using hf_mem x
      have hmem : f x ∈ G.rightNeighborSet x := (Finset.mem_erase.mp hfx).2
      obtain ⟨e, hex, hright⟩ :=
        (mem_rightNeighborSet G x (f x)).1 hmem
      refine ⟨e, (G.mem_leftIncident x e).1 hex, hright, ?_⟩
      intro hxe0
      exact (hx hxe0).elim
  choose g hg using hedge
  have hgLeft : ∀ x : X, G.left (g x) = x := fun x => (hg x).1
  have hgRight : ∀ x : X, G.right (g x) = f x := fun x => (hg x).2.1
  have hg0 : g (G.left e0) = e0 := (hg (G.left e0)).2.2 rfl
  have hg_inj : Function.Injective g := by
    intro x x' hxx'
    have hleft := congrArg G.left hxx'
    exact (hgLeft x).symm.trans (hleft.trans (hgLeft x'))
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
  exact ⟨P, hP, he0P⟩

/-- A connected cubic bipartite multigraph is matching-covered in the exact
edge-copy sense used by the manuscript. -/
theorem isMatchingCovered_of_connected_cubic
    (G : BipartiteMultigraph X Y E) (hconn : G.IsConnected) (hG : G.IsCubic) :
    G.IsMatchingCovered := by
  refine ⟨hconn, G.exists_perfectMatching_of_cubic hG, ?_⟩
  intro e
  exact G.exists_perfectMatching_containing_edge_of_cubic hG e

end BipartiteMultigraph
end BachThesisLean
