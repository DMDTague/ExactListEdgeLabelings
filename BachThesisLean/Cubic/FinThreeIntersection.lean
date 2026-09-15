import BachThesisLean.Cubic.PortMasks

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# Three-port finite-set bookkeeping

Two subsets of a three-element port set, each of size at least two, must
intersect.  We also record that pulling a port set back along a permutation
preserves its cardinality.
-/

/-- Pull a set of three ports back along a permutation. -/
noncomputable def finThreePermPreimage
    (σ : Equiv.Perm (Fin 3)) (S : Finset (Fin 3)) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun i => σ i ∈ S)

@[simp] theorem mem_finThreePermPreimage
    (σ : Equiv.Perm (Fin 3)) (S : Finset (Fin 3)) (i : Fin 3) :
    i ∈ finThreePermPreimage σ S ↔ σ i ∈ S := by
  classical
  simp [finThreePermPreimage]

/-- A permutation does not change the size of a port set. -/
theorem card_finThreePermPreimage
    (σ : Equiv.Perm (Fin 3)) (S : Finset (Fin 3)) :
    (finThreePermPreimage σ S).card = S.card := by
  classical
  refine Finset.card_nbij σ ?_ ?_ ?_
  · intro i hi
    exact (mem_finThreePermPreimage σ S i).1 hi
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ.symm j, ?_, ?_⟩
    · exact (mem_finThreePermPreimage σ S (σ.symm j)).2 (by simpa)
    · simp

/-- Any two subsets of `Fin 3` of cardinality at least two intersect. -/
theorem finThree_inter_nonempty_of_card_ge_two
    (S T : Finset (Fin 3)) (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) :
    (S ∩ T).Nonempty := by
  classical
  by_contra hnone
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    apply hnone
    exact ⟨i, by simp [hiS, hiT]⟩
  have hunion : (S ∪ T).card = S.card + T.card :=
    Finset.card_union_of_disjoint hdisj
  have hle : (S ∪ T).card ≤ 3 := by
    calc
      (S ∪ T).card ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card (by simp)
      _ = 3 := by decide
  rw [hunion] at hle
  omega

/-- A size-two mask intersects the inverse-permuted image of another
size-two mask. -/
theorem finThree_inter_permPreimage_nonempty_of_card_ge_two
    (σ : Equiv.Perm (Fin 3)) (S T : Finset (Fin 3))
    (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) :
    (S ∩ finThreePermPreimage σ T).Nonempty := by
  apply finThree_inter_nonempty_of_card_ge_two S (finThreePermPreimage σ T) hS
  simpa [card_finThreePermPreimage] using hT

end BipartiteMultigraph
end BachThesisLean
