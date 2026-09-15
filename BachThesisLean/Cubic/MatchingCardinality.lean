import BachThesisLean.Cubic.Foundations

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Cardinality of perfect matchings

These elementary lemmas count actual edge copies. They are useful when a
three-edge cut is exposed: a perfect matching contains one edge for each
vertex on either shore, even in the presence of parallel copies.
-/

/-- A perfect matching contains exactly one edge copy per left vertex. -/
theorem IsPerfectMatching.card_eq_left
    {G : BipartiteMultigraph X Y E} {P : Finset E}
    (hP : G.IsPerfectMatching P) :
    P.card = Fintype.card X := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_nbij G.left ?_ ?_ ?_
  · intro e he
    simp
  · intro e he f hf hef
    exact (G.isMatching_iff P).1 hP.isMatching e he f hf (.inl (G.left e))
      (by rfl) (by simpa [Incident] using hef.symm)
  · intro x hx
    obtain ⟨e, he, _⟩ := hP.existsUnique_incident (.inl x)
    exact ⟨e, he.1, by simpa [Incident] using he.2⟩

/-- A perfect matching contains exactly one edge copy per right vertex. -/
theorem IsPerfectMatching.card_eq_right
    {G : BipartiteMultigraph X Y E} {P : Finset E}
    (hP : G.IsPerfectMatching P) :
    P.card = Fintype.card Y := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_nbij G.right ?_ ?_ ?_
  · intro e he
    simp
  · intro e he f hf hef
    exact (G.isMatching_iff P).1 hP.isMatching e he f hf (.inr (G.right e))
      (by rfl) (by simpa [Incident] using hef.symm)
  · intro y hy
    obtain ⟨e, he, _⟩ := hP.existsUnique_incident (.inr y)
    exact ⟨e, he.1, by simpa [Incident] using he.2⟩

end BipartiteMultigraph
end BachThesisLean
