import BachThesisLean.Cubic.Foundations

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Three-block complementary-factor language

For the cubic manuscript, a partition of the left shore into three nonempty
blocks is most conveniently represented by a surjective map to `Fin 3`.  A
tricolored complementary component is then one component of the complement of
a perfect matching that reaches a left vertex of every color.

This file introduces only the vocabulary.  It does not assert the universal
`TF3` conjecture.
-/

/-- A partition into three nonempty labeled blocks, encoded by its color map. -/
structure ThreeBlockColoring (X : Type u) where
  color : X → Fin 3
  surjective : Function.Surjective color

/-- One component of the complement of `P` meets all three left blocks. -/
def HasTricoloredComplement
    (G : BipartiteMultigraph X Y E) (c : ThreeBlockColoring X) : Prop :=
  ∃ P : Finset E, ∃ root : X ⊕ Y,
    G.IsPerfectMatching P ∧
      ∀ i : Fin 3, ∃ x : X,
        c.color x = i ∧ G.FactorReachable Pᶜ root (.inl x)

/-- The cubic three-block factor property `TF3` on a fixed graph. -/
def HasTF3 (G : BipartiteMultigraph X Y E) : Prop :=
  ∀ c : ThreeBlockColoring X, G.HasTricoloredComplement c

/-- A tricolored complementary witness carries one chosen vertex of any
prescribed color. -/
theorem HasTricoloredComplement.exists_reachable_color
    {G : BipartiteMultigraph X Y E} {c : ThreeBlockColoring X}
    (h : G.HasTricoloredComplement c) (i : Fin 3) :
    ∃ P : Finset E, ∃ root : X ⊕ Y, ∃ x : X,
      G.IsPerfectMatching P ∧ c.color x = i ∧
        G.FactorReachable Pᶜ root (.inl x) := by
  obtain ⟨P, root, hP, hall⟩ := h
  obtain ⟨x, hx, hreach⟩ := hall i
  exact ⟨P, root, x, hP, hx, hreach⟩

/-- On a cubic graph the selected complement in every `TF3` witness is a
spanning two-factor, matching the manuscript's formulation. -/
theorem HasTricoloredComplement.exists_twoFactor
    {G : BipartiteMultigraph X Y E} (hG : G.IsCubic)
    {c : ThreeBlockColoring X} (h : G.HasTricoloredComplement c) :
    ∃ H : Finset E, G.IsTwoFactor H ∧
      ∃ root : X ⊕ Y,
        ∀ i : Fin 3, ∃ x : X,
          c.color x = i ∧ G.FactorReachable H root (.inl x) := by
  obtain ⟨P, root, hP, hall⟩ := h
  refine ⟨Pᶜ, ?_, root, hall⟩
  exact (G.perfectMatching_compl_iff_twoFactor hG P).1 hP

end BipartiteMultigraph
end BachThesisLean
