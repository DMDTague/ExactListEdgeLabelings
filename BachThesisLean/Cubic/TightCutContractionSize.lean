import BachThesisLean.Cubic.TightCutContraction

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Size of explicit tight-cut contractions

A contraction retains exactly one cut shore and replaces the opposite shore by
one new root.  These explicit equivalences make the resulting vertex counts
transparent and prove the strict size decrease used by tight-cut induction.
-/

/-- Total number of vertices in the two shores. -/
def vertexCard (G : BipartiteMultigraph X Y E) : ℕ :=
  Fintype.card X + Fintype.card Y

/-- The vertices of `G / Wᶜ` are exactly the vertices of `W`, together with
one contraction root. -/
def contractComplementVerticesEquiv (W : Finset (X ⊕ Y)) :
    (ContractComplementLeft X Y W ⊕ ContractComplementRight X Y W) ≃
      ({a : X ⊕ Y // a ∈ W} ⊕ Unit) where
  toFun
    | .inl (.inl x) => .inl ⟨.inl x.1, x.2⟩
    | .inl (.inr u) => .inr u
    | .inr y => .inl ⟨.inr y.1, y.2⟩
  invFun
    | .inl ⟨.inl x, hx⟩ => .inl (.inl ⟨x, hx⟩)
    | .inl ⟨.inr y, hy⟩ => .inr ⟨y, hy⟩
    | .inr u => .inl (.inr u)
  left_inv z := by
    rcases z with (x | u) | y <;> rfl
  right_inv z := by
    rcases z with ⟨a, ha⟩ | u
    · rcases a with x | y <;> rfl
    · rfl

/-- The vertices of `G / W` are exactly the vertices outside `W`, together
with one contraction root. -/
def contractSetVerticesEquiv (W : Finset (X ⊕ Y)) :
    (ContractSetLeft X Y W ⊕ ContractSetRight X Y W) ≃
      ({a : X ⊕ Y // a ∈ Wᶜ} ⊕ Unit) where
  toFun
    | .inl x => .inl ⟨.inl x.1, Finset.mem_compl.mpr x.2⟩
    | .inr (.inl y) => .inl ⟨.inr y.1, Finset.mem_compl.mpr y.2⟩
    | .inr (.inr u) => .inr u
  invFun
    | .inl ⟨.inl x, hx⟩ => .inl ⟨x, Finset.mem_compl.mp hx⟩
    | .inl ⟨.inr y, hy⟩ => .inr (.inl ⟨y, Finset.mem_compl.mp hy⟩)
    | .inr u => .inr (.inr u)
  left_inv z := by
    rcases z with x | (y | u) <;> rfl
  right_inv z := by
    rcases z with ⟨a, ha⟩ | u
    · rcases a with x | y <;> rfl
    · rfl

@[simp] theorem vertexCard_contractComplement
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    vertexCard (G.contractComplement W) = W.card + 1 := by
  change Fintype.card (ContractComplementLeft X Y W) +
    Fintype.card (ContractComplementRight X Y W) = W.card + 1
  rw [← Fintype.card_sum]
  calc
    Fintype.card (ContractComplementLeft X Y W ⊕ ContractComplementRight X Y W) =
        Fintype.card ({a : X ⊕ Y // a ∈ W} ⊕ Unit) :=
      Fintype.card_congr (contractComplementVerticesEquiv W)
    _ = W.card + 1 := by
      simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_unit]

@[simp] theorem vertexCard_contractSet
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    vertexCard (G.contractSet W) = Wᶜ.card + 1 := by
  change Fintype.card (ContractSetLeft X Y W) +
    Fintype.card (ContractSetRight X Y W) = Wᶜ.card + 1
  rw [← Fintype.card_sum]
  calc
    Fintype.card (ContractSetLeft X Y W ⊕ ContractSetRight X Y W) =
        Fintype.card ({a : X ⊕ Y // a ∈ Wᶜ} ⊕ Unit) :=
      Fintype.card_congr (contractSetVerticesEquiv W)
    _ = Wᶜ.card + 1 := by
      simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_unit]

/-- Contracting the complement of a nontrivial cut strictly lowers the total
vertex count. -/
theorem contractComplement_vertexCard_lt
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hnontriv : IsNontrivialCutShore W) :
    vertexCard (G.contractComplement W) < vertexCard G := by
  change 1 < W.card ∧ 1 < Wᶜ.card at hnontriv
  rw [vertexCard_contractComplement]
  change W.card + 1 < Fintype.card X + Fintype.card Y
  have hpartition : W.card + Wᶜ.card = Fintype.card X + Fintype.card Y := by
    simpa only [Fintype.card_sum] using Finset.card_add_card_compl W
  omega

/-- Contracting the set itself also strictly lowers total vertex count. -/
theorem contractSet_vertexCard_lt
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hnontriv : IsNontrivialCutShore W) :
    vertexCard (G.contractSet W) < vertexCard G := by
  change 1 < W.card ∧ 1 < Wᶜ.card at hnontriv
  rw [vertexCard_contractSet]
  change Wᶜ.card + 1 < Fintype.card X + Fintype.card Y
  have hpartition : W.card + Wᶜ.card = Fintype.card X + Fintype.card Y := by
    simpa only [Fintype.card_sum] using Finset.card_add_card_compl W
  omega

end BipartiteMultigraph
end BachThesisLean
