import BachThesisLean.Cubic.SquareSmoothingDeletion
import BachThesisLean.Cubic.TightCutContractionSize

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Size decrease under square smoothing

The vertex type of either smoothing is independent of the terminal pairing: it
is exactly the original vertex set with the four displayed square vertices
deleted.  The explicit equivalence below is enough to make the strict size
decrease used by minimal-counterexample induction kernel-visible.
-/

/-- Reduced smoothing vertices are exactly original vertices outside the
square. -/
def reducedVerticesEquiv :
    (Q.ReducedLeft ⊕ Q.ReducedRight) ≃
      {v : X ⊕ Y // v ∈ Q.squareVerticesᶜ} where
  toFun v :=
    ⟨Q.liftVertex v,
      Finset.mem_compl.mpr (Q.liftVertex_not_mem_squareVertices v)⟩
  invFun v := by
    rcases v with ⟨v, hv⟩
    have hvout : v ∉ Q.squareVertices := Finset.mem_compl.mp hv
    cases v with
    | inl x =>
        refine .inl ⟨x, ?_⟩
        intro i hxi
        apply hvout
        exact (Q.mem_squareVertices_inl x).2 ⟨i, hxi⟩
    | inr y =>
        refine .inr ⟨y, ?_⟩
        intro i hyi
        apply hvout
        exact (Q.mem_squareVertices_inr y).2 ⟨i, hyi⟩
  left_inv v := by
    rcases v with x | y <;> rfl
  right_inv v := by
    rcases v with ⟨v, hv⟩
    apply Subtype.ext
    rcases v with x | y <;> rfl

/-- The total vertex count of either smoothing is the cardinality of the
complement of the four square vertices. -/
@[simp] theorem vertexCard_smooth (swap : Bool) :
    vertexCard (Q.smooth swap) = Q.squareVerticesᶜ.card := by
  change Fintype.card Q.ReducedLeft + Fintype.card Q.ReducedRight =
    Q.squareVerticesᶜ.card
  rw [← Fintype.card_sum]
  calc
    Fintype.card (Q.ReducedLeft ⊕ Q.ReducedRight) =
        Fintype.card {v : X ⊕ Y // v ∈ Q.squareVerticesᶜ} :=
      Fintype.card_congr Q.reducedVerticesEquiv
    _ = Q.squareVerticesᶜ.card := Fintype.card_coe _

/-- The displayed square is nonempty (indeed it has four vertices). -/
theorem squareVertices_nonempty : Q.squareVertices.Nonempty := by
  exact ⟨.inl (Q.leftVertex false),
    (Q.mem_squareVertices_inl (Q.leftVertex false)).2 ⟨false, rfl⟩⟩

/-- Every square smoothing has strictly fewer total vertices than the original
graph. -/
theorem smooth_vertexCard_lt (swap : Bool) :
    vertexCard (Q.smooth swap) < vertexCard G := by
  rw [Q.vertexCard_smooth]
  change Q.squareVerticesᶜ.card < Fintype.card X + Fintype.card Y
  have hpartition := Finset.card_add_card_compl Q.squareVertices
  have hpositive : 0 < Q.squareVertices.card :=
    Finset.card_pos.mpr Q.squareVertices_nonempty
  have hpartition' :
      Q.squareVertices.card + Q.squareVerticesᶜ.card =
        Fintype.card X + Fintype.card Y := by
    simpa only [Fintype.card_sum] using hpartition
  omega

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
