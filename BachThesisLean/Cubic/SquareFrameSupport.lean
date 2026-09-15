import BachThesisLean.Cubic.SquareFrameFromCorners

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Support of a displayed square

In a simple graph the four cells determined by the two left and two right
square vertices contain exactly the four displayed square copies.  Thus square
membership can be read purely from endpoints.
-/

/-- In a simple graph, an edge copy lies on a displayed square exactly when
its two endpoints are among the two corresponding square-corner sets. -/
theorem not_outsideSquare_iff_endpoints
    (Q : SquareFrame G) (hsimple : G.IsSimple) (e : E) :
    ¬ Q.OutsideSquare e ↔
      G.left e ∈ ({Q.leftVertex false, Q.leftVertex true} : Finset X) ∧
      G.right e ∈ ({Q.rightVertex false, Q.rightVertex true} : Finset Y) := by
  classical
  constructor
  · intro h
    simp only [OutsideSquare] at h
    push_neg at h
    obtain ⟨i, j, hij⟩ := h
    subst e
    constructor
    · cases i <;> simp [Q.square_left]
    · cases j <;> simp [Q.square_right]
  · rintro ⟨hl, hr⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
    rcases hl with hl | hl
    · rcases hr with hr | hr
      · intro hout
        apply hout false false
        apply hsimple
        apply Prod.ext
        · exact hl.trans (Q.square_left false false).symm
        · exact hr.trans (Q.square_right false false).symm
      · intro hout
        apply hout false true
        apply hsimple
        apply Prod.ext
        · exact hl.trans (Q.square_left false true).symm
        · exact hr.trans (Q.square_right false true).symm
    · rcases hr with hr | hr
      · intro hout
        apply hout true false
        apply hsimple
        apply Prod.ext
        · exact hl.trans (Q.square_left true false).symm
        · exact hr.trans (Q.square_right true false).symm
      · intro hout
        apply hout true true
        apply hsimple
        apply Prod.ext
        · exact hl.trans (Q.square_left true true).symm
        · exact hr.trans (Q.square_right true true).symm

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
