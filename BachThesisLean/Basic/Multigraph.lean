import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image

namespace BachThesisLean

universe u v w

/-!
## Finite edge-copy bipartite multigraphs

The edge type is an actual type of edge copies. Consequently two edges with
the same endpoints are still different edges, which is essential for the
counting conventions in the capstone.
-/

structure BipartiteMultigraph (X : Type u) (Y : Type v) (E : Type w) where
  left : E → X
  right : E → Y

namespace BipartiteMultigraph

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]

noncomputable def leftIncident
    (G : BipartiteMultigraph X Y E) (x : X) : Finset E :=
  by
    classical
    exact Finset.univ.filter (fun e => G.left e = x)

noncomputable def rightIncident
    (G : BipartiteMultigraph X Y E) (y : Y) : Finset E :=
  by
    classical
    exact Finset.univ.filter (fun e => G.right e = y)

@[simp] theorem mem_leftIncident
    (G : BipartiteMultigraph X Y E) (x : X) (e : E) :
    e ∈ G.leftIncident x ↔ G.left e = x := by
  classical
  simp [leftIncident]

@[simp] theorem mem_rightIncident
    (G : BipartiteMultigraph X Y E) (y : Y) (e : E) :
    e ∈ G.rightIncident y ↔ G.right e = y := by
  classical
  simp [rightIncident]

noncomputable def leftDegree
    (G : BipartiteMultigraph X Y E) (x : X) : ℕ :=
  (G.leftIncident x).card

noncomputable def rightDegree
    (G : BipartiteMultigraph X Y E) (y : Y) : ℕ :=
  (G.rightIncident y).card

def IsLeftRegular
    (G : BipartiteMultigraph X Y E) (k : ℕ) : Prop :=
  ∀ x, G.leftDegree x = k

def IsRightRegular
    (G : BipartiteMultigraph X Y E) (k : ℕ) : Prop :=
  ∀ y, G.rightDegree y = k

theorem leftDegree_eq_card
    (G : BipartiteMultigraph X Y E) (x : X) :
    G.leftDegree x = (G.leftIncident x).card := rfl

theorem rightDegree_eq_card
    (G : BipartiteMultigraph X Y E) (y : Y) :
    G.rightDegree y = (G.rightIncident y).card := rfl

end BipartiteMultigraph
end BachThesisLean
