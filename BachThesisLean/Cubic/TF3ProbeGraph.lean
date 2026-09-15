import BachThesisLean.Cubic.TF3
import BachThesisLean.Cubic.TightCutContractionSize

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# The two-vertex edge probe

Fix an edge `e = xy` of `G`.  The manuscript's probe deletes `e`, adds a new
left vertex `xi` and a new right vertex `eta`, joins `y` to `xi` and `x` to
`eta`, and puts two parallel copies between `xi` and `eta`.

The four new copies are tagged explicitly.  In particular the two pole copies
remain distinct even though they have identical endpoints.
-/

/-- The four new edge copies of the probe. -/
inductive ProbeFreshEdge where
  | xEta
  | yXi
  | pole0
  | pole1
  deriving DecidableEq

instance : Fintype ProbeFreshEdge where
  elems := {.xEta, .yXi, .pole0, .pole1}
  complete x := by
    cases x <;> simp

abbrev EdgeProbeLeft (X : Type u) := X ⊕ PUnit
abbrev EdgeProbeRight (Y : Type v) := Y ⊕ PUnit
abbrev EdgeProbeEdge (e : E) := {f : E // f ≠ e} ⊕ ProbeFreshEdge

/-- Replace one edge by the manuscript's two-vertex probe gadget. -/
def edgeProbe (G : BipartiteMultigraph X Y E) (e : E) :
    BipartiteMultigraph (EdgeProbeLeft X) (EdgeProbeRight Y) (EdgeProbeEdge e) where
  left
    | .inl f => .inl (G.left f.1)
    | .inr .xEta => .inl (G.left e)
    | .inr .yXi => .inr PUnit.unit
    | .inr .pole0 => .inr PUnit.unit
    | .inr .pole1 => .inr PUnit.unit
  right
    | .inl f => .inl (G.right f.1)
    | .inr .xEta => .inr PUnit.unit
    | .inr .yXi => .inl (G.right e)
    | .inr .pole0 => .inr PUnit.unit
    | .inr .pole1 => .inr PUnit.unit

@[simp] theorem edgeProbe_left_old
    (G : BipartiteMultigraph X Y E) (e : E) (f : {f : E // f ≠ e}) :
    (G.edgeProbe e).left (.inl f) = .inl (G.left f.1) := rfl

@[simp] theorem edgeProbe_right_old
    (G : BipartiteMultigraph X Y E) (e : E) (f : {f : E // f ≠ e}) :
    (G.edgeProbe e).right (.inl f) = .inl (G.right f.1) := rfl

@[simp] theorem edgeProbe_left_xEta
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).left (.inr .xEta) = .inl (G.left e) := rfl

@[simp] theorem edgeProbe_right_xEta
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).right (.inr .xEta) = .inr PUnit.unit := rfl

@[simp] theorem edgeProbe_left_yXi
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).left (.inr .yXi) = .inr PUnit.unit := rfl

@[simp] theorem edgeProbe_right_yXi
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).right (.inr .yXi) = .inl (G.right e) := rfl

@[simp] theorem edgeProbe_left_pole0
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).left (.inr .pole0) = .inr PUnit.unit := rfl

@[simp] theorem edgeProbe_right_pole0
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).right (.inr .pole0) = .inr PUnit.unit := rfl

@[simp] theorem edgeProbe_left_pole1
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).left (.inr .pole1) = .inr PUnit.unit := rfl

@[simp] theorem edgeProbe_right_pole1
    (G : BipartiteMultigraph X Y E) (e : E) :
    (G.edgeProbe e).right (.inr .pole1) = .inr PUnit.unit := rfl

/-- The new left pole vertex `xi`. -/
def probeXi : EdgeProbeLeft X := .inr PUnit.unit

/-- The new right pole vertex `eta`. -/
def probeEta : EdgeProbeRight Y := .inr PUnit.unit

/-- The designated three-block coloring for a target old left vertex `v`.
Old vertices other than `v` form block `0`, `v` is block `1`, and the new
probe vertex `xi` is block `2`.  The old endpoint `left e` witnesses that
block `0` is nonempty when `v` is not an endpoint of `e`. -/
noncomputable def edgeProbeLeftColoring
    (G : BipartiteMultigraph X Y E) (e : E) (v : X)
    (hv : v ≠ G.left e) : ThreeBlockColoring (EdgeProbeLeft X) where
  color
    | .inl x => if x = v then 1 else 0
    | .inr _ => 2
  surjective := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · refine ⟨.inl (G.left e), ?_⟩
      have hne : G.left e ≠ v := Ne.symm hv
      simp [hne]
    · exact ⟨.inl v, by simp⟩
    · exact ⟨.inr PUnit.unit, rfl⟩

@[simp] theorem edgeProbeLeftColoring_old_target
    (G : BipartiteMultigraph X Y E) (e : E) (v : X)
    (hv : v ≠ G.left e) :
    (G.edgeProbeLeftColoring e v hv).color (.inl v) = 1 := by
  simp [edgeProbeLeftColoring]

@[simp] theorem edgeProbeLeftColoring_xi
    (G : BipartiteMultigraph X Y E) (e : E) (v : X)
    (hv : v ≠ G.left e) :
    (G.edgeProbeLeftColoring e v hv).color (probeXi : EdgeProbeLeft X) = 2 := rfl

/-- The probe adds exactly two vertices. -/
theorem edgeProbe_vertexCard
    (G : BipartiteMultigraph X Y E) (e : E) :
    vertexCard (G.edgeProbe e) = vertexCard G + 2 := by
  simp [vertexCard]
  omega

end BipartiteMultigraph
end BachThesisLean
