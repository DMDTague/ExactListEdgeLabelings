import BachThesisLean.Cubic.PfaffianSpanning

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Smoothing a three-edge odd path

The Pfaffian closure argument smooths an odd path

`u -- z -- w -- v`

whose two internal vertices `z` and `w` have degree two.  This file records the
local path data and defines the smoothed bipartite multigraph obtained by
deleting `z,w` and replacing the three path copies by one *fresh tagged edge*
from `u` to `v`.  The tag is essential in the multigraph model: the new copy is
kept distinct even when an old parallel `u-v` copy already exists.

The Pfaffian-signing transport is proved in the subsequent smoothing modules;
here we establish only the edge-copy-safe graph operation and its endpoint
bookkeeping.
-/

/-- Local data for a three-edge odd path with saturated degree-two internal
vertices.  `z_saturated` and `w_saturated` are the exact local form of the
hypothesis that the internal vertices have no incident copies besides the two
shown path copies. -/
structure OddPathFrame (G : BipartiteMultigraph X Y E) where
  u : X
  z : Y
  w : X
  v : Y
  uz : E
  wz : E
  wv : E
  u_ne_w : u ≠ w
  v_ne_z : v ≠ z
  uz_left : G.left uz = u
  uz_right : G.right uz = z
  wz_left : G.left wz = w
  wz_right : G.right wz = z
  wv_left : G.left wv = w
  wv_right : G.right wv = v
  uz_ne_wz : uz ≠ wz
  wz_ne_wv : wz ≠ wv
  uz_ne_wv : uz ≠ wv
  z_saturated : ∀ e : E, G.right e = z → e = uz ∨ e = wz
  w_saturated : ∀ e : E, G.left e = w → e = wz ∨ e = wv

namespace OddPathFrame

variable (Q : OddPathFrame G)

/-- Old copies surviving the smoothing have neither deleted internal endpoint. -/
def Survives (e : E) : Prop := G.left e ≠ Q.w ∧ G.right e ≠ Q.z

abbrev Survivor := {e : E // Q.Survives e}
abbrev ReducedLeft := {x : X // x ≠ Q.w}
abbrev ReducedRight := {y : Y // y ≠ Q.z}
abbrev SmoothEdge := Q.Survivor ⊕ Unit

noncomputable instance : Fintype Q.Survivor := Fintype.ofFinite _
noncomputable instance : Fintype Q.ReducedLeft := Fintype.ofFinite _
noncomputable instance : Fintype Q.ReducedRight := Fintype.ofFinite _
noncomputable instance : Fintype Q.SmoothEdge := Fintype.ofFinite _

instance : DecidableEq Q.Survivor := inferInstance
instance : DecidableEq Q.ReducedLeft := inferInstance
instance : DecidableEq Q.ReducedRight := inferInstance
instance : DecidableEq Q.SmoothEdge := inferInstance

@[simp] theorem survives_iff (e : E) :
    Q.Survives e ↔ G.left e ≠ Q.w ∧ G.right e ≠ Q.z := Iff.rfl

/-- The first path copy is removed because its right endpoint is `z`. -/
theorem uz_not_survives : ¬ Q.Survives Q.uz := by
  intro h
  exact h.2 Q.uz_right

/-- The middle path copy is removed at both internal endpoints. -/
theorem wz_not_survives : ¬ Q.Survives Q.wz := by
  intro h
  exact h.1 Q.wz_left

/-- The last path copy is removed because its left endpoint is `w`. -/
theorem wv_not_survives : ¬ Q.Survives Q.wv := by
  intro h
  exact h.1 Q.wv_left

/-- The tagged fresh edge in the smoothed edge-copy type. -/
def freshEdge : Q.SmoothEdge := .inr ()

/-- Embedding of surviving old copies into the smoothed edge-copy type. -/
def oldEdge (e : Q.Survivor) : Q.SmoothEdge := .inl e

/-- Canonical embedding of surviving copies back into the original edge-copy
type. -/
def survivorEmbedding : Q.Survivor ↪ E :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Lift a finite collection of surviving copies back to the original edge
copy type. -/
def liftSurvivorSet (S : Finset Q.Survivor) : Finset E :=
  S.map Q.survivorEmbedding

@[simp] theorem mem_liftSurvivorSet_iff
    (S : Finset Q.Survivor) (e : E) :
    e ∈ Q.liftSurvivorSet S ↔ ∃ a ∈ S, a.val = e := by
  simp [liftSurvivorSet, survivorEmbedding]

/-- The smoothed graph deletes the internal shore vertices and adds one fresh
copy from `u` to `v`. -/
def smooth : BipartiteMultigraph Q.ReducedLeft Q.ReducedRight Q.SmoothEdge where
  left
    | .inl e => ⟨G.left e.val, e.property.1⟩
    | .inr _ => ⟨Q.u, Q.u_ne_w⟩
  right
    | .inl e => ⟨G.right e.val, e.property.2⟩
    | .inr _ => ⟨Q.v, Q.v_ne_z⟩

@[simp] theorem smooth_left_old (e : Q.Survivor) :
    Q.smooth.left (Q.oldEdge e) = ⟨G.left e.val, e.property.1⟩ := rfl

@[simp] theorem smooth_right_old (e : Q.Survivor) :
    Q.smooth.right (Q.oldEdge e) = ⟨G.right e.val, e.property.2⟩ := rfl

@[simp] theorem smooth_left_fresh :
    Q.smooth.left Q.freshEdge = ⟨Q.u, Q.u_ne_w⟩ := rfl

@[simp] theorem smooth_right_fresh :
    Q.smooth.right Q.freshEdge = ⟨Q.v, Q.v_ne_z⟩ := rfl

/-- The fresh smoothing copy is never identified with a surviving old copy. -/
theorem freshEdge_ne_old (e : Q.Survivor) : Q.freshEdge ≠ Q.oldEdge e := by
  simp [freshEdge, oldEdge]

/-- Conversely, an old surviving copy is never the fresh smoothing copy. -/
theorem oldEdge_ne_fresh (e : Q.Survivor) : Q.oldEdge e ≠ Q.freshEdge := by
  exact (Q.freshEdge_ne_old e).symm

/-- The old-edge embedding into the smoothed graph is injective. -/
theorem oldEdge_injective : Function.Injective Q.oldEdge := by
  intro a b h
  simpa [oldEdge] using h

/-- Any old copy incident with the deleted right vertex is one of `uz,wz`. -/
theorem right_eq_z_cases {e : E} (h : G.right e = Q.z) :
    e = Q.uz ∨ e = Q.wz :=
  Q.z_saturated e h

/-- Any old copy incident with the deleted left vertex is one of `wz,wv`. -/
theorem left_eq_w_cases {e : E} (h : G.left e = Q.w) :
    e = Q.wz ∨ e = Q.wv :=
  Q.w_saturated e h

/-- Every original edge copy not among the three path copies survives. -/
theorem survives_of_ne_path {e : E}
    (huz : e ≠ Q.uz) (hwz : e ≠ Q.wz) (hwv : e ≠ Q.wv) :
    Q.Survives e := by
  constructor
  · intro hleft
    rcases Q.left_eq_w_cases hleft with h | h
    · exact hwz h
    · exact hwv h
  · intro hright
    rcases Q.right_eq_z_cases hright with h | h
    · exact huz h
    · exact hwz h

/-- Hence the three displayed path copies are exactly the copies removed by the
smoothing operation. -/
theorem not_survives_iff_eq_path (e : E) :
    ¬ Q.Survives e ↔ e = Q.uz ∨ e = Q.wz ∨ e = Q.wv := by
  constructor
  · intro h
    by_contra hpath
    apply h
    apply Q.survives_of_ne_path
    · intro he
      exact hpath (Or.inl he)
    · intro he
      exact hpath (Or.inr (Or.inl he))
    · intro he
      exact hpath (Or.inr (Or.inr he))
  · intro hpath
    rcases hpath with rfl | rfl | rfl
    · exact Q.uz_not_survives
    · exact Q.wz_not_survives
    · exact Q.wv_not_survives

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
