import BachThesisLean.Cubic.OddPathSmoothing

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Perfect-matching lift through odd-path smoothing

A smooth matching has two local states.  If the fresh `u-v` copy is selected,
its lift uses the two outer path copies `u-z` and `w-v`.  If the fresh copy is
not selected, the lift instead uses the middle copy `w-z`.  Surviving old
copies are lifted unchanged.
-/

/-- Whether the fresh smoothing copy is selected. -/
def freshSelected (S : Finset Q.SmoothEdge) : Prop := Q.freshEdge ∈ S

/-- Lift a selected edge set from the smoothing to actual old edge copies. -/
noncomputable def liftMatchingSet (S : Finset Q.SmoothEdge) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    (∃ h : Q.Survives e, Q.oldEdge ⟨e, h⟩ ∈ S) ∨
    (e = Q.uz ∧ Q.freshSelected S) ∨
    (e = Q.wv ∧ Q.freshSelected S) ∨
    (e = Q.wz ∧ ¬ Q.freshSelected S)

theorem mem_liftMatchingSet (S : Finset Q.SmoothEdge) (e : E) :
    e ∈ Q.liftMatchingSet S ↔
      (∃ h : Q.Survives e, Q.oldEdge ⟨e, h⟩ ∈ S) ∨
      (e = Q.uz ∧ Q.freshSelected S) ∨
      (e = Q.wv ∧ Q.freshSelected S) ∨
      (e = Q.wz ∧ ¬ Q.freshSelected S) := by
  classical
  simp [liftMatchingSet]

@[simp] theorem mem_liftMatchingSet_old
    (S : Finset Q.SmoothEdge) (e : Q.Survivor) :
    e.val ∈ Q.liftMatchingSet S ↔ Q.oldEdge e ∈ S := by
  rw [Q.mem_liftMatchingSet S e.val]
  constructor
  · rintro (⟨h, he⟩ | ⟨hez, _⟩ | ⟨hev, _⟩ | ⟨hew, _⟩)
    · have hh : (⟨e.val, h⟩ : Q.Survivor) = e := Subtype.ext rfl
      simpa [oldEdge, hh] using he
    · have hs := e.property
      rw [hez] at hs
      exact False.elim (Q.uz_not_survives hs)
    · have hs := e.property
      rw [hev] at hs
      exact False.elim (Q.wv_not_survives hs)
    · have hs := e.property
      rw [hew] at hs
      exact False.elim (Q.wz_not_survives hs)
  · intro he
    exact Or.inl ⟨e.property, by simpa [oldEdge] using he⟩

@[simp] theorem mem_liftMatchingSet_uz (S : Finset Q.SmoothEdge) :
    Q.uz ∈ Q.liftMatchingSet S ↔ Q.freshSelected S := by
  rw [Q.mem_liftMatchingSet S Q.uz]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, hfresh⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · exact False.elim (Q.uz_not_survives h)
    · exact hfresh
    · exact False.elim (Q.uz_ne_wv h)
    · exact False.elim (Q.uz_ne_wz h)
  · intro hfresh
    exact Or.inr (Or.inl ⟨rfl, hfresh⟩)

@[simp] theorem mem_liftMatchingSet_wv (S : Finset Q.SmoothEdge) :
    Q.wv ∈ Q.liftMatchingSet S ↔ Q.freshSelected S := by
  rw [Q.mem_liftMatchingSet S Q.wv]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hfresh⟩ | ⟨h, _⟩)
    · exact False.elim (Q.wv_not_survives h)
    · exact False.elim (Q.uz_ne_wv h.symm)
    · exact hfresh
    · exact False.elim (Q.wz_ne_wv h.symm)
  · intro hfresh
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hfresh⟩))

@[simp] theorem mem_liftMatchingSet_wz (S : Finset Q.SmoothEdge) :
    Q.wz ∈ Q.liftMatchingSet S ↔ ¬ Q.freshSelected S := by
  rw [Q.mem_liftMatchingSet S Q.wz]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hfresh⟩)
    · exact False.elim (Q.wz_not_survives h)
    · exact False.elim (Q.uz_ne_wz h.symm)
    · exact False.elim (Q.wz_ne_wv h)
    · exact hfresh
  · intro hfresh
    exact Or.inr (Or.inr (Or.inr ⟨rfl, hfresh⟩))

/-- Recover the original selected copy seen from a surviving left vertex.  The
fresh edge recovers to the outer path copy `u-z`. -/
def recoverLeft : Q.SmoothEdge → E
  | .inl e => e.val
  | .inr _ => Q.uz

/-- Recover the original selected copy seen from a surviving right vertex.  The
fresh edge recovers to the other outer path copy `w-v`. -/
def recoverRight : Q.SmoothEdge → E
  | .inl e => e.val
  | .inr _ => Q.wv

@[simp] theorem recoverLeft_old (e : Q.Survivor) :
    Q.recoverLeft (Q.oldEdge e) = e.val := rfl

@[simp] theorem recoverRight_old (e : Q.Survivor) :
    Q.recoverRight (Q.oldEdge e) = e.val := rfl

@[simp] theorem recoverLeft_fresh : Q.recoverLeft Q.freshEdge = Q.uz := rfl
@[simp] theorem recoverRight_fresh : Q.recoverRight Q.freshEdge = Q.wv := rfl

/-- Left recovery preserves the left endpoint. -/
theorem recoverLeft_left (a : Q.SmoothEdge) :
    G.left (Q.recoverLeft a) = (Q.smooth.left a).val := by
  rcases a with e | unit
  · rfl
  · cases unit
    exact Q.uz_left

/-- Right recovery preserves the right endpoint. -/
theorem recoverRight_right (a : Q.SmoothEdge) :
    G.right (Q.recoverRight a) = (Q.smooth.right a).val := by
  rcases a with e | unit
  · rfl
  · cases unit
    exact Q.wv_right

/-- Left recovery is injective because the fresh copy recovers to `u-z`, which
is not a surviving old copy. -/
theorem recoverLeft_injective : Function.Injective Q.recoverLeft := by
  intro a b h
  rcases a with a | ua
  · rcases b with b | ub
    · exact congrArg Sum.inl (Subtype.ext h)
    · cases ub
      have ha := a.property
      change a.val = Q.uz at h
      rw [h] at ha
      exact False.elim (Q.uz_not_survives ha)
  · cases ua
    rcases b with b | ub
    · have hb := b.property
      change Q.uz = b.val at h
      rw [← h] at hb
      exact False.elim (Q.uz_not_survives hb)
    · cases ub
      rfl

/-- Right recovery is injective for the symmetric reason. -/
theorem recoverRight_injective : Function.Injective Q.recoverRight := by
  intro a b h
  rcases a with a | ua
  · rcases b with b | ub
    · exact congrArg Sum.inl (Subtype.ext h)
    · cases ub
      have ha := a.property
      change a.val = Q.wv at h
      rw [h] at ha
      exact False.elim (Q.wv_not_survives ha)
  · cases ua
    rcases b with b | ub
    · have hb := b.property
      change Q.wv = b.val at h
      rw [← h] at hb
      exact False.elim (Q.wv_not_survives hb)
    · cases ub
      rfl

/-- Membership of the recovered left copy is exactly membership of the smooth
copy. -/
theorem recoverLeft_mem_liftMatchingSet_iff
    (S : Finset Q.SmoothEdge) (a : Q.SmoothEdge) :
    Q.recoverLeft a ∈ Q.liftMatchingSet S ↔ a ∈ S := by
  rcases a with a | unit
  · exact Q.mem_liftMatchingSet_old S a
  · cases unit
    exact Q.mem_liftMatchingSet_uz S

/-- Membership of the recovered right copy is exactly membership of the smooth
copy. -/
theorem recoverRight_mem_liftMatchingSet_iff
    (S : Finset Q.SmoothEdge) (a : Q.SmoothEdge) :
    Q.recoverRight a ∈ Q.liftMatchingSet S ↔ a ∈ S := by
  rcases a with a | unit
  · exact Q.mem_liftMatchingSet_old S a
  · cases unit
    exact Q.mem_liftMatchingSet_wv S

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
