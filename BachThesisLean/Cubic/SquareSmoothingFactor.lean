import BachThesisLean.Cubic.SquareSmoothing
import BachThesisLean.Cubic.FactorPathTransport
import BachThesisLean.Cubic.PortMasks

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Lifting factors through square smoothing

A selected fresh smoothing edge is expanded to its two original spokes and a
path through the deleted square. The square-edge rule below encodes all four
fresh-edge membership cases without identifying edge copies.
-/

/-- Whether a tagged smoothing copy is selected. -/
def freshSelected (S : Finset Q.SmoothEdge) (i : Bool) : Prop :=
  (Sum.inr i : Q.SmoothEdge) ∈ S

/-- The square copies selected when lifting a factor.

* If neither fresh copy is selected, all four square copies are kept.
* If exactly fresh copy `j` is selected, only the direct square copy joining
  its two spoke endpoints is omitted.
* If both fresh copies are selected, only the two direct paired square copies
  are kept.
-/
def squareSelected (swap : Bool) (S : Finset Q.SmoothEdge)
    (i j : Bool) : Prop :=
  if i = squarePair swap j then
    Q.freshSelected S j → Q.freshSelected S (squarePair true j)
  else
    ¬ (Q.freshSelected S false ∧ Q.freshSelected S true)

/-- Expand a selected set in the smoothing back to original edge copies. -/
noncomputable def liftFactor (swap : Bool) (S : Finset Q.SmoothEdge) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    (∃ h : Q.Survives e, (Sum.inl ⟨e, h⟩ : Q.SmoothEdge) ∈ S) ∨
    (∃ i, e = Q.rightSpoke i ∧ Q.freshSelected S i) ∨
    (∃ i, e = Q.leftSpoke (squarePair swap i) ∧ Q.freshSelected S i) ∨
    (∃ i j, e = Q.square i j ∧ Q.squareSelected swap S i j)

theorem mem_liftFactor (swap : Bool) (S : Finset Q.SmoothEdge) (e : E) :
    e ∈ Q.liftFactor swap S ↔
      (∃ h : Q.Survives e, (Sum.inl ⟨e, h⟩ : Q.SmoothEdge) ∈ S) ∨
      (∃ i, e = Q.rightSpoke i ∧ Q.freshSelected S i) ∨
      (∃ i, e = Q.leftSpoke (squarePair swap i) ∧ Q.freshSelected S i) ∨
      (∃ i j, e = Q.square i j ∧ Q.squareSelected swap S i j) := by
  classical
  simp [liftFactor]

@[simp] theorem mem_liftFactor_old (swap : Bool) (S : Finset Q.SmoothEdge)
    (e : Q.Survivor) :
    e.val ∈ Q.liftFactor swap S ↔ (Sum.inl e : Q.SmoothEdge) ∈ S := by
  rw [Q.mem_liftFactor swap S e.val]
  constructor
  · rintro (⟨h, he⟩ | ⟨i, hi, _⟩ | ⟨i, hi, _⟩ | ⟨i, j, hij, _⟩)
    · have hh : (⟨e.val, h⟩ : Q.Survivor) = e := Subtype.ext rfl
      simpa [hh] using he
    · exact False.elim (e.property.2.2 i hi)
    · exact False.elim (e.property.2.1 (squarePair swap i) hi)
    · exact False.elim (e.property.1 i j hij)
  · intro he
    exact Or.inl ⟨e.property, by simpa using he⟩

@[simp] theorem mem_liftFactor_rightSpoke (swap i : Bool)
    (S : Finset Q.SmoothEdge) :
    Q.rightSpoke i ∈ Q.liftFactor swap S ↔ Q.freshSelected S i := by
  rw [Q.mem_liftFactor swap S (Q.rightSpoke i)]
  constructor
  · rintro (⟨h, _⟩ | ⟨j, hij, hj⟩ | ⟨j, hij, _⟩ | ⟨a, b, hab, _⟩)
    · exact False.elim (h.2.2 i rfl)
    · exact (Q.rightSpoke_injective hij).symm ▸ hj
    · exact False.elim (Q.leftSpoke_ne_rightSpoke (squarePair swap j) i hij.symm)
    · exact False.elim (Q.square_ne_rightSpoke a b i hab.symm)
  · intro hi
    exact Or.inr (Or.inl ⟨i, rfl, hi⟩)

@[simp] theorem mem_liftFactor_leftSpoke_paired (swap i : Bool)
    (S : Finset Q.SmoothEdge) :
    Q.leftSpoke (squarePair swap i) ∈ Q.liftFactor swap S ↔
      Q.freshSelected S i := by
  rw [Q.mem_liftFactor swap S (Q.leftSpoke (squarePair swap i))]
  constructor
  · rintro (⟨h, _⟩ | ⟨j, hij, _⟩ | ⟨j, hij, hj⟩ | ⟨a, b, hab, _⟩)
    · exact False.elim (h.2.1 (squarePair swap i) rfl)
    · exact False.elim (Q.leftSpoke_ne_rightSpoke (squarePair swap i) j hij)
    · have hp : i = j := by
        apply squarePair_injective swap
        exact Q.leftSpoke_injective hij
      simpa [hp] using hj
    · exact False.elim (Q.square_ne_leftSpoke a b (squarePair swap i) hab.symm)
  · intro hi
    exact Or.inr (Or.inr (Or.inl ⟨i, rfl, hi⟩))

@[simp] theorem mem_liftFactor_square (swap i j : Bool)
    (S : Finset Q.SmoothEdge) :
    Q.square i j ∈ Q.liftFactor swap S ↔ Q.squareSelected swap S i j := by
  rw [Q.mem_liftFactor swap S (Q.square i j)]
  constructor
  · rintro (⟨h, _⟩ | ⟨k, hik, _⟩ | ⟨k, hik, _⟩ | ⟨a, b, hab, hs⟩)
    · exact False.elim (h.1 i j rfl)
    · exact False.elim (Q.square_ne_rightSpoke i j k hik)
    · exact False.elim (Q.square_ne_leftSpoke i j (squarePair swap k) hik)
    · have hp : (i, j) = (a, b) := Q.square_injective hab
      cases hp
      exact hs
  · intro hs
    exact Or.inr (Or.inr (Or.inr ⟨i, j, rfl, hs⟩))

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
