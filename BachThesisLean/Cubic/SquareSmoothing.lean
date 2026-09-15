import BachThesisLean.Cubic.Foundations

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Edge-copy square smoothing

This file defines the local data of an oriented four-cycle together with its
four external spokes and the two bipartite smoothings. The construction keeps
the two inserted smoothing edges as tagged edge copies, so an inserted edge is
never identified with a pre-existing parallel edge.
-/

/-- The two possible pairings of the two external left and right terminals. -/
def squarePair (swap i : Bool) : Bool :=
  if swap then !i else i

@[simp] theorem squarePair_false (i : Bool) : squarePair false i = i := by
  simp [squarePair]

@[simp] theorem squarePair_true_false : squarePair true false = true := by
  simp [squarePair]

@[simp] theorem squarePair_true_true : squarePair true true = false := by
  simp [squarePair]

@[simp] theorem squarePair_pair (swap i : Bool) :
    squarePair swap (squarePair swap i) = i := by
  cases swap <;> cases i <;> rfl

theorem squarePair_injective (swap : Bool) : Function.Injective (squarePair swap) := by
  intro i j h
  have h' := congrArg (squarePair swap) h
  simpa using h'

/-- An oriented square saturated by one external spoke at each square vertex.
The saturation clauses say that the displayed three copies are all incident
copies at each square vertex. They are the local fact supplied by cubicity
when constructing a frame from an actual cubic square. -/
structure SquareFrame (G : BipartiteMultigraph X Y E) where
  leftVertex : Bool → X
  rightVertex : Bool → Y
  externalLeft : Bool → X
  externalRight : Bool → Y
  square : Bool → Bool → E
  leftSpoke : Bool → E
  rightSpoke : Bool → E
  leftVertex_ne : leftVertex false ≠ leftVertex true
  rightVertex_ne : rightVertex false ≠ rightVertex true
  externalLeft_ne : ∀ i j, externalLeft i ≠ leftVertex j
  externalRight_ne : ∀ i j, externalRight i ≠ rightVertex j
  square_left : ∀ i j, G.left (square i j) = leftVertex i
  square_right : ∀ i j, G.right (square i j) = rightVertex j
  leftSpoke_left : ∀ i, G.left (leftSpoke i) = leftVertex i
  leftSpoke_right : ∀ i, G.right (leftSpoke i) = externalRight i
  rightSpoke_left : ∀ i, G.left (rightSpoke i) = externalLeft i
  rightSpoke_right : ∀ i, G.right (rightSpoke i) = rightVertex i
  square_injective : Function.Injective (fun p : Bool × Bool => square p.1 p.2)
  leftSpoke_injective : Function.Injective leftSpoke
  rightSpoke_injective : Function.Injective rightSpoke
  square_ne_leftSpoke : ∀ i j k, square i j ≠ leftSpoke k
  square_ne_rightSpoke : ∀ i j k, square i j ≠ rightSpoke k
  leftSpoke_ne_rightSpoke : ∀ i j, leftSpoke i ≠ rightSpoke j
  left_saturated : ∀ e i, G.left e = leftVertex i →
    e = square i false ∨ e = square i true ∨ e = leftSpoke i
  right_saturated : ∀ e j, G.right e = rightVertex j →
    e = square false j ∨ e = square true j ∨ e = rightSpoke j

namespace SquareFrame

variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-- An old edge is outside the four cycle copies. -/
def OutsideSquare (e : E) : Prop := ∀ i j, e ≠ Q.square i j

/-- Surviving old copies are neither cycle copies nor any of the four spokes. -/
def Survives (e : E) : Prop :=
  Q.OutsideSquare e ∧ (∀ i, e ≠ Q.leftSpoke i) ∧ ∀ i, e ≠ Q.rightSpoke i

@[simp] theorem survives_iff (e : E) :
    Q.Survives e ↔ Q.OutsideSquare e ∧
      (∀ i, e ≠ Q.leftSpoke i) ∧ ∀ i, e ≠ Q.rightSpoke i := Iff.rfl

abbrev Survivor := {e : E // Q.Survives e}
abbrev ReducedLeft := {x : X // ∀ i, x ≠ Q.leftVertex i}
abbrev ReducedRight := {y : Y // ∀ i, y ≠ Q.rightVertex i}
abbrev SmoothEdge := Q.Survivor ⊕ Bool

noncomputable instance : Fintype Q.Survivor := Fintype.ofFinite _
noncomputable instance : Fintype Q.ReducedLeft := Fintype.ofFinite _
noncomputable instance : Fintype Q.ReducedRight := Fintype.ofFinite _
noncomputable instance : Fintype Q.SmoothEdge := Fintype.ofFinite _

instance : DecidableEq Q.Survivor := inferInstance
instance : DecidableEq Q.ReducedLeft := inferInstance
instance : DecidableEq Q.ReducedRight := inferInstance
instance : DecidableEq Q.SmoothEdge := inferInstance

/-- A non-cycle copy is either an ordinary survivor or one of the four spokes. -/
theorem outsideSquare_cases {e : E} (h : Q.OutsideSquare e) :
    Q.Survives e ∨ (∃ i, e = Q.leftSpoke i) ∨ ∃ i, e = Q.rightSpoke i := by
  classical
  by_cases hl : ∃ i, e = Q.leftSpoke i
  · exact Or.inr (Or.inl hl)
  by_cases hr : ∃ i, e = Q.rightSpoke i
  · exact Or.inr (Or.inr hr)
  refine Or.inl ⟨h, ?_, ?_⟩
  · intro i hi
    exact hl ⟨i, hi⟩
  · intro i hi
    exact hr ⟨i, hi⟩

/-- A surviving old copy has no deleted left endpoint. -/
theorem survivor_left_ne (e : Q.Survivor) (i : Bool) :
    G.left e.val ≠ Q.leftVertex i := by
  intro h
  rcases Q.left_saturated e.val i h with hs | hs | hs
  · exact e.property.1 i false hs
  · exact e.property.1 i true hs
  · exact e.property.2.1 i hs

/-- A surviving old copy has no deleted right endpoint. -/
theorem survivor_right_ne (e : Q.Survivor) (i : Bool) :
    G.right e.val ≠ Q.rightVertex i := by
  intro h
  rcases Q.right_saturated e.val i h with hs | hs | hs
  · exact e.property.1 false i hs
  · exact e.property.1 true i hs
  · exact e.property.2.2 i hs

/-- The smoothed graph for either of the two bipartite terminal pairings. -/
def smooth (swap : Bool) : BipartiteMultigraph Q.ReducedLeft Q.ReducedRight Q.SmoothEdge where
  left
    | .inl e => ⟨G.left e.val, Q.survivor_left_ne e⟩
    | .inr i => ⟨Q.externalLeft i, Q.externalLeft_ne i⟩
  right
    | .inl e => ⟨G.right e.val, Q.survivor_right_ne e⟩
    | .inr i => ⟨Q.externalRight (squarePair swap i), Q.externalRight_ne _⟩

@[simp] theorem smooth_left_old (swap : Bool) (e : Q.Survivor) :
    (Q.smooth swap).left (.inl e) = ⟨G.left e.val, Q.survivor_left_ne e⟩ := rfl

@[simp] theorem smooth_right_old (swap : Bool) (e : Q.Survivor) :
    (Q.smooth swap).right (.inl e) = ⟨G.right e.val, Q.survivor_right_ne e⟩ := rfl

@[simp] theorem smooth_left_fresh (swap i : Bool) :
    (Q.smooth swap).left (.inr i) = ⟨Q.externalLeft i, Q.externalLeft_ne i⟩ := rfl

@[simp] theorem smooth_right_fresh (swap i : Bool) :
    (Q.smooth swap).right (.inr i) =
      ⟨Q.externalRight (squarePair swap i), Q.externalRight_ne _⟩ := rfl

/-- Recover the old incident copy at a surviving left vertex. -/
def recoverLeft : Q.SmoothEdge → E
  | .inl e => e.val
  | .inr i => Q.rightSpoke i

/-- Recover the old incident copy at a surviving right vertex. -/
def recoverRight (swap : Bool) : Q.SmoothEdge → E
  | .inl e => e.val
  | .inr i => Q.leftSpoke (squarePair swap i)

@[simp] theorem recoverLeft_old (e : Q.Survivor) : Q.recoverLeft (.inl e) = e.val := rfl
@[simp] theorem recoverLeft_fresh (i : Bool) : Q.recoverLeft (.inr i) = Q.rightSpoke i := rfl
@[simp] theorem recoverRight_old (swap : Bool) (e : Q.Survivor) :
    Q.recoverRight swap (.inl e) = e.val := rfl
@[simp] theorem recoverRight_fresh (swap i : Bool) :
    Q.recoverRight swap (.inr i) = Q.leftSpoke (squarePair swap i) := rfl

theorem recoverLeft_injective : Function.Injective Q.recoverLeft := by
  intro a b h
  cases a with
  | inl e =>
      cases b with
      | inl f => exact congrArg Sum.inl (Subtype.ext h)
      | inr i => exact False.elim (e.property.2.2 i h)
  | inr i =>
      cases b with
      | inl e => exact False.elim (e.property.2.2 i h.symm)
      | inr j => exact congrArg Sum.inr (Q.rightSpoke_injective h)

theorem recoverRight_injective (swap : Bool) : Function.Injective (Q.recoverRight swap) := by
  intro a b h
  cases a with
  | inl e =>
      cases b with
      | inl f => exact congrArg Sum.inl (Subtype.ext h)
      | inr i => exact False.elim (e.property.2.1 _ h)
  | inr i =>
      cases b with
      | inl e => exact False.elim (e.property.2.1 _ h.symm)
      | inr j =>
          apply congrArg Sum.inr
          apply squarePair_injective swap
          exact Q.leftSpoke_injective h

@[simp] theorem recoverLeft_left (swap : Bool) (e : Q.SmoothEdge) :
    G.left (Q.recoverLeft e) = ((Q.smooth swap).left e).val := by
  cases e with
  | inl e => rfl
  | inr i => exact Q.rightSpoke_left i

@[simp] theorem recoverRight_right (swap : Bool) (e : Q.SmoothEdge) :
    G.right (Q.recoverRight swap e) = ((Q.smooth swap).right e).val := by
  cases e with
  | inl e => rfl
  | inr i => exact Q.leftSpoke_right (squarePair swap i)

theorem recoverLeft_incidence_image (swap : Bool) (x : Q.ReducedLeft) :
    ((Q.smooth swap).incidentEdges (.inl x)).image Q.recoverLeft =
      G.incidentEdges (.inl x.val) := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' : (Q.smooth swap).left a = x := by
      simpa [Incident] using ha
    simpa only [mem_incidentEdges, Incident, Q.recoverLeft_left swap a] using
      congrArg Subtype.val ha'
  · intro he
    have he' : G.left e = x.val := by simpa [Incident] using he
    have hs : Q.OutsideSquare e := by
      intro i j h
      exact x.property i
        (he'.symm.trans ((congrArg G.left h).trans (Q.square_left i j)))
    rcases Q.outsideSquare_cases hs with h | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine Finset.mem_image.mpr ⟨.inl ⟨e, h⟩, ?_, rfl⟩
      simp only [mem_incidentEdges, Incident, smooth_left_old]
      exact Subtype.ext he'
    · exact False.elim (x.property i (he'.symm.trans (Q.leftSpoke_left i)))
    · refine Finset.mem_image.mpr ⟨.inr i, ?_, rfl⟩
      simp only [mem_incidentEdges, Incident, smooth_left_fresh]
      exact Subtype.ext ((Q.rightSpoke_left i).symm.trans he')

theorem recoverRight_incidence_image (swap : Bool) (y : Q.ReducedRight) :
    ((Q.smooth swap).incidentEdges (.inr y)).image (Q.recoverRight swap) =
      G.incidentEdges (.inr y.val) := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' : (Q.smooth swap).right a = y := by
      simpa [Incident] using ha
    simpa [Incident] using congrArg Subtype.val ha'
  · intro he
    have he' : G.right e = y.val := by simpa [Incident] using he
    have hs : Q.OutsideSquare e := by
      intro i j h
      exact y.property j
        (he'.symm.trans ((congrArg G.right h).trans (Q.square_right i j)))
    rcases Q.outsideSquare_cases hs with h | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine Finset.mem_image.mpr ⟨.inl ⟨e, h⟩, ?_, rfl⟩
      simp only [mem_incidentEdges, Incident, smooth_right_old]
      exact Subtype.ext he'
    · refine Finset.mem_image.mpr ⟨.inr (squarePair swap i), ?_, ?_⟩
      · simp only [mem_incidentEdges, Incident, smooth_right_fresh, squarePair_pair]
        exact Subtype.ext ((Q.leftSpoke_right i).symm.trans he')
      · simp
    · exact False.elim (y.property i (he'.symm.trans (Q.rightSpoke_right i)))

/-- Each surviving incidence has a unique old copy, including when distinct
spokes share an external endpoint. Thus both pairings preserve cubicity. -/
theorem smooth_isCubic (hG : G.IsCubic) (swap : Bool) : (Q.smooth swap).IsCubic := by
  intro v
  cases v with
  | inl x =>
      have h := congrArg Finset.card (Q.recoverLeft_incidence_image swap x)
      rw [Finset.card_image_of_injective _ Q.recoverLeft_injective] at h
      exact h.trans (hG (.inl x.val))
  | inr y =>
      have h := congrArg Finset.card (Q.recoverRight_incidence_image swap y)
      rw [Finset.card_image_of_injective _ (Q.recoverRight_injective swap)] at h
      exact h.trans (hG (.inr y.val))

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
