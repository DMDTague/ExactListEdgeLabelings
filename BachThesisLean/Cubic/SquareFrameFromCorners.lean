import BachThesisLean.Cubic.SquareSmoothing
import BachThesisLean.Cubic.BraceSimplicity

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Building a square frame from four corners

The smoothing API uses a `SquareFrame`, which records not only the four cycle
copies but also the unique third incident copy at each cubic corner.  This file
packages the local construction once: in a simple cubic graph, any genuine
`K₂,₂` of four distinct edge copies canonically extends (noncomputably) to a
`SquareFrame` by choosing the third incident edge at each corner.
-/

/-- The four cycle copies and their two-by-two endpoint data, before choosing
external spokes. -/
structure SquareCorners (G : BipartiteMultigraph X Y E) where
  leftVertex : Bool → X
  rightVertex : Bool → Y
  square : Bool → Bool → E
  leftVertex_ne : leftVertex false ≠ leftVertex true
  rightVertex_ne : rightVertex false ≠ rightVertex true
  square_left : ∀ i j, G.left (square i j) = leftVertex i
  square_right : ∀ i j, G.right (square i j) = rightVertex j
  square_injective : Function.Injective (fun p : Bool × Bool => square p.1 p.2)

namespace SquareCorners

variable (C : SquareCorners G)

/-- The two left corner labels are injective. -/
theorem leftVertex_injective : Function.Injective C.leftVertex := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · exact False.elim (C.leftVertex_ne hij)
  · exact False.elim (C.leftVertex_ne hij.symm)
  · rfl

/-- The two right corner labels are injective. -/
theorem rightVertex_injective : Function.Injective C.rightVertex := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · exact False.elim (C.rightVertex_ne hij)
  · exact False.elim (C.rightVertex_ne hij.symm)
  · rfl

/-- The two square copies in one row are distinct. -/
theorem square_ne_same_left (i : Bool) :
    C.square i false ≠ C.square i true := by
  intro h
  have hp : (i, false) = (i, true) := C.square_injective h
  exact Bool.false_ne_true (congrArg Prod.snd hp)

/-- The two square copies in one column are distinct. -/
theorem square_ne_same_right (j : Bool) :
    C.square false j ≠ C.square true j := by
  intro h
  have hp : (false, j) = (true, j) := C.square_injective h
  exact Bool.false_ne_true (congrArg Prod.fst hp)

/-- At a cubic left corner there is an incident copy other than the two square
copies. -/
theorem exists_leftThird (hG : G.IsCubic) (i : Bool) :
    ∃ e : E, e ∈ G.leftIncident (C.leftVertex i) ∧
      e ≠ C.square i false ∧ e ≠ C.square i true := by
  classical
  let T : Finset E := {C.square i false, C.square i true}
  have hTcard : T.card = 2 := by
    simp [T, C.square_ne_same_left i]
  have hdeg : (G.leftIncident (C.leftVertex i)).card = 3 := by
    simpa using hG (.inl (C.leftVertex i))
  have hex : ∃ e : E, e ∈ G.leftIncident (C.leftVertex i) ∧ e ∉ T := by
    by_contra hnone
    push_neg at hnone
    have hsub : G.leftIncident (C.leftVertex i) ⊆ T := by
      intro e he
      exact hnone e he
    have hle := Finset.card_le_card hsub
    rw [hdeg, hTcard] at hle
    omega
  obtain ⟨e, heI, heT⟩ := hex
  have hne : e ≠ C.square i false ∧ e ≠ C.square i true := by
    simpa [T] using heT
  exact ⟨e, heI, hne.1, hne.2⟩

/-- At a cubic right corner there is an incident copy other than the two square
copies. -/
theorem exists_rightThird (hG : G.IsCubic) (j : Bool) :
    ∃ e : E, e ∈ G.rightIncident (C.rightVertex j) ∧
      e ≠ C.square false j ∧ e ≠ C.square true j := by
  classical
  let T : Finset E := {C.square false j, C.square true j}
  have hTcard : T.card = 2 := by
    simp [T, C.square_ne_same_right j]
  have hdeg : (G.rightIncident (C.rightVertex j)).card = 3 := by
    simpa using hG (.inr (C.rightVertex j))
  have hex : ∃ e : E, e ∈ G.rightIncident (C.rightVertex j) ∧ e ∉ T := by
    by_contra hnone
    push_neg at hnone
    have hsub : G.rightIncident (C.rightVertex j) ⊆ T := by
      intro e he
      exact hnone e he
    have hle := Finset.card_le_card hsub
    rw [hdeg, hTcard] at hle
    omega
  obtain ⟨e, heI, heT⟩ := hex
  have hne : e ≠ C.square false j ∧ e ≠ C.square true j := by
    simpa [T] using heT
  exact ⟨e, heI, hne.1, hne.2⟩

/-- Chosen third copy at a left square vertex. -/
noncomputable def leftThird (hG : G.IsCubic) (i : Bool) : E :=
  Classical.choose (C.exists_leftThird hG i)

/-- Chosen third copy at a right square vertex. -/
noncomputable def rightThird (hG : G.IsCubic) (j : Bool) : E :=
  Classical.choose (C.exists_rightThird hG j)

@[simp] theorem leftThird_mem (hG : G.IsCubic) (i : Bool) :
    C.leftThird hG i ∈ G.leftIncident (C.leftVertex i) :=
  (Classical.choose_spec (C.exists_leftThird hG i)).1

@[simp] theorem rightThird_mem (hG : G.IsCubic) (j : Bool) :
    C.rightThird hG j ∈ G.rightIncident (C.rightVertex j) :=
  (Classical.choose_spec (C.exists_rightThird hG j)).1

@[simp] theorem leftThird_left (hG : G.IsCubic) (i : Bool) :
    G.left (C.leftThird hG i) = C.leftVertex i :=
  (G.mem_leftIncident (C.leftVertex i) (C.leftThird hG i)).1
    (C.leftThird_mem hG i)

@[simp] theorem rightThird_right (hG : G.IsCubic) (j : Bool) :
    G.right (C.rightThird hG j) = C.rightVertex j :=
  (G.mem_rightIncident (C.rightVertex j) (C.rightThird hG j)).1
    (C.rightThird_mem hG j)

theorem leftThird_ne_square (hG : G.IsCubic) (i j : Bool) :
    C.leftThird hG i ≠ C.square i j := by
  cases j
  · exact (Classical.choose_spec (C.exists_leftThird hG i)).2.1
  · exact (Classical.choose_spec (C.exists_leftThird hG i)).2.2

theorem rightThird_ne_square (hG : G.IsCubic) (j i : Bool) :
    C.rightThird hG j ≠ C.square i j := by
  cases i
  · exact (Classical.choose_spec (C.exists_rightThird hG j)).2.1
  · exact (Classical.choose_spec (C.exists_rightThird hG j)).2.2

/-- The chosen third copy exhausts the remaining left incidence slot. -/
theorem left_saturated (hG : G.IsCubic) (e : E) (i : Bool)
    (he : G.left e = C.leftVertex i) :
    e = C.square i false ∨ e = C.square i true ∨ e = C.leftThird hG i := by
  classical
  by_cases h0 : e = C.square i false
  · exact Or.inl h0
  by_cases h1 : e = C.square i true
  · exact Or.inr (Or.inl h1)
  by_cases ht : e = C.leftThird hG i
  · exact Or.inr (Or.inr ht)
  have heI : e ∈ G.leftIncident (C.leftVertex i) :=
    (G.mem_leftIncident (C.leftVertex i) e).2 he
  have hs0I : C.square i false ∈ G.leftIncident (C.leftVertex i) :=
    (G.mem_leftIncident (C.leftVertex i) (C.square i false)).2
      (C.square_left i false)
  have hs1I : C.square i true ∈ G.leftIncident (C.leftVertex i) :=
    (G.mem_leftIncident (C.leftVertex i) (C.square i true)).2
      (C.square_left i true)
  have htI := C.leftThird_mem hG i
  let T : Finset E :=
    {e, C.square i false, C.square i true, C.leftThird hG i}
  have hTsub : T ⊆ G.leftIncident (C.leftVertex i) := by
    intro z hz
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact heI
    · exact hs0I
    · exact hs1I
    · exact htI
  have h01 : C.square i false ≠ C.square i true := C.square_ne_same_left i
  have h0t : C.square i false ≠ C.leftThird hG i :=
    (C.leftThird_ne_square hG i false).symm
  have h1t : C.square i true ≠ C.leftThird hG i :=
    (C.leftThird_ne_square hG i true).symm
  have hinner :
      ({C.square i false, C.square i true, C.leftThird hG i} : Finset E).card = 3 := by
    simp [h01, h0t, h1t]
  have heNotInner :
      e ∉ ({C.square i false, C.square i true, C.leftThird hG i} : Finset E) := by
    simp [h0, h1, ht]
  have hTcard : T.card = 4 := by
    change ({e, C.square i false, C.square i true, C.leftThird hG i} : Finset E).card = 4
    rw [Finset.card_insert_of_not_mem heNotInner, hinner]
  have hdeg : (G.leftIncident (C.leftVertex i)).card = 3 := by
    simpa using hG (.inl (C.leftVertex i))
  have hle := Finset.card_le_card hTsub
  rw [hTcard, hdeg] at hle
  omega

/-- The chosen third copy exhausts the remaining right incidence slot. -/
theorem right_saturated (hG : G.IsCubic) (e : E) (j : Bool)
    (he : G.right e = C.rightVertex j) :
    e = C.square false j ∨ e = C.square true j ∨ e = C.rightThird hG j := by
  classical
  by_cases h0 : e = C.square false j
  · exact Or.inl h0
  by_cases h1 : e = C.square true j
  · exact Or.inr (Or.inl h1)
  by_cases ht : e = C.rightThird hG j
  · exact Or.inr (Or.inr ht)
  have heI : e ∈ G.rightIncident (C.rightVertex j) :=
    (G.mem_rightIncident (C.rightVertex j) e).2 he
  have hs0I : C.square false j ∈ G.rightIncident (C.rightVertex j) :=
    (G.mem_rightIncident (C.rightVertex j) (C.square false j)).2
      (C.square_right false j)
  have hs1I : C.square true j ∈ G.rightIncident (C.rightVertex j) :=
    (G.mem_rightIncident (C.rightVertex j) (C.square true j)).2
      (C.square_right true j)
  have htI := C.rightThird_mem hG j
  let T : Finset E :=
    {e, C.square false j, C.square true j, C.rightThird hG j}
  have hTsub : T ⊆ G.rightIncident (C.rightVertex j) := by
    intro z hz
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact heI
    · exact hs0I
    · exact hs1I
    · exact htI
  have h01 : C.square false j ≠ C.square true j := C.square_ne_same_right j
  have h0t : C.square false j ≠ C.rightThird hG j :=
    (C.rightThird_ne_square hG j false).symm
  have h1t : C.square true j ≠ C.rightThird hG j :=
    (C.rightThird_ne_square hG j true).symm
  have hinner :
      ({C.square false j, C.square true j, C.rightThird hG j} : Finset E).card = 3 := by
    simp [h01, h0t, h1t]
  have heNotInner :
      e ∉ ({C.square false j, C.square true j, C.rightThird hG j} : Finset E) := by
    simp [h0, h1, ht]
  have hTcard : T.card = 4 := by
    change ({e, C.square false j, C.square true j, C.rightThird hG j} : Finset E).card = 4
    rw [Finset.card_insert_of_not_mem heNotInner, hinner]
  have hdeg : (G.rightIncident (C.rightVertex j)).card = 3 := by
    simpa using hG (.inr (C.rightVertex j))
  have hle := Finset.card_le_card hTsub
  rw [hTcard, hdeg] at hle
  omega

/-- A four-corner square in a simple cubic graph extends to the full smoothing
frame, with the four third incident copies as external spokes. -/
noncomputable def toSquareFrame (hsimple : G.IsSimple) (hG : G.IsCubic) :
    SquareFrame G where
  leftVertex := C.leftVertex
  rightVertex := C.rightVertex
  externalLeft := fun j => G.left (C.rightThird hG j)
  externalRight := fun i => G.right (C.leftThird hG i)
  square := C.square
  leftSpoke := C.leftThird hG
  rightSpoke := C.rightThird hG
  leftVertex_ne := C.leftVertex_ne
  rightVertex_ne := C.rightVertex_ne
  externalLeft_ne := by
    intro j i hEq
    have hpairs :
        (G.left (C.rightThird hG j), G.right (C.rightThird hG j)) =
          (G.left (C.square i j), G.right (C.square i j)) := by
      apply Prod.ext
      · simpa only [C.square_left] using hEq
      · rw [C.rightThird_right hG j, C.square_right i j]
    exact (C.rightThird_ne_square hG j i) (hsimple hpairs)
  externalRight_ne := by
    intro i j hEq
    have hpairs :
        (G.left (C.leftThird hG i), G.right (C.leftThird hG i)) =
          (G.left (C.square i j), G.right (C.square i j)) := by
      apply Prod.ext
      · rw [C.leftThird_left hG i, C.square_left i j]
      · simpa only [C.square_right] using hEq
    exact (C.leftThird_ne_square hG i j) (hsimple hpairs)
  square_left := C.square_left
  square_right := C.square_right
  leftSpoke_left := C.leftThird_left hG
  leftSpoke_right := fun i => rfl
  rightSpoke_left := fun j => rfl
  rightSpoke_right := C.rightThird_right hG
  square_injective := C.square_injective
  leftSpoke_injective := by
    intro i k hik
    apply C.leftVertex_injective
    rw [← C.leftThird_left hG i, ← C.leftThird_left hG k, hik]
  rightSpoke_injective := by
    intro j l hjl
    apply C.rightVertex_injective
    rw [← C.rightThird_right hG j, ← C.rightThird_right hG l, hjl]
  square_ne_leftSpoke := by
    intro i j k hEq
    have hik : i = k := by
      apply C.leftVertex_injective
      rw [← C.square_left i j, ← C.leftThird_left hG k, hEq]
    subst k
    exact (C.leftThird_ne_square hG i j) hEq.symm
  square_ne_rightSpoke := by
    intro i j l hEq
    have hjl : j = l := by
      apply C.rightVertex_injective
      rw [← C.square_right i j, ← C.rightThird_right hG l, hEq]
    subst l
    exact (C.rightThird_ne_square hG j i) hEq.symm
  leftSpoke_ne_rightSpoke := by
    intro i j hEq
    have hpairs :
        (G.left (C.leftThird hG i), G.right (C.leftThird hG i)) =
          (G.left (C.square i j), G.right (C.square i j)) := by
      apply Prod.ext
      · rw [C.leftThird_left hG i, C.square_left i j]
      · calc
          G.right (C.leftThird hG i) = G.right (C.rightThird hG j) :=
            congrArg G.right hEq
          _ = C.rightVertex j := C.rightThird_right hG j
          _ = G.right (C.square i j) := (C.square_right i j).symm
    exact (C.leftThird_ne_square hG i j) (hsimple hpairs)
  left_saturated := C.left_saturated hG
  right_saturated := C.right_saturated hG

end SquareCorners
end BipartiteMultigraph
end BachThesisLean
