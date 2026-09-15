import BachThesisLean.Basic.Multigraph
import Mathlib.Data.Fintype.Pi

namespace BachThesisLean

open BipartiteMultigraph

universe u v w z

/-!
## Exact left-list assignments

An exact list assignment gives every left vertex a finite set of labels whose
cardinality is exactly its left degree. An admissible labeling uses precisely
that label set at each left vertex and is injective at every right vertex.
-/

structure ExactLeftLists
    {X : Type u} {Y : Type v} {E : Type w}
    [Fintype X] [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) (Λ : Type z) [Fintype Λ] where
  labels : X → Finset Λ
  card_labels : ∀ x, (labels x).card = G.leftDegree x

namespace ExactLeftLists

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable {Λ : Type z} [Fintype Λ]
variable {G : BipartiteMultigraph X Y E}

noncomputable def labelsUsedAtLeft
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (x : X) : Finset Λ :=
  by
    classical
    exact (G.leftIncident x).image σ

noncomputable def labelsUsedAtRight
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (y : Y) : Finset Λ :=
  by
    classical
    exact (G.rightIncident y).image σ

/-- Membership in the finite image of the left incidence set, stated without
exposing the classical `DecidableEq` chosen inside `labelsUsedAtLeft`. -/
theorem mem_labelsUsedAtLeft
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (x : X) (c : Λ) :
    c ∈ labelsUsedAtLeft G σ x ↔ ∃ e ∈ G.leftIncident x, σ e = c := by
  classical
  simp [labelsUsedAtLeft]

/-- Membership in the finite image of the right incidence set, stated without
exposing the classical `DecidableEq` chosen inside `labelsUsedAtRight`. -/
theorem mem_labelsUsedAtRight
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (y : Y) (c : Λ) :
    c ∈ labelsUsedAtRight G σ y ↔ ∃ e ∈ G.rightIncident y, σ e = c := by
  classical
  simp [labelsUsedAtRight]

def IsAdmissible
    (L : ExactLeftLists G Λ) (σ : E → Λ) : Prop :=
  (∀ x, labelsUsedAtLeft G σ x = L.labels x) ∧
  (∀ y, (G.rightIncident y).card = (labelsUsedAtRight G σ y).card)

noncomputable def admissibleLabelings
    (L : ExactLeftLists G Λ) : Finset (E → Λ) := by
  classical
  exact Finset.univ.filter (fun σ => IsAdmissible L σ)

noncomputable def count
    (L : ExactLeftLists G Λ) : ℕ :=
  (admissibleLabelings L).card

theorem mem_admissibleLabelings
    (L : ExactLeftLists G Λ) (σ : E → Λ) :
    σ ∈ admissibleLabelings L ↔ IsAdmissible L σ := by
  classical
  simp [admissibleLabelings]

noncomputable def uniform
    (G : BipartiteMultigraph X Y E) (k : ℕ)
    (h : G.IsLeftRegular k) : ExactLeftLists G (Fin k) where
  labels := fun _ => Finset.univ
  card_labels := by
    intro x
    simp [h x]

noncomputable def ordinaryCount
    (G : BipartiteMultigraph X Y E) (k : ℕ)
    (h : G.IsLeftRegular k) : ℕ :=
  count (uniform G k h)

end ExactLeftLists
end BachThesisLean
