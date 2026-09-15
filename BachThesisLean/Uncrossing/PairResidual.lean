import BachThesisLean.Uncrossing.GlobalSurplus
import BachThesisLean.Uncrossing.FibreSurplus
import BachThesisLean.Cubic.EdgeRestriction

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E] [DecidableEq Λ]

/-- Decode a binary residual label as one of the selected global labels. -/
def pairLabel (a b : Λ) (i : Fin 2) : Λ := if i = 0 then a else b

@[simp] theorem pairLabel_zero (a b : Λ) : pairLabel a b 0 = a := by
  simp [pairLabel]

@[simp] theorem pairLabel_one (a b : Λ) : pairLabel a b 1 = b := by
  simp [pairLabel]

theorem pairLabel_injective {a b : Λ} (hab : a ≠ b) :
    Function.Injective (pairLabel a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairLabel]

@[simp] theorem pairCode_pairLabel {a b : Λ} (hab : a ≠ b) (i : Fin 2) :
    (if pairLabel a b i = a then (0 : Fin 2) else 1) = i := by
  fin_cases i <;> simp [pairLabel, hab.symm]

theorem pairLabel_pairCode
    (σ : E → Λ) {a b : Λ} (e : E) (he : e ∈ pairEdges σ a b) :
    pairLabel a b (pairCode σ a e) = σ e := by
  rcases (mem_pairEdges σ a b e).1 he with ha | hb
  · simp [pairCode, pairLabel, ha]
  · by_cases ha : σ e = a
    · simp [pairCode, pairLabel, ha]
    · have hcode : pairCode σ a e = 1 := by simp [pairCode, ha]
      rw [hcode, pairLabel_one]
      exact hb.symm

/-- Active copies keep their original endpoints and their distinct copy IDs. -/
noncomputable abbrev pairResidualGraph
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (a b : Λ) :=
  G.restrictEdges (pairEdges σ a b)

/-- The original completion certifies the exact residual left degrees. The
proof counts the image of the injective binary coloring on each incidence set;
no graph component classification or external coloring theorem is used. -/
theorem pairResidual_leftDegree
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    {σ : E → Λ} (hσ : (exactListsOfSupports S hS).IsAdmissible σ)
    (x : X) :
    (pairResidualGraph G σ a b).leftDegree x =
      (if x ∈ S a then 1 else 0) + (if x ∈ S b then 1 else 0) := by
  classical
  let H := pairResidualGraph G σ a b
  let c : {e // e ∈ pairEdges σ a b} → Fin 2 :=
    fun e => pairCode σ a e.val
  have hinj : Set.InjOn c (H.leftIncident x) := by
    intro e he f hf hc
    apply Subtype.ext
    apply hσ.left_injOn x
      ((G.mem_leftIncident x e.val).2 ((H.mem_leftIncident x e).1 he))
      ((G.mem_leftIncident x f.val).2 ((H.mem_leftIncident x f).1 hf))
    exact pairCode_eq_imp_label_eq σ hab e.property f.property hc
  let T : Finset (Fin 2) := {i | x ∈ S (pairLabel a b i)}
  have himage : (H.leftIncident x).image c = T := by
    ext i
    constructor
    · intro hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
      have hm := hσ.label_mem e.val
      change σ e.val ∈ listsOfSupports S (G.left e.val) at hm
      rw [mem_listsOfSupports] at hm
      have hx : G.left e.val = x := (H.mem_leftIncident x e).1 he
      simpa [T, c, pairLabel_pairCode σ e.val e.property, hx] using hm
    · intro hi
      have hm : pairLabel a b i ∈ (exactListsOfSupports S hS).labels x := by
        change pairLabel a b i ∈ listsOfSupports S x
        apply (mem_listsOfSupports S x (pairLabel a b i)).2
        simpa [T] using hi
      obtain ⟨e, ⟨hex, hec⟩, _⟩ :=
        hσ.exact_once x (pairLabel a b i) hm
      have heP : e ∈ pairEdges σ a b := by
        rw [mem_pairEdges, hec]
        fin_cases i <;> simp [pairLabel]
      apply Finset.mem_image.mpr
      refine ⟨⟨e, heP⟩, (H.mem_leftIncident x _).2 hex, ?_⟩
      simpa [c, pairCode, hec] using pairCode_pairLabel hab i
  have hcard : H.leftDegree x = T.card := by
    change (H.leftIncident x).card = T.card
    rw [← himage, Finset.card_image_iff.mpr hinj]
  rw [hcard]
  by_cases ha : x ∈ S a
  · by_cases hb : x ∈ S b
    · have hT : T = ({0, 1} : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [T, pairLabel, ha, hb]
      simp [hT, ha, hb]
    · have hT : T = ({0} : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [T, pairLabel, ha, hb]
      simp [hT, ha, hb]
  · by_cases hb : x ∈ S b
    · have hT : T = ({1} : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [T, pairLabel, ha, hb]
      simp [hT, ha, hb]
    · have hT : T = (∅ : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [T, pairLabel, ha, hb]
      simp [hT, ha, hb]

/-- Equality of frozen assignments preserves the active copy set. -/
theorem pairEdges_eq_of_freezePair_eq
    (a b : Λ) {σ τ : E → Λ}
    (h : freezePair a b τ = freezePair a b σ) :
    pairEdges τ a b = pairEdges σ a b := by
  ext e
  have he := congrFun h e
  simp only [freezePair] at he
  by_cases ht : τ e = a ∨ τ e = b <;>
    by_cases hs : σ e = a ∨ σ e = b <;>
    simp_all [mem_pairEdges]

/-- Every frozen copy retains its original label. -/
theorem label_eq_of_freezePair_eq
    (a b : Λ) {σ τ : E → Λ}
    (h : freezePair a b τ = freezePair a b σ)
    {e : E} (he : e ∉ pairEdges σ a b) :
    τ e = σ e := by
  have ht : e ∉ pairEdges τ a b := by
    rw [pairEdges_eq_of_freezePair_eq a b h]
    exact he
  have heq := congrFun h e
  have hs := (mem_pairEdges σ a b e).not.mp he
  have ht' := (mem_pairEdges τ a b e).not.mp ht
  simpa [freezePair, hs, ht'] using heq

end BachThesisLean
