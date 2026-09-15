import BachThesisLean.Basic.Counting
import Mathlib.Data.Fintype.EquivFin

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]

/-!
# Relabelling a common finite palette

When every left vertex has the same finite label set `P`, labels outside `P`
are unused.  An equivalence `P ≃ Fin k` therefore transports admissible
labelings exactly to ordinary proper `k`-edge-colorings.
-/

noncomputable def encodeCommonPalette
    {P : Finset Λ} {k : ℕ} (eP : P ≃ Fin k)
    (σ : E → Λ) (hmem : ∀ e, σ e ∈ P) : E → Fin k :=
  fun edge => eP ⟨σ edge, hmem edge⟩

noncomputable def decodeCommonPalette
    {P : Finset Λ} {k : ℕ} (eP : P ≃ Fin k)
    (τ : E → Fin k) : E → Λ :=
  fun edge => (eP.symm (τ edge)).1

@[simp] theorem decodeCommonPalette_encodeCommonPalette
    {P : Finset Λ} {k : ℕ} (eP : P ≃ Fin k)
    (σ : E → Λ) (hmem : ∀ e, σ e ∈ P) :
    decodeCommonPalette eP (encodeCommonPalette eP σ hmem) = σ := by
  funext edge
  simp [decodeCommonPalette, encodeCommonPalette]

@[simp] theorem encodeCommonPalette_decodeCommonPalette
    {P : Finset Λ} {k : ℕ} (eP : P ≃ Fin k)
    (τ : E → Fin k) :
    encodeCommonPalette eP (decodeCommonPalette eP τ)
      (fun edge => (eP.symm (τ edge)).2) = τ := by
  funext edge
  simp [decodeCommonPalette, encodeCommonPalette]

/-- Admissible labelings for a common palette are equivalent to admissible
uniform `Fin k` labelings. -/
noncomputable def commonPaletteAdmissibleEquiv
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (L : ExactLeftLists G Λ) (P : Finset Λ)
    (hlabels : ∀ x, L.labels x = P) (hP : P.card = k) :
    L.AdmissibleLabeling ≃ (uniform G k hG).AdmissibleLabeling := by
  classical
  let eP : P ≃ Fin k := Finset.equivFinOfCardEq hP
  let forward : L.AdmissibleLabeling → (uniform G k hG).AdmissibleLabeling := fun s => by
    have hmem : ∀ edge, s.1 edge ∈ P := by
      intro edge
      rw [← hlabels (G.left edge)]
      exact s.2.label_mem edge
    let τ : E → Fin k := encodeCommonPalette eP s.1 hmem
    refine ⟨τ, ?_⟩
    apply (isAdmissible_uniform_iff k hG τ).2
    constructor
    · intro x edge hedge f hf hEq
      apply s.2.left_injOn x hedge hf
      have hsub :
          (⟨s.1 edge, hmem edge⟩ : P) = ⟨s.1 f, hmem f⟩ :=
        eP.injective hEq
      exact congrArg Subtype.val hsub
    · intro y edge hedge f hf hEq
      apply s.2.right_injOn y hedge hf
      have hsub :
          (⟨s.1 edge, hmem edge⟩ : P) = ⟨s.1 f, hmem f⟩ :=
        eP.injective hEq
      exact congrArg Subtype.val hsub
  let backward : (uniform G k hG).AdmissibleLabeling → L.AdmissibleLabeling := fun s => by
    let τ : E → Λ := decodeCommonPalette eP s.1
    refine ⟨τ, ?_⟩
    have hinj := (isAdmissible_uniform_iff k hG s.1).1 s.2
    apply isAdmissible_of_label_mem_of_injOn
    · intro edge
      rw [hlabels (G.left edge)]
      exact (eP.symm (s.1 edge)).2
    · intro x edge hedge f hf hEq
      apply hinj.1 x hedge hf
      apply eP.symm.injective
      apply Subtype.ext
      exact hEq
    · intro y edge hedge f hf hEq
      apply hinj.2 y hedge hf
      apply eP.symm.injective
      apply Subtype.ext
      exact hEq
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    apply Subtype.ext
    funext edge
    simp [forward, backward, eP, decodeCommonPalette, encodeCommonPalette]
  · intro s
    apply Subtype.ext
    funext edge
    simp [forward, backward, eP, decodeCommonPalette, encodeCommonPalette]

/-- Count form of `commonPaletteAdmissibleEquiv`. -/
theorem count_eq_ordinary_of_common_palette
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (L : ExactLeftLists G Λ) (P : Finset Λ)
    (hlabels : ∀ x, L.labels x = P) (hP : P.card = k) :
    L.count = ordinaryCount G k hG := by
  unfold ordinaryCount
  exact count_eq_of_equiv L (uniform G k hG)
    (commonPaletteAdmissibleEquiv G k hG L P hlabels hP)

end BachThesisLean
