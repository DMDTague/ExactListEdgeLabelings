import BachThesisLean.Basic.ExactLists

namespace BachThesisLean

open BipartiteMultigraph

namespace ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable {G : BipartiteMultigraph X Y E}

/-!
# Exact use, injectivity, and finite counting

The image formulation in `IsAdmissible` enforces the manuscript's “each
once” requirement because an exact list has the same cardinality as the
incident edge set.  The lemmas below make that argument explicit; equality
of image sets alone would not imply injectivity without exactness.
-/

omit [Fintype X] [Fintype Y] [Fintype Λ] in
theorem right_card_eq_iff_injOn (σ : E → Λ) (y : Y) :
    (G.rightIncident y).card = (labelsUsedAtRight G σ y).card ↔
      Set.InjOn σ (G.rightIncident y) := by
  classical
  simpa [labelsUsedAtRight, eq_comm] using
    (Finset.card_image_iff (s := G.rightIncident y) (f := σ))

theorem isAdmissible_iff_right_injOn (L : ExactLeftLists G Λ) (σ : E → Λ) :
    L.IsAdmissible σ ↔
      (∀ x, labelsUsedAtLeft G σ x = L.labels x) ∧
      (∀ y, Set.InjOn σ (G.rightIncident y)) := by
  simp only [IsAdmissible, right_card_eq_iff_injOn]

theorem IsAdmissible.left_injOn {L : ExactLeftLists G Λ} {σ : E → Λ}
    (h : L.IsAdmissible σ) (x : X) :
    Set.InjOn σ (G.leftIncident x) := by
  classical
  apply Finset.card_image_iff.mp
  change (labelsUsedAtLeft G σ x).card = (G.leftIncident x).card
  rw [h.1 x, L.card_labels x]
  rfl

theorem IsAdmissible.right_injOn {L : ExactLeftLists G Λ} {σ : E → Λ}
    (h : L.IsAdmissible σ) (y : Y) :
    Set.InjOn σ (G.rightIncident y) :=
  (right_card_eq_iff_injOn σ y).mp (h.2 y)

theorem IsAdmissible.rightDegree_le_card {L : ExactLeftLists G Λ} {σ : E → Λ}
    (h : L.IsAdmissible σ) (y : Y) : G.rightDegree y ≤ Fintype.card Λ := by
  classical
  rw [rightDegree, h.2 y]
  exact Finset.card_le_univ _

theorem IsAdmissible.label_mem {L : ExactLeftLists G Λ} {σ : E → Λ}
    (h : L.IsAdmissible σ) (e : E) : σ e ∈ L.labels (G.left e) := by
  classical
  rw [← h.1]
  exact Finset.mem_image.mpr ⟨e, (G.mem_leftIncident _ _).mpr rfl, rfl⟩

/-- To prove admissibility it is enough to prove pointwise list membership
and injectivity on every left and right incidence set. Exactness upgrades the
left-side inclusion to equality of the used-label set with the prescribed
list. -/
theorem isAdmissible_of_label_mem_of_injOn
    (L : ExactLeftLists G Λ) (σ : E → Λ)
    (hmem : ∀ e, σ e ∈ L.labels (G.left e))
    (hleft : ∀ x, Set.InjOn σ (G.leftIncident x))
    (hright : ∀ y, Set.InjOn σ (G.rightIncident y)) :
    L.IsAdmissible σ := by
  classical
  apply (isAdmissible_iff_right_injOn L σ).2
  refine ⟨?_, hright⟩
  intro x
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    change c ∈ (G.leftIncident x).image σ at hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    have hxe : G.left e = x := (G.mem_leftIncident x e).1 he
    simpa [hxe] using hmem e
  · rw [L.card_labels x]
    change (G.leftIncident x).card ≤ (labelsUsedAtLeft G σ x).card
    exact (Finset.card_image_iff.mpr (hleft x)).ge

theorem IsAdmissible.exact_once {L : ExactLeftLists G Λ} {σ : E → Λ}
    (h : L.IsAdmissible σ) (x : X) (c : Λ) (hc : c ∈ L.labels x) :
    ∃! e : E, G.left e = x ∧ σ e = c := by
  classical
  rw [← h.1 x] at hc
  obtain ⟨e, he, hσ⟩ := Finset.mem_image.mp hc
  refine ⟨e, ⟨(G.mem_leftIncident x e).mp he, hσ⟩, ?_⟩
  intro e' he'
  exact h.left_injOn x ((G.mem_leftIncident x e').mpr he'.1) he
    (he'.2.trans hσ.symm)

/-- On a left-regular graph, the uniform exact-list model is precisely proper
edge colouring with the fixed palette `Fin k`, including the case `k = 0`. -/
theorem isAdmissible_uniform_iff (k : ℕ) (hG : G.IsLeftRegular k)
    (σ : E → Fin k) :
    (uniform G k hG).IsAdmissible σ ↔
      (∀ x, Set.InjOn σ (G.leftIncident x)) ∧
      (∀ y, Set.InjOn σ (G.rightIncident y)) := by
  classical
  constructor
  · intro h
    exact ⟨h.left_injOn, h.right_injOn⟩
  · rintro ⟨hleft, hright⟩
    letI : DecidableEq (Fin k) := Classical.decEq _
    apply (isAdmissible_iff_right_injOn _ _).mpr
    refine ⟨?_, hright⟩
    intro x
    simp only [uniform, labelsUsedAtLeft]
    apply Finset.eq_univ_of_card
    have hcard := Finset.card_image_iff.mpr (hleft x)
    have hdegree : (G.leftIncident x).card = Fintype.card (Fin k) := by
      simpa only [Fintype.card_fin] using hG x
    exact hcard.trans hdegree

/-- The genuinely finite type counted by `count`. Edge copies stay distinct. -/
abbrev AdmissibleLabeling (L : ExactLeftLists G Λ) :=
  {σ : E → Λ // L.IsAdmissible σ}

noncomputable instance admissibleLabelingFintype (L : ExactLeftLists G Λ) :
    Fintype L.AdmissibleLabeling := by
  classical
  infer_instance

theorem count_eq_card (L : ExactLeftLists G Λ) :
    L.count = Fintype.card L.AdmissibleLabeling := by
  classical
  simp [count, admissibleLabelings, AdmissibleLabeling, Fintype.card_subtype]

theorem count_pos_iff (L : ExactLeftLists G Λ) :
    0 < L.count ↔ ∃ σ : E → Λ, L.IsAdmissible σ := by
  classical
  simp [count, Finset.card_pos, Finset.Nonempty, mem_admissibleLabelings]

theorem count_eq_zero_iff (L : ExactLeftLists G Λ) :
    L.count = 0 ↔ ∀ σ : E → Λ, ¬ L.IsAdmissible σ := by
  rw [← not_iff_not]
  simp [← count_pos_iff, Nat.pos_iff_ne_zero]

/-- The palette obstruction used in the first case of the two-label fibre
analysis: a right vertex cannot receive more distinct labels than exist. -/
theorem count_eq_zero_of_rightDegree_gt_card (L : ExactLeftLists G Λ)
    (y : Y) (hy : Fintype.card Λ < G.rightDegree y) : L.count = 0 := by
  apply (count_eq_zero_iff L).mpr
  intro σ hσ
  exact Nat.not_le_of_lt hy (hσ.rightDegree_le_card y)

/-- A counting implication with the required combinatorial injection explicit. -/
theorem count_le_of_injective
    {Γ : Type*} [Fintype Γ] (L : ExactLeftLists G Λ) (M : ExactLeftLists G Γ)
    (f : L.AdmissibleLabeling → M.AdmissibleLabeling)
    (hf : Function.Injective f) : L.count ≤ M.count := by
  rw [count_eq_card, count_eq_card]
  exact Fintype.card_le_of_injective f hf

theorem count_eq_of_equiv
    {Γ : Type*} [Fintype Γ] (L : ExactLeftLists G Λ) (M : ExactLeftLists G Γ)
    (e : L.AdmissibleLabeling ≃ M.AdmissibleLabeling) : L.count = M.count := by
  rw [count_eq_card, count_eq_card]
  exact Fintype.card_congr e

end ExactLeftLists
end BachThesisLean
