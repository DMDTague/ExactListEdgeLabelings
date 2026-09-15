import BachThesisLean.Uncrossing.Canonical

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X]

/-!
# Removing the empty prefix of a canonical support family

If `K ≤ m` and every left degree is at most `K`, the first `m-K` supports of
`canonicalSupport G m` are empty.  Every admissible labeling therefore uses
only the final `K` labels. Subtracting the offset `m-K` gives an explicit
bijection with the canonical `K`-label system.
-/

/-- Embed a canonical `K`-label into the final `K` positions of `Fin m`. -/
def liftCanonicalLabel {m K : ℕ} (hKm : K ≤ m) (j : Fin K) : Fin m :=
  ⟨m - K + j.val, by omega⟩

@[simp] theorem liftCanonicalLabel_val {m K : ℕ} (hKm : K ≤ m) (j : Fin K) :
    (liftCanonicalLabel hKm j).val = m - K + j.val := rfl

/-- Any label actually used by the `m`-slot canonical system lies in its final
`K` positions. -/
theorem canonical_admissible_label_ge_offset
    (G : BipartiteMultigraph X Y E) {m K : ℕ} (hKm : K ≤ m)
    (hdeg : ∀ x, G.leftDegree x ≤ K)
    {σ : E → Fin m}
    (hσ : (exactListsOfSupports (canonicalSupport G m)
      (canonicalSupport_exact G m (fun x => (hdeg x).trans hKm))).IsAdmissible σ)
    (edge : E) :
    m - K ≤ (σ edge).val := by
  have hm := hσ.label_mem edge
  change σ edge ∈ listsOfSupports (canonicalSupport G m) (G.left edge) at hm
  rw [mem_listsOfSupports, mem_canonicalSupport] at hm
  have hd := hdeg (G.left edge)
  omega

/-- Lower an actually used final-`K` label by the empty-prefix offset. -/
noncomputable def lowerCanonicalLabel
    {m K : ℕ} (hKm : K ≤ m) (c : Fin m) (hc : m - K ≤ c.val) : Fin K :=
  ⟨c.val - (m - K), by omega⟩

@[simp] theorem lower_liftCanonicalLabel
    {m K : ℕ} (hKm : K ≤ m) (j : Fin K) :
    lowerCanonicalLabel hKm (liftCanonicalLabel hKm j)
      (by
        change m - K ≤ m - K + j.val
        omega) = j := by
  apply Fin.ext
  simp [lowerCanonicalLabel, liftCanonicalLabel]

/-- The canonical admissible-labeling spaces with `m` slots and with only the
final `K` slots are equivalent. -/
noncomputable def canonicalAdmissibleEquiv
    (G : BipartiteMultigraph X Y E) {m K : ℕ} (hKm : K ≤ m)
    (hdeg : ∀ x, G.leftDegree x ≤ K) :
    (exactListsOfSupports (canonicalSupport G m)
      (canonicalSupport_exact G m (fun x => (hdeg x).trans hKm))).AdmissibleLabeling ≃
      (exactListsOfSupports (canonicalSupport G K)
        (canonicalSupport_exact G K hdeg)).AdmissibleLabeling := by
  classical
  let hM : ExactSupportIncidence G (canonicalSupport G m) :=
    canonicalSupport_exact G m (fun x => (hdeg x).trans hKm)
  let hK : ExactSupportIncidence G (canonicalSupport G K) :=
    canonicalSupport_exact G K hdeg
  let forward :
      (exactListsOfSupports (canonicalSupport G m) hM).AdmissibleLabeling →
        (exactListsOfSupports (canonicalSupport G K) hK).AdmissibleLabeling := fun s => by
    have hoff : ∀ edge, m - K ≤ (s.1 edge).val := by
      intro edge
      exact canonical_admissible_label_ge_offset G hKm hdeg s.2 edge
    let τ : E → Fin K := fun edge => lowerCanonicalLabel hKm (s.1 edge) (hoff edge)
    refine ⟨τ, ?_⟩
    apply isAdmissible_of_label_mem_of_injOn
    · intro edge
      have hm := s.2.label_mem edge
      change s.1 edge ∈ listsOfSupports (canonicalSupport G m) (G.left edge) at hm
      rw [mem_listsOfSupports, mem_canonicalSupport] at hm
      change τ edge ∈ listsOfSupports (canonicalSupport G K) (G.left edge)
      rw [mem_listsOfSupports, mem_canonicalSupport]
      dsimp [τ, lowerCanonicalLabel]
      have ho := hoff edge
      omega
    · intro x edge hedge f hf hEq
      apply s.2.left_injOn x hedge hf
      apply Fin.ext
      change (s.1 edge).val = (s.1 f).val
      have he := congrArg Fin.val hEq
      dsimp [τ, lowerCanonicalLabel] at he
      have heo := hoff edge
      have hfo := hoff f
      omega
    · intro y edge hedge f hf hEq
      apply s.2.right_injOn y hedge hf
      apply Fin.ext
      change (s.1 edge).val = (s.1 f).val
      have he := congrArg Fin.val hEq
      dsimp [τ, lowerCanonicalLabel] at he
      have heo := hoff edge
      have hfo := hoff f
      omega
  let backward :
      (exactListsOfSupports (canonicalSupport G K) hK).AdmissibleLabeling →
        (exactListsOfSupports (canonicalSupport G m) hM).AdmissibleLabeling := fun s => by
    let τ : E → Fin m := fun edge => liftCanonicalLabel hKm (s.1 edge)
    refine ⟨τ, ?_⟩
    apply isAdmissible_of_label_mem_of_injOn
    · intro edge
      have hm := s.2.label_mem edge
      change s.1 edge ∈ listsOfSupports (canonicalSupport G K) (G.left edge) at hm
      rw [mem_listsOfSupports, mem_canonicalSupport] at hm
      change τ edge ∈ listsOfSupports (canonicalSupport G m) (G.left edge)
      rw [mem_listsOfSupports, mem_canonicalSupport]
      dsimp [τ, liftCanonicalLabel]
      omega
    · intro x edge hedge f hf hEq
      apply s.2.left_injOn x hedge hf
      apply Fin.ext
      have he := congrArg Fin.val hEq
      dsimp [τ, liftCanonicalLabel] at he
      omega
    · intro y edge hedge f hf hEq
      apply s.2.right_injOn y hedge hf
      apply Fin.ext
      have he := congrArg Fin.val hEq
      dsimp [τ, liftCanonicalLabel] at he
      omega
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    apply Subtype.ext
    funext edge
    apply Fin.ext
    have ho : m - K ≤ (s.1 edge).val :=
      canonical_admissible_label_ge_offset G hKm hdeg s.2 edge
    simp [forward, backward, lowerCanonicalLabel, liftCanonicalLabel]
    omega
  · intro s
    apply Subtype.ext
    funext edge
    apply Fin.ext
    simp [forward, backward, lowerCanonicalLabel, liftCanonicalLabel]

/-- Empty canonical prefix slots do not affect the completion count. -/
theorem canonicalSupport_count_eq_of_le
    (G : BipartiteMultigraph X Y E) {m K : ℕ} (hKm : K ≤ m)
    (hdeg : ∀ x, G.leftDegree x ≤ K) :
    (exactListsOfSupports (canonicalSupport G m)
      (canonicalSupport_exact G m (fun x => (hdeg x).trans hKm))).count =
      (exactListsOfSupports (canonicalSupport G K)
        (canonicalSupport_exact G K hdeg)).count := by
  exact count_eq_of_equiv _ _ (canonicalAdmissibleEquiv G hKm hdeg)

end BachThesisLean
