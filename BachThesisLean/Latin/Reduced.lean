import BachThesisLean.Latin.Bijections
import Mathlib.Logic.Equiv.Fin.Rotate

namespace BachThesisLean

open LatinSquare

/-!
# The canonical and reduced classes

The first operation is precisely the row-symbol conjugation from v13.23:
`Q' s c = r` if and only if `Q r c = s`. Thus it inverts each column
permutation (the row index and the symbol exchange roles). The final
simultaneous relabelling sends the distinguished last index to the first.
-/

noncomputable def columnPermutation {m : ℕ} (Q : LatinSquare m)
    (c : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun r => Q.entry r c) (Q.column_bijective c)

@[simp] theorem columnPermutation_apply {m : ℕ} (Q : LatinSquare m)
    (c r : Fin m) : columnPermutation Q c r = Q.entry r c := rfl

noncomputable def rowSymbolConjugate {m : ℕ} (Q : LatinSquare m) :
    LatinSquare m where
  entry := fun s c => (columnPermutation Q c).symm s
  row_bijective := by
    intro s
    constructor
    · intro c d h
      change (columnPermutation Q c).symm s = (columnPermutation Q d).symm s at h
      have hc := (columnPermutation Q c).apply_symm_apply s
      have hd := (columnPermutation Q d).apply_symm_apply s
      change Q.entry ((columnPermutation Q c).symm s) c = s at hc
      change Q.entry ((columnPermutation Q d).symm s) d = s at hd
      rw [← h] at hd
      exact (Q.row_bijective _).1 (hc.trans hd.symm)
    · intro r
      obtain ⟨c, hc⟩ := (Q.row_bijective r).2 s
      refine ⟨c, ?_⟩
      apply (columnPermutation Q c).injective
      simpa using hc.symm
  column_bijective := fun c => (columnPermutation Q c).symm.bijective

@[simp] theorem rowSymbolConjugate_entry {m : ℕ} (Q : LatinSquare m)
    (s c : Fin m) :
    (rowSymbolConjugate Q).entry s c = (columnPermutation Q c).symm s := rfl

theorem rowSymbolConjugate_entry_iff {m : ℕ} (Q : LatinSquare m)
    (s c r : Fin m) :
    (rowSymbolConjugate Q).entry s c = r ↔ Q.entry r c = s := by
  change (columnPermutation Q c).symm s = r ↔ columnPermutation Q c r = s
  exact (Equiv.symm_apply_eq _).trans eq_comm

@[simp] theorem rowSymbolConjugate_involutive {m : ℕ} (Q : LatinSquare m) :
    rowSymbolConjugate (rowSymbolConjugate Q) = Q := by
  apply LatinSquare.ext
  intro r c
  apply (rowSymbolConjugate_entry_iff _ _ _ _).2
  apply (rowSymbolConjugate_entry_iff _ _ _ _).2
  rfl

def LastReducedClass (m : ℕ) (hm : 0 < m) :=
  {Q : LatinSquare m //
    (∀ c, Q.entry (lastIndex m hm) c = c) ∧
    (∀ r, Q.entry r (lastIndex m hm) = r)}

noncomputable def canonicalToLastReduced {m : ℕ} {hm : 0 < m}
    (Q : CanonicalClass m hm) : LastReducedClass m hm := by
  refine ⟨rowSymbolConjugate Q.1, ?_, ?_⟩
  · intro c
    exact (rowSymbolConjugate_entry_iff _ _ _ _).2 (Q.2.1 c)
  · intro r
    exact (rowSymbolConjugate_entry_iff _ _ _ _).2 (Q.2.2 r)

noncomputable def lastReducedToCanonical {m : ℕ} {hm : 0 < m}
    (Q : LastReducedClass m hm) : CanonicalClass m hm := by
  refine ⟨rowSymbolConjugate Q.1, ?_, ?_⟩
  · intro c
    exact (rowSymbolConjugate_entry_iff _ _ _ _).2 (Q.2.1 c)
  · intro r
    exact (rowSymbolConjugate_entry_iff _ _ _ _).2 (Q.2.2 r)

noncomputable def canonicalLastReducedEquiv {m : ℕ} (hm : 0 < m) :
    CanonicalClass m hm ≃ LastReducedClass m hm where
  toFun := canonicalToLastReduced
  invFun := lastReducedToCanonical
  left_inv Q := by
    apply Subtype.ext
    exact rowSymbolConjugate_involutive Q.1
  right_inv Q := by
    apply Subtype.ext
    exact rowSymbolConjugate_involutive Q.1

noncomputable def simultaneousRelabel {m : ℕ} (e : Equiv.Perm (Fin m))
    (Q : LatinSquare m) : LatinSquare m where
  entry := fun i j => e (Q.entry (e.symm i) (e.symm j))
  row_bijective := fun i => e.bijective.comp
    ((Q.row_bijective (e.symm i)).comp e.symm.bijective)
  column_bijective := fun j => e.bijective.comp
    ((Q.column_bijective (e.symm j)).comp e.symm.bijective)

@[simp] theorem simultaneousRelabel_symm {m : ℕ} (e : Equiv.Perm (Fin m))
    (Q : LatinSquare m) :
    simultaneousRelabel e.symm (simultaneousRelabel e Q) = Q := by
  ext i j
  simp [simultaneousRelabel]

/-- The manuscript's cycle, adding one and sending the final index to zero. -/
def normalizationCycle (m : ℕ) : Equiv.Perm (Fin m) := finRotate m

@[simp] theorem normalizationCycle_last (m : ℕ) (hm : 0 < m) :
    normalizationCycle m (lastIndex m hm) = firstIndex m hm := by
  cases m with
  | zero => omega
  | succ n => simpa [normalizationCycle, lastIndex, firstIndex] using
      (finRotate_last' (n := n))

@[simp] theorem normalizationCycle_symm_first (m : ℕ) (hm : 0 < m) :
    (normalizationCycle m).symm (firstIndex m hm) = lastIndex m hm := by
  apply (normalizationCycle m).injective
  simp

noncomputable def lastReducedToReduced {m : ℕ} {hm : 0 < m}
    (Q : LastReducedClass m hm) : ReducedClass m hm := by
  refine ⟨simultaneousRelabel (normalizationCycle m) Q.1, ?_, ?_⟩
  · intro c
    simp only [simultaneousRelabel, normalizationCycle_symm_first]
    rw [Q.2.1]
    exact (normalizationCycle m).apply_symm_apply c
  · intro r
    simp only [simultaneousRelabel, normalizationCycle_symm_first]
    rw [Q.2.2]
    exact (normalizationCycle m).apply_symm_apply r

noncomputable def reducedToLastReduced {m : ℕ} {hm : 0 < m}
    (Q : ReducedClass m hm) : LastReducedClass m hm := by
  refine ⟨simultaneousRelabel (normalizationCycle m).symm Q.1, ?_, ?_⟩
  · intro c
    simp only [simultaneousRelabel, Equiv.symm_symm, normalizationCycle_last]
    rw [Q.2.1]
    exact (normalizationCycle m).symm_apply_apply c
  · intro r
    simp only [simultaneousRelabel, Equiv.symm_symm, normalizationCycle_last]
    rw [Q.2.2]
    exact (normalizationCycle m).symm_apply_apply r

noncomputable def lastReducedEquiv {m : ℕ} (hm : 0 < m) :
    LastReducedClass m hm ≃ ReducedClass m hm where
  toFun := lastReducedToReduced
  invFun := reducedToLastReduced
  left_inv Q := by
    apply Subtype.ext
    exact simultaneousRelabel_symm (normalizationCycle m) Q.1
  right_inv Q := by
    apply Subtype.ext
    exact simultaneousRelabel_symm (normalizationCycle m).symm Q.1

noncomputable def canonicalReducedEquiv {m : ℕ} (hm : 0 < m) :
    CanonicalClass m hm ≃ ReducedClass m hm :=
  (canonicalLastReducedEquiv hm).trans (lastReducedEquiv hm)

end BachThesisLean
