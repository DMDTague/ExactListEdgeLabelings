import BachThesisLean.Latin.Counting

namespace BachThesisLean

open LatinSquare

/-!
# Normalizing an arbitrary Latin square

The occurrences of the final symbol form a permutation matrix. Reorder
columns by that permutation to put the final symbol on the diagonal.
Keeping the column permutation makes this operation invertible. Combined
with the other two normalization equivalences, this proves the usual
`L m = m! * (m - 1)! * ρ m` formula without an enumeration assumption.
-/

noncomputable def rowPermutation {m : ℕ} (Q : LatinSquare m)
    (r : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (Q.entry r) (Q.row_bijective r)

@[simp] theorem rowPermutation_apply {m : ℕ} (Q : LatinSquare m)
    (r c : Fin m) : rowPermutation Q r c = Q.entry r c := rfl

/-- The column containing symbol `s` in each row. -/
noncomputable def symbolPositionPermutation {m : ℕ} (Q : LatinSquare m)
    (s : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun r => (rowPermutation Q r).symm s) (by
    constructor
    · intro r t h
      change (rowPermutation Q r).symm s = (rowPermutation Q t).symm s at h
      have hr := (rowPermutation Q r).apply_symm_apply s
      have ht := (rowPermutation Q t).apply_symm_apply s
      change Q.entry r ((rowPermutation Q r).symm s) = s at hr
      change Q.entry t ((rowPermutation Q t).symm s) = s at ht
      rw [← h] at ht
      exact (Q.column_bijective _).1 (hr.trans ht.symm)
    · intro c
      obtain ⟨r, hr⟩ := (Q.column_bijective c).2 s
      refine ⟨r, ?_⟩
      apply (rowPermutation Q r).injective
      simpa using hr.symm)

theorem symbolPositionPermutation_eq_iff {m : ℕ} (Q : LatinSquare m)
    (s r c : Fin m) :
    symbolPositionPermutation Q s r = c ↔ Q.entry r c = s := by
  change (rowPermutation Q r).symm s = c ↔ rowPermutation Q r c = s
  exact (Equiv.symm_apply_eq _).trans eq_comm

@[simp] theorem entry_symbolPositionPermutation {m : ℕ} (Q : LatinSquare m)
    (s r : Fin m) : Q.entry r (symbolPositionPermutation Q s r) = s :=
  (rowPermutation Q r).apply_symm_apply s

def permuteColumns {m : ℕ} (e : Equiv.Perm (Fin m)) (Q : LatinSquare m) :
    LatinSquare m where
  entry := fun r c => Q.entry r (e c)
  row_bijective := fun r => (Q.row_bijective r).comp e.bijective
  column_bijective := fun c => Q.column_bijective (e c)

noncomputable def normalizeDiagonal {m : ℕ} (hm : 0 < m) (Q : LatinSquare m) :
    ConstantDiagonalClass m hm :=
  ⟨permuteColumns (symbolPositionPermutation Q (lastSymbol m hm)) Q,
    fun r => entry_symbolPositionPermutation Q (lastSymbol m hm) r⟩

noncomputable def diagonalNormalizationPair {m : ℕ} (hm : 0 < m)
    (Q : LatinSquare m) : Equiv.Perm (Fin m) × ConstantDiagonalClass m hm :=
  (symbolPositionPermutation Q (lastSymbol m hm), normalizeDiagonal hm Q)

def denormalizeDiagonal {m : ℕ} {hm : 0 < m}
    (P : Equiv.Perm (Fin m) × ConstantDiagonalClass m hm) : LatinSquare m :=
  permuteColumns P.1.symm P.2.1

theorem denormalize_diagonalNormalizationPair {m : ℕ} (hm : 0 < m)
    (Q : LatinSquare m) :
    denormalizeDiagonal (diagonalNormalizationPair hm Q) = Q := by
  ext r c
  simp [denormalizeDiagonal, diagonalNormalizationPair, normalizeDiagonal, permuteColumns]

@[simp] theorem symbolPositionPermutation_denormalizeDiagonal {m : ℕ} {hm : 0 < m}
    (P : Equiv.Perm (Fin m) × ConstantDiagonalClass m hm) :
    symbolPositionPermutation (denormalizeDiagonal P) (lastSymbol m hm) = P.1 := by
  apply Equiv.ext
  intro r
  apply (symbolPositionPermutation_eq_iff _ _ _ _).2
  change P.2.1.entry r (P.1.symm (P.1 r)) = lastSymbol m hm
  simpa using P.2.2 r

theorem diagonalNormalizationPair_denormalize {m : ℕ} {hm : 0 < m}
    (P : Equiv.Perm (Fin m) × ConstantDiagonalClass m hm) :
    diagonalNormalizationPair hm (denormalizeDiagonal P) = P := by
  apply Prod.ext
  · exact symbolPositionPermutation_denormalizeDiagonal P
  · apply Subtype.ext
    apply LatinSquare.ext
    intro r c
    change P.2.1.entry r (P.1.symm
      (symbolPositionPermutation (denormalizeDiagonal P) (lastSymbol m hm) c)) =
      P.2.1.entry r c
    rw [symbolPositionPermutation_denormalizeDiagonal]
    simp

noncomputable def diagonalNormalizationEquiv {m : ℕ} (hm : 0 < m) :
    LatinSquare m ≃ Equiv.Perm (Fin m) × ConstantDiagonalClass m hm where
  toFun := diagonalNormalizationPair hm
  invFun := denormalizeDiagonal
  left_inv := denormalize_diagonalNormalizationPair hm
  right_inv := diagonalNormalizationPair_denormalize

/-- Complete constructive normalization with the two permutation factors retained. -/
noncomputable def totalNormalizationEquiv {m : ℕ} (hm : 0 < m) :
    LatinSquare m ≃
      Equiv.Perm (Fin m) × (Equiv.Perm (Fin (m - 1)) × ReducedClass m hm) :=
  (diagonalNormalizationEquiv hm).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((normalizationEquiv hm).trans
        (Equiv.prodCongr (lastFixingPermEquiv m hm) (canonicalReducedEquiv hm))))

theorem L_eq_factorial_mul_V (m : ℕ) (hm : 0 < m) :
    L m = Nat.factorial m * V m hm := by
  rw [L_eq_card, V_eq_card, Fintype.card_congr (diagonalNormalizationEquiv hm),
    Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]

theorem L_eq_factorial_mul_factorial_mul_rho (m : ℕ) (hm : 0 < m) :
    L m = Nat.factorial m * Nat.factorial (m - 1) * ρ m hm := by
  rw [L_eq_factorial_mul_V m hm, V_eq_factorial_mul_rho, Nat.mul_assoc]

end BachThesisLean
