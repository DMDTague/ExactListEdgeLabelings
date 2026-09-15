import BachThesisLean.Latin.Defs
import Mathlib.Data.Fintype.Prod

namespace BachThesisLean

open LatinSquare

universe u

/-!
# Symbol relabelling and final-column normalization

The first normalization step in v13.23 Section 4.6 is independent of the
residual graph: relabel the symbols by the inverse of the final-column
permutation.  The code below makes that step explicit.  The stabilizer of
the final symbol is retained as a subtype; identifying it with
`Equiv.Perm (Fin (m - 1))` is a separate finite-indexing lemma.
-/

noncomputable def relabelSymbols
    {m : ℕ} (e : Equiv.Perm (Fin m)) (Q : LatinSquare m) : LatinSquare m where
  entry := fun i j => e (Q.entry i j)
  row_bijective := fun i => e.bijective.comp (Q.row_bijective i)
  column_bijective := fun j => e.bijective.comp (Q.column_bijective j)

@[simp] theorem relabelSymbols_entry
    {m : ℕ} (e : Equiv.Perm (Fin m)) (Q : LatinSquare m)
    (i j : Fin m) :
    (relabelSymbols e Q).entry i j = e (Q.entry i j) := rfl

noncomputable def finalColumnPermutation
    {m : ℕ} (Q : LatinSquare m) (hm : 0 < m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun i => Q.entry i (lastIndex m hm))
    (Q.column_bijective (lastIndex m hm))

@[simp] theorem finalColumnPermutation_apply
    {m : ℕ} (Q : LatinSquare m) (hm : 0 < m) (i : Fin m) :
    finalColumnPermutation Q hm i = Q.entry i (lastIndex m hm) := rfl

theorem finalColumnPermutation_last
    {m : ℕ} {hm : 0 < m} (Q : ConstantDiagonalClass m hm) :
    finalColumnPermutation Q.1 hm (lastIndex m hm) = lastSymbol m hm := by
  simpa [finalColumnPermutation, IsConstantDiagonalSquare,
    IsConstantDiagonal] using Q.2 (lastIndex m hm)

def LastFixingPerm (m : ℕ) (hm : 0 < m) :=
  {p : Equiv.Perm (Fin m) // p (lastSymbol m hm) = lastSymbol m hm}

noncomputable def normalizeFinalColumn
    {m : ℕ} {hm : 0 < m} (Q : ConstantDiagonalClass m hm) :
    CanonicalClass m hm := by
  let p : Equiv.Perm (Fin m) := finalColumnPermutation Q.1 hm
  have hp : p (lastSymbol m hm) = lastSymbol m hm := by
    exact finalColumnPermutation_last Q
  have hpinv : p.symm (lastSymbol m hm) = lastSymbol m hm := by
    apply p.injective
    simpa [hp] using p.apply_symm_apply (lastSymbol m hm)
  refine ⟨relabelSymbols p.symm Q.1, ?_⟩
  constructor
  · intro i
    change p.symm (Q.1.entry i i) = lastSymbol m hm
    have hdiag : Q.1.entry i i = lastSymbol m hm := by
      exact Q.2 i
    rw [hdiag]
    exact hpinv
  · intro i
    change p.symm (Q.1.entry i (lastIndex m hm)) = i
    have hcol : Q.1.entry i (lastIndex m hm) = p i := by
      rfl
    rw [hcol]
    exact p.symm_apply_apply i

noncomputable def denormalizeFinalColumn
    {m : ℕ} {hm : 0 < m}
    (P : LastFixingPerm m hm × CanonicalClass m hm) :
    ConstantDiagonalClass m hm := by
  refine ⟨relabelSymbols P.1.1 P.2.1, ?_⟩
  intro i
  change P.1.1 (P.2.1.entry i i) = lastSymbol m hm
  rw [P.2.2.1 i]
  exact P.1.2

noncomputable def normalizationPair
    {m : ℕ} {hm : 0 < m} (Q : ConstantDiagonalClass m hm) :
    LastFixingPerm m hm × CanonicalClass m hm :=
  let p : Equiv.Perm (Fin m) := finalColumnPermutation Q.1 hm
  (⟨p, finalColumnPermutation_last Q⟩, normalizeFinalColumn Q)

theorem denormalize_normalizationPair
    {m : ℕ} {hm : 0 < m} (Q : ConstantDiagonalClass m hm) :
    denormalizeFinalColumn (normalizationPair Q) = Q := by
  apply Subtype.ext
  apply LatinSquare.ext
  intro i j
  simp [denormalizeFinalColumn, normalizationPair, normalizeFinalColumn,
    relabelSymbols]

theorem normalizationPair_denormalize
    {m : ℕ} {hm : 0 < m}
    (P : LastFixingPerm m hm × CanonicalClass m hm) :
    normalizationPair (denormalizeFinalColumn P) = P := by
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    have hlast (j : Fin m) :
        P.2.1.entry j (lastIndex m hm) = j := by
      exact P.2.2.2 j
    simp [normalizationPair, denormalizeFinalColumn, finalColumnPermutation,
      relabelSymbols, hlast]
  · apply Subtype.ext
    apply LatinSquare.ext
    intro i j
    have hlast (k : Fin m) :
        P.2.1.entry k (lastIndex m hm) = k := by
      exact P.2.2.2 k
    simp [normalizationPair, denormalizeFinalColumn, normalizeFinalColumn,
      finalColumnPermutation, relabelSymbols, hlast]

noncomputable def normalizationEquiv
    {m : ℕ} (hm : 0 < m) :
    ConstantDiagonalClass m hm ≃
      LastFixingPerm m hm × CanonicalClass m hm where
  toFun := normalizationPair
  invFun := denormalizeFinalColumn
  left_inv := denormalize_normalizationPair
  right_inv := normalizationPair_denormalize

theorem card_constantDiagonalClass
    {m : ℕ} (hm : 0 < m)
    [Fintype (ConstantDiagonalClass m hm)]
    [Fintype (LastFixingPerm m hm)]
    [Fintype (CanonicalClass m hm)] :
    Fintype.card (ConstantDiagonalClass m hm) =
      Fintype.card (LastFixingPerm m hm) *
        Fintype.card (CanonicalClass m hm) := by
  rw [Fintype.card_congr (normalizationEquiv hm), Fintype.card_prod]

end BachThesisLean
