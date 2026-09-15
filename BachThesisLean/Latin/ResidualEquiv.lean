import BachThesisLean.Latin.ResidualCanonical
import BachThesisLean.Latin.Counting

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists LatinSquare

/-!
# Residual labelings are exactly canonical Latin squares

This file proves the inverse direction of the residual completion.  The final
row is forced column-by-column: its non-final entry is the unique residual
symbol absent from the upper part of that column.
-/

/-- A non-final entry in the final row is not the final symbol, since that
symbol already occurs at the final diagonal position. -/
theorem canonical_lastRow_nonfinal_ne_last
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n)) (j : Fin n) :
    Q.1.entry (Fin.last n) j.castSucc ≠ Fin.last n := by
  intro h
  have hdiag :
      Q.1.entry (Fin.last n) (Fin.last n) = Fin.last n := by
    simpa using Q.2.1 (Fin.last n)
  have hcols := (Q.1.row_bijective (Fin.last n)).1 (h.trans hdiag.symm)
  exact (Fin.castSucc_ne_last j) hcols

/-- The residual symbol represented by a non-final entry of the final row. -/
noncomputable def canonicalLastRowLabel
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (j : Fin n) : Fin n :=
  (Q.1.entry (Fin.last n) j.castSucc).castPred
    (canonical_lastRow_nonfinal_ne_last Q j)

@[simp] theorem canonicalLastRowLabel_castSucc
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (j : Fin n) :
    (canonicalLastRowLabel Q j).castSucc =
      Q.1.entry (Fin.last n) j.castSucc := by
  simp [canonicalLastRowLabel]

/-- The final-row residual symbol is absent from the corresponding upper
column.  Otherwise column injectivity would identify a non-final row with the
final row. -/
theorem canonicalLastRowLabel_not_used
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (j : Fin n) :
    canonicalLastRowLabel Q j ∉
      labelsUsedAtRight (crownGraph n) (canonicalResidualLabels Q) j := by
  intro hused
  obtain ⟨e, he, hlabel⟩ :=
    (mem_labelsUsedAtRight (crownGraph n) (canonicalResidualLabels Q) j
      (canonicalLastRowLabel Q j)).1 hused
  have he' := ((crownGraph n).mem_rightIncident j e).1 he
  change e.1.2 = j at he'
  have hentry :
      Q.1.entry e.1.1.castSucc e.1.2.castSucc =
        Q.1.entry (Fin.last n) j.castSucc := by
    calc
      Q.1.entry e.1.1.castSucc e.1.2.castSucc =
          (canonicalResidualLabels Q e).castSucc :=
        (canonicalResidualLabels_castSucc Q e).symm
      _ = (canonicalLastRowLabel Q j).castSucc :=
        congrArg (fun c : Fin n => c.castSucc) hlabel
      _ = Q.1.entry (Fin.last n) j.castSucc :=
        canonicalLastRowLabel_castSucc Q j
  rw [he'] at hentry
  have hrow := (Q.1.column_bijective j.castSucc).1 hentry
  exact (Fin.castSucc_ne_last e.1.1) hrow

/-- For the residual labeling extracted from a canonical square, the chosen
missing label of column `j` is exactly the label encoded in the final row. -/
theorem residualMissingLabel_canonicalToResidual
    {n : ℕ} (hn : 0 < n)
    (Q : CanonicalClass (n + 1) (Nat.succ_pos n)) (j : Fin n) :
    residualMissingLabel hn (canonicalToResidual Q) j =
      canonicalLastRowLabel Q j := by
  apply residualMissingLabel_eq_of_not_used hn (canonicalToResidual Q) j
  change canonicalLastRowLabel Q j ∉
    labelsUsedAtRight (crownGraph n) (canonicalResidualLabels Q) j
  exact canonicalLastRowLabel_not_used Q j

/-- Completing the residual labeling extracted from a canonical square returns
the original square. -/
theorem canonical_residual_roundtrip
    {n : ℕ} (hn : 0 < n)
    (Q : CanonicalClass (n + 1) (Nat.succ_pos n)) :
    residualToCanonical hn (canonicalToResidual Q) = Q := by
  apply Subtype.ext
  apply LatinSquare.ext
  intro i j
  change residualFilledEntry hn (canonicalToResidual Q) i j = Q.1.entry i j
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last =>
          rw [residualFilledEntry_last_last]
          have hd := Q.2.1 (Fin.last n)
          simpa using hd.symm
      | cast j =>
          rw [residualFilledEntry_last_castSucc,
            residualMissingLabel_canonicalToResidual hn Q j,
            canonicalLastRowLabel_castSucc]
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [residualFilledEntry_castSucc_last]
          have hf := Q.2.2 i.castSucc
          simpa using hf.symm
      | cast j =>
          by_cases hij : i = j
          · subst j
            rw [residualFilledEntry_castSucc_diagonal]
            have hd := Q.2.1 i.castSucc
            simpa using hd.symm
          · rw [residualFilledEntry_castSucc_offDiagonal hn
              (canonicalToResidual Q) i j hij]
            change (canonicalResidualLabels Q ⟨(i, j), hij⟩).castSucc =
              Q.1.entry i.castSucc j.castSucc
            exact canonicalResidualLabels_castSucc Q ⟨(i, j), hij⟩

/-- The manuscript's residual completion/deletion correspondence as an actual
finite equivalence. -/
noncomputable def residualCanonicalEquiv
    {n : ℕ} (hn : 0 < n) :
    CrownResidualLabeling n ≃
      CanonicalClass (n + 1) (Nat.succ_pos n) where
  toFun := residualToCanonical hn
  invFun := canonicalToResidual
  left_inv := residual_canonical_roundtrip hn
  right_inv := canonical_residual_roundtrip hn

/-- The residual exact-list count is the canonical Latin-square count of the
next order: `N_{n-1}(R_n) = U_{n+1}` in the manuscript's notation. -/
theorem crownResidual_count_eq_U (n : ℕ) (hn : 0 < n) :
    (crownResidualLists n).count = U (n + 1) (Nat.succ_pos n) := by
  rw [count_eq_card, U_eq_card]
  exact Fintype.card_congr (residualCanonicalEquiv hn)

end BachThesisLean
