import BachThesisLean.Latin.Residual

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

/-!
# Column structure of the completed residual array

The residual completion already gives every non-final row as a permutation.
This file proves the dual column facts needed to control the final row.
-/

/-- The upper-left part of each non-final column is injective. -/
theorem residualFilledEntry_upperLeft_column_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) :
    Function.Injective (fun i : Fin n =>
      residualFilledEntry hn σ i.castSucc j.castSucc) := by
  intro i k h
  by_cases hij : i = j
  · subst i
    by_cases hkj : k = j
    · exact hkj.symm
    · change residualFilledEntry hn σ j.castSucc j.castSucc =
        residualFilledEntry hn σ k.castSucc j.castSucc at h
      rw [residualFilledEntry_castSucc_diagonal,
        residualFilledEntry_castSucc_offDiagonal hn σ k j hkj] at h
      exact False.elim ((Fin.castSucc_ne_last (σ.1 ⟨(k, j), hkj⟩)) h.symm)
  · by_cases hkj : k = j
    · subst k
      change residualFilledEntry hn σ i.castSucc j.castSucc =
        residualFilledEntry hn σ j.castSucc j.castSucc at h
      rw [residualFilledEntry_castSucc_offDiagonal hn σ i j hij,
        residualFilledEntry_castSucc_diagonal] at h
      exact False.elim ((Fin.castSucc_ne_last (σ.1 ⟨(i, j), hij⟩)) h)
    · change residualFilledEntry hn σ i.castSucc j.castSucc =
        residualFilledEntry hn σ k.castSucc j.castSucc at h
      rw [residualFilledEntry_castSucc_offDiagonal hn σ i j hij,
        residualFilledEntry_castSucc_offDiagonal hn σ k j hkj] at h
      have hσ : σ.1 ⟨(i, j), hij⟩ = σ.1 ⟨(k, j), hkj⟩ :=
        (Fin.castSucc_injective n) h
      have he := σ.2.right_injOn j
        ((crownGraph n).mem_rightIncident j ⟨(i, j), hij⟩ |>.2 rfl)
        ((crownGraph n).mem_rightIncident j ⟨(k, j), hkj⟩ |>.2 rfl) hσ
      exact congrArg (fun e : CrownEdge n => e.1.1) he

/-- The appended final-row entry of a non-final column is genuinely new: it
is the unique residual symbol absent from that column. -/
theorem residualFilledEntry_upperLeft_ne_missing
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (i j : Fin n) :
    residualFilledEntry hn σ i.castSucc j.castSucc ≠
      (residualMissingLabel hn σ j).castSucc := by
  by_cases hij : i = j
  · subst i
    rw [residualFilledEntry_castSucc_diagonal]
    exact (Fin.castSucc_ne_last (residualMissingLabel hn σ j)).symm
  · rw [residualFilledEntry_castSucc_offDiagonal hn σ i j hij]
    intro h
    have hσ : σ.1 ⟨(i, j), hij⟩ = residualMissingLabel hn σ j :=
      (Fin.castSucc_injective n) h
    have hused :
        σ.1 ⟨(i, j), hij⟩ ∈
          labelsUsedAtRight (crownGraph n) σ.1 j :=
      (mem_labelsUsedAtRight (crownGraph n) σ.1 j _).2
        ⟨⟨(i, j), hij⟩,
          ((crownGraph n).mem_rightIncident j ⟨(i, j), hij⟩).2 rfl, rfl⟩
    have hmissing := residualMissingLabel_not_used hn σ j
    apply hmissing
    simpa [hσ] using hused

/-- Every non-final column of the completed array is injective, including its
appended missing-symbol entry in the final row. -/
theorem residualFilledEntry_nonfinalColumn_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) :
    Function.Injective (fun i : Fin (n + 1) =>
      residualFilledEntry hn σ i j.castSucc) := by
  intro i k h
  induction i using Fin.lastCases with
  | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k =>
          have hk := residualFilledEntry_upperLeft_ne_missing hn σ k j
          simp only [residualFilledEntry_last_castSucc] at h
          exact False.elim (hk h.symm)
  | cast i =>
      induction k using Fin.lastCases with
      | last =>
          have hi := residualFilledEntry_upperLeft_ne_missing hn σ i j
          simp only [residualFilledEntry_last_castSucc] at h
          exact False.elim (hi h)
      | cast k =>
          have hik := residualFilledEntry_upperLeft_column_injective hn σ j h
          exact congrArg (fun x : Fin n => x.castSucc) hik

/-- The final column is the identity column, hence injective. -/
theorem residualFilledEntry_lastColumn_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    Function.Injective (fun i : Fin (n + 1) =>
      residualFilledEntry hn σ i (Fin.last n)) := by
  intro i k h
  induction i using Fin.lastCases with
  | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k =>
          simp only [residualFilledEntry_last_last,
            residualFilledEntry_castSucc_last] at h
          exact False.elim ((Fin.castSucc_ne_last k) h.symm)
  | cast i =>
      induction k using Fin.lastCases with
      | last =>
          simp only [residualFilledEntry_last_last,
            residualFilledEntry_castSucc_last] at h
          exact False.elim ((Fin.castSucc_ne_last i) h)
      | cast k =>
          simpa only [residualFilledEntry_castSucc_last] using h

/-- Every column of the completed array is injective. -/
theorem residualFilledEntry_column_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin (n + 1)) :
    Function.Injective (fun i : Fin (n + 1) => residualFilledEntry hn σ i j) := by
  induction j using Fin.lastCases with
  | last => exact residualFilledEntry_lastColumn_injective hn σ
  | cast j => exact residualFilledEntry_nonfinalColumn_injective hn σ j

end BachThesisLean
