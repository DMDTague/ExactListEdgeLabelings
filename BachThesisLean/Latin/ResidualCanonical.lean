import BachThesisLean.Latin.ResidualFinalRow

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists LatinSquare

/-!
# Canonical Latin square attached to a residual labeling

The preceding files construct the completed `(n+1) × (n+1)` array and prove
injectivity of every row and column.  Here it is packaged as a Latin square
and its manuscript normalization conditions are recorded explicitly.
-/

@[simp] theorem lastIndex_succ_eq_last (n : ℕ) :
    lastIndex (n + 1) (Nat.succ_pos n) = Fin.last n := by
  apply Fin.ext
  simp [lastIndex]

@[simp] theorem lastSymbol_succ_eq_last (n : ℕ) :
    lastSymbol (n + 1) (Nat.succ_pos n) = Fin.last n :=
  lastIndex_succ_eq_last n

/-- Every row of the residual completion is injective. -/
theorem residualFilledEntry_row_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (i : Fin (n + 1)) :
    Function.Injective (residualFilledEntry hn σ i) := by
  induction i using Fin.lastCases with
  | last => exact residualFilledEntry_lastRow_injective hn σ
  | cast i => exact residualFilledEntry_upperRow_injective hn σ i

/-- The completed residual array is a Latin square. -/
noncomputable def residualFilledLatinSquare
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    LatinSquare (n + 1) where
  entry := residualFilledEntry hn σ
  row_bijective := fun i =>
    ⟨residualFilledEntry_row_injective hn σ i,
      Finite.surjective_of_injective
        (residualFilledEntry_row_injective hn σ i)⟩
  column_bijective := fun j =>
    ⟨residualFilledEntry_column_injective hn σ j,
      Finite.surjective_of_injective
        (residualFilledEntry_column_injective hn σ j)⟩

/-- The completed square has constant final-symbol diagonal and identity final
column, exactly the canonical normalization used in manuscript v13.23. -/
noncomputable def residualToCanonical
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    CanonicalClass (n + 1) (Nat.succ_pos n) := by
  refine ⟨residualFilledLatinSquare hn σ, ?_⟩
  constructor
  · intro i
    change residualFilledEntry hn σ i i =
      lastSymbol (n + 1) (Nat.succ_pos n)
    rw [lastSymbol_succ_eq_last]
    induction i using Fin.lastCases with
    | last => exact residualFilledEntry_last_last hn σ
    | cast i => exact residualFilledEntry_castSucc_diagonal hn σ i
  · intro i
    change residualFilledEntry hn σ i
      (lastIndex (n + 1) (Nat.succ_pos n)) = i
    rw [lastIndex_succ_eq_last]
    induction i using Fin.lastCases with
    | last => exact residualFilledEntry_last_last hn σ
    | cast i => exact residualFilledEntry_castSucc_last hn σ i

/-- The canonical completion remembers the original residual labeling in its
upper-left off-diagonal block. -/
theorem residualToCanonical_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (residualToCanonical hn) := by
  intro σ τ h
  apply Subtype.ext
  funext e
  have hsq : (residualToCanonical hn σ).1 =
      (residualToCanonical hn τ).1 := congrArg Subtype.val h
  have hentry := congrArg
    (fun Q : LatinSquare (n + 1) =>
      Q.entry e.1.1.castSucc e.1.2.castSucc) hsq
  change residualFilledEntry hn σ e.1.1.castSucc e.1.2.castSucc =
    residualFilledEntry hn τ e.1.1.castSucc e.1.2.castSucc at hentry
  rw [residualFilledEntry_castSucc_offDiagonal hn σ e.1.1 e.1.2 e.2,
    residualFilledEntry_castSucc_offDiagonal hn τ e.1.1 e.1.2 e.2] at hentry
  exact Fin.castSucc_injective n hentry

/-- An upper-left off-diagonal entry of a canonical square cannot be the final
symbol, because that symbol already occurs on the diagonal of its row. -/
theorem canonical_upperLeft_offDiagonal_ne_last
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (e : CrownEdge n) :
    Q.1.entry e.1.1.castSucc e.1.2.castSucc ≠ Fin.last n := by
  intro h
  have hdiag :
      Q.1.entry e.1.1.castSucc e.1.1.castSucc = Fin.last n := by
    simpa using Q.2.1 e.1.1.castSucc
  have heq :
      Q.1.entry e.1.1.castSucc e.1.2.castSucc =
        Q.1.entry e.1.1.castSucc e.1.1.castSucc := h.trans hdiag.symm
  have hcol := (Q.1.row_bijective e.1.1.castSucc).1 heq
  exact e.2 (Fin.castSucc_injective n hcol).symm

/-- Delete the final symbol from an upper-left off-diagonal entry. -/
noncomputable def canonicalResidualLabels
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (e : CrownEdge n) : Fin n :=
  (Q.1.entry e.1.1.castSucc e.1.2.castSucc).castPred
    (canonical_upperLeft_offDiagonal_ne_last Q e)

@[simp] theorem canonicalResidualLabels_castSucc
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (e : CrownEdge n) :
    (canonicalResidualLabels Q e).castSucc =
      Q.1.entry e.1.1.castSucc e.1.2.castSucc := by
  simp [canonicalResidualLabels]

/-- The recovered label lies in the residual list prescribed at its left
endpoint.  The final-column identity rules out the row index itself. -/
theorem canonicalResidualLabels_mem
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n))
    (e : CrownEdge n) :
    canonicalResidualLabels Q e ∈
      (crownResidualLists n).labels ((crownGraph n).left e) := by
  rw [crownResidualLists_mem_labels]
  change canonicalResidualLabels Q e ≠ e.1.1
  intro h
  have hentry :
      Q.1.entry e.1.1.castSucc e.1.2.castSucc = e.1.1.castSucc := by
    calc
      Q.1.entry e.1.1.castSucc e.1.2.castSucc =
          (canonicalResidualLabels Q e).castSucc :=
        (canonicalResidualLabels_castSucc Q e).symm
      _ = e.1.1.castSucc := congrArg (fun x : Fin n => x.castSucc) h
  have hfinal :
      Q.1.entry e.1.1.castSucc (Fin.last n) = e.1.1.castSucc := by
    simpa using Q.2.2 e.1.1.castSucc
  have hcols := (Q.1.row_bijective e.1.1.castSucc).1
    (hentry.trans hfinal.symm)
  exact (Fin.castSucc_ne_last e.1.2) hcols

/-- Deleting the distinguished row/column and diagonal from a canonical square
gives an admissible labeling of the manuscript's residual exact lists. -/
theorem canonicalResidualLabels_admissible
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n)) :
    (crownResidualLists n).IsAdmissible (canonicalResidualLabels Q) := by
  apply isAdmissible_of_label_mem_of_injOn
  · exact canonicalResidualLabels_mem Q
  · intro x e he f hf h
    have he' := ((crownGraph n).mem_leftIncident x e).1 he
    have hf' := ((crownGraph n).mem_leftIncident x f).1 hf
    change e.1.1 = x at he'
    change f.1.1 = x at hf'
    have hentry :
        Q.1.entry e.1.1.castSucc e.1.2.castSucc =
          Q.1.entry f.1.1.castSucc f.1.2.castSucc := by
      calc
        Q.1.entry e.1.1.castSucc e.1.2.castSucc =
            (canonicalResidualLabels Q e).castSucc :=
          (canonicalResidualLabels_castSucc Q e).symm
        _ = (canonicalResidualLabels Q f).castSucc :=
          congrArg (fun c : Fin n => c.castSucc) h
        _ = Q.1.entry f.1.1.castSucc f.1.2.castSucc :=
          canonicalResidualLabels_castSucc Q f
    rw [he', hf'] at hentry
    have hright := (Q.1.row_bijective x.castSucc).1 hentry
    apply Subtype.ext
    exact Prod.ext (he'.trans hf'.symm) (Fin.castSucc_injective n hright)
  · intro y e he f hf h
    have he' := ((crownGraph n).mem_rightIncident y e).1 he
    have hf' := ((crownGraph n).mem_rightIncident y f).1 hf
    change e.1.2 = y at he'
    change f.1.2 = y at hf'
    have hentry :
        Q.1.entry e.1.1.castSucc e.1.2.castSucc =
          Q.1.entry f.1.1.castSucc f.1.2.castSucc := by
      calc
        Q.1.entry e.1.1.castSucc e.1.2.castSucc =
            (canonicalResidualLabels Q e).castSucc :=
          (canonicalResidualLabels_castSucc Q e).symm
        _ = (canonicalResidualLabels Q f).castSucc :=
          congrArg (fun c : Fin n => c.castSucc) h
        _ = Q.1.entry f.1.1.castSucc f.1.2.castSucc :=
          canonicalResidualLabels_castSucc Q f
    rw [he', hf'] at hentry
    have hleft := (Q.1.column_bijective y.castSucc).1 hentry
    apply Subtype.ext
    exact Prod.ext (Fin.castSucc_injective n hleft) (he'.trans hf'.symm)

noncomputable def canonicalToResidual
    {n : ℕ} (Q : CanonicalClass (n + 1) (Nat.succ_pos n)) :
    CrownResidualLabeling n :=
  ⟨canonicalResidualLabels Q, canonicalResidualLabels_admissible Q⟩

/-- Deleting the canonical completion recovers the original residual labeling. -/
theorem residual_canonical_roundtrip
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    canonicalToResidual (residualToCanonical hn σ) = σ := by
  apply Subtype.ext
  funext e
  apply Fin.castSucc_injective n
  have h := canonicalResidualLabels_castSucc
    (Q := residualToCanonical hn σ) e
  change (canonicalResidualLabels (residualToCanonical hn σ) e).castSucc =
    residualFilledEntry hn σ e.1.1.castSucc e.1.2.castSucc at h
  rw [residualFilledEntry_castSucc_offDiagonal hn σ e.1.1 e.1.2 e.2] at h
  exact h

end BachThesisLean
