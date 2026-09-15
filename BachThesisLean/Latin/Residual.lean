import BachThesisLean.Latin.Crown

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists LatinSquare

/-!
# Canonical residual exact lists

For the crown graph `R_n = K_{n,n} - M`, the manuscript's canonical residual
assignment gives row `i` the label set `Fin n \ {i}`.  This file builds the
exact-list object and the missing-column-label machinery used to complete an
admissible residual labeling to a canonical Latin square of order `n + 1`.
-/

/-- The manuscript's residual list system: row `i` may use every label except
`i` itself. -/
noncomputable def crownResidualLists (n : ℕ) :
    ExactLeftLists (crownGraph n) (Fin n) where
  labels := fun i => Finset.univ.erase i
  card_labels := by
    classical
    intro i
    rw [crown_left_regular n i]
    simp

abbrev CrownResidualLabeling (n : ℕ) :=
  (crownResidualLists n).AdmissibleLabeling

@[simp] theorem crownResidualLists_mem_labels
    {n : ℕ} (i c : Fin n) :
    c ∈ (crownResidualLists n).labels i ↔ c ≠ i := by
  classical
  simp [crownResidualLists]

/-- Every right column of a residual labeling uses exactly `n - 1` labels. -/
theorem crownResidual_usedAtRight_card
    {n : ℕ} (σ : CrownResidualLabeling n) (j : Fin n) :
    (labelsUsedAtRight (crownGraph n) σ.1 j).card = n - 1 := by
  rw [← σ.2.2 j]
  simpa [BipartiteMultigraph.rightDegree] using crown_right_regular n j

/-- The labels absent from one right column. -/
noncomputable def residualUnusedAtRight
    {n : ℕ} (σ : CrownResidualLabeling n) (j : Fin n) : Finset (Fin n) := by
  classical
  exact (labelsUsedAtRight (crownGraph n) σ.1 j)ᶜ

/-- For positive `n`, exactly one residual label is absent from each column. -/
theorem residualUnusedAtRight_card
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) :
    (residualUnusedAtRight σ j).card = 1 := by
  classical
  rw [residualUnusedAtRight, Finset.card_compl, Fintype.card_fin,
    crownResidual_usedAtRight_card σ j]
  omega

/-- The unique residual label missing from a column. -/
noncomputable def residualMissingLabel
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) : Fin n :=
  (Finset.card_eq_one.mp (residualUnusedAtRight_card hn σ j)).choose

@[simp] theorem residualUnusedAtRight_eq_singleton
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) :
    residualUnusedAtRight σ j = {residualMissingLabel hn σ j} :=
  (Finset.card_eq_one.mp (residualUnusedAtRight_card hn σ j)).choose_spec

/-- The chosen missing label really is absent from the corresponding right
column. -/
theorem residualMissingLabel_not_used
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) :
    residualMissingLabel hn σ j ∉ labelsUsedAtRight (crownGraph n) σ.1 j := by
  classical
  have hm : residualMissingLabel hn σ j ∈ residualUnusedAtRight σ j := by
    rw [residualUnusedAtRight_eq_singleton hn σ j]
    simp
  simpa [residualUnusedAtRight] using hm

/-- A label absent from a column is the distinguished missing label of that
column. -/
theorem residualMissingLabel_eq_of_not_used
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) (c : Fin n)
    (hc : c ∉ labelsUsedAtRight (crownGraph n) σ.1 j) :
    residualMissingLabel hn σ j = c := by
  classical
  have hm : c ∈ residualUnusedAtRight σ j := by
    simpa [residualUnusedAtRight] using hc
  rw [residualUnusedAtRight_eq_singleton hn σ j] at hm
  exact (Finset.mem_singleton.mp hm).symm

/-- The manuscript's completed `(n+1) × (n+1)` array before packaging the
Latin-square laws. The upper-left off-diagonal block is the residual labeling,
the diagonal is the new final symbol, the final column is the identity, and
the final row records the unique label missing from each residual column. -/
noncomputable def residualFilledEntry
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    Fin (n + 1) → Fin (n + 1) → Fin (n + 1) :=
  fun i =>
    Fin.lastCases
      (Fin.lastCases (Fin.last n)
        (fun j : Fin n => (residualMissingLabel hn σ j).castSucc))
      (fun i : Fin n =>
        Fin.lastCases i.castSucc
          (fun j : Fin n =>
            if h : i = j then Fin.last n else (σ.1 ⟨(i, j), h⟩).castSucc))
      i

@[simp] theorem residualFilledEntry_last_last
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    residualFilledEntry hn σ (Fin.last n) (Fin.last n) = Fin.last n := by
  simp [residualFilledEntry]

@[simp] theorem residualFilledEntry_last_castSucc
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (j : Fin n) :
    residualFilledEntry hn σ (Fin.last n) j.castSucc =
      (residualMissingLabel hn σ j).castSucc := by
  simp [residualFilledEntry]

@[simp] theorem residualFilledEntry_castSucc_last
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (i : Fin n) :
    residualFilledEntry hn σ i.castSucc (Fin.last n) = i.castSucc := by
  simp [residualFilledEntry]

@[simp] theorem residualFilledEntry_castSucc_diagonal
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (i : Fin n) :
    residualFilledEntry hn σ i.castSucc i.castSucc = Fin.last n := by
  simp [residualFilledEntry]

theorem residualFilledEntry_castSucc_offDiagonal
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (i j : Fin n) (h : i ≠ j) :
    residualFilledEntry hn σ i.castSucc j.castSucc =
      (σ.1 ⟨(i, j), h⟩).castSucc := by
  simp [residualFilledEntry, h]

/-- Inside a non-final row, the upper-left block is injective: the new diagonal
symbol is separated from every residual label, and off-diagonal collisions are
ruled out by left admissibility. -/
theorem residualFilledEntry_upperLeft_row_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (i : Fin n) :
    Function.Injective (fun j : Fin n =>
      residualFilledEntry hn σ i.castSucc j.castSucc) := by
  intro j k h
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · exact hik
    · change residualFilledEntry hn σ i.castSucc i.castSucc =
        residualFilledEntry hn σ i.castSucc k.castSucc at h
      rw [residualFilledEntry_castSucc_diagonal,
        residualFilledEntry_castSucc_offDiagonal hn σ i k hik] at h
      exact False.elim ((Fin.castSucc_ne_last (σ.1 ⟨(i, k), hik⟩)) h.symm)
  · by_cases hik : i = k
    · subst k
      change residualFilledEntry hn σ i.castSucc j.castSucc =
        residualFilledEntry hn σ i.castSucc i.castSucc at h
      rw [residualFilledEntry_castSucc_diagonal,
        residualFilledEntry_castSucc_offDiagonal hn σ i j hij] at h
      exact False.elim ((Fin.castSucc_ne_last (σ.1 ⟨(i, j), hij⟩)) h)
    · change residualFilledEntry hn σ i.castSucc j.castSucc =
        residualFilledEntry hn σ i.castSucc k.castSucc at h
      rw [residualFilledEntry_castSucc_offDiagonal hn σ i j hij,
        residualFilledEntry_castSucc_offDiagonal hn σ i k hik] at h
      have hσ : σ.1 ⟨(i, j), hij⟩ = σ.1 ⟨(i, k), hik⟩ :=
        (Fin.castSucc_injective n) h
      have he := σ.2.left_injOn i
        ((crownGraph n).mem_leftIncident i ⟨(i, j), hij⟩ |>.2 rfl)
        ((crownGraph n).mem_leftIncident i ⟨(i, k), hik⟩ |>.2 rfl) hσ
      exact congrArg (fun e : CrownEdge n => e.1.2) he

/-- No upper-left entry in row `i` equals the identity entry appended in the
final column of that row. -/
theorem residualFilledEntry_upperLeft_ne_rowIndex
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (i j : Fin n) :
    residualFilledEntry hn σ i.castSucc j.castSucc ≠ i.castSucc := by
  by_cases hij : i = j
  · subst j
    rw [residualFilledEntry_castSucc_diagonal]
    exact (Fin.castSucc_ne_last i).symm
  · rw [residualFilledEntry_castSucc_offDiagonal hn σ i j hij]
    intro h
    have hσ : σ.1 ⟨(i, j), hij⟩ = i := (Fin.castSucc_injective n) h
    have hmem := σ.2.label_mem ⟨(i, j), hij⟩
    rw [crownResidualLists_mem_labels] at hmem
    exact hmem hσ

/-- Every non-final row of the completed array is a permutation of
`Fin (n+1)`. -/
theorem residualFilledEntry_upperRow_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (i : Fin n) :
    Function.Injective (residualFilledEntry hn σ i.castSucc) := by
  intro j k h
  induction j using Fin.lastCases with
  | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k =>
          have hk := residualFilledEntry_upperLeft_ne_rowIndex hn σ i k
          simp only [residualFilledEntry_castSucc_last] at h
          exact False.elim (hk h.symm)
  | cast j =>
      induction k using Fin.lastCases with
      | last =>
          have hj := residualFilledEntry_upperLeft_ne_rowIndex hn σ i j
          simp only [residualFilledEntry_castSucc_last] at h
          exact False.elim (hj h)
      | cast k =>
          have hjk := residualFilledEntry_upperLeft_row_injective hn σ i h
          exact congrArg (fun x : Fin n => x.castSucc) hjk

end BachThesisLean
