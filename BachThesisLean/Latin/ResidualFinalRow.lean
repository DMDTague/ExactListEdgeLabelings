import BachThesisLean.Latin.ResidualColumns

namespace BachThesisLean

/-!
# The final row of the residual completion

Every non-final row is already a permutation and every column is injective.
The only remaining Latin-square condition is injectivity of the final row.
If two final-row entries agreed in distinct non-final columns, the positions of
that symbol in the first `n` rows would inject `Fin n` into the `n - 1`
remaining columns, a finite pigeonhole contradiction.
-/

/-- A non-final row, packaged as a permutation of the completed symbol set. -/
noncomputable def residualUpperRowPerm
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) (i : Fin n) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (residualFilledEntry hn σ i.castSucc)
    ⟨residualFilledEntry_upperRow_injective hn σ i,
      Finite.surjective_of_injective
        (residualFilledEntry_upperRow_injective hn σ i)⟩

/-- The unique column in row `i` carrying the completed symbol `c`. -/
noncomputable def residualUpperRowPosition
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (i : Fin n) (c : Fin (n + 1)) : Fin (n + 1) :=
  (residualUpperRowPerm hn σ i).symm c

@[simp] theorem residualFilledEntry_upperRowPosition
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (i : Fin n) (c : Fin (n + 1)) :
    residualFilledEntry hn σ i.castSucc
      (residualUpperRowPosition hn σ i c) = c := by
  change (residualUpperRowPerm hn σ i)
    ((residualUpperRowPerm hn σ i).symm c) = c
  exact (residualUpperRowPerm hn σ i).apply_symm_apply c

/-- For a fixed symbol, its positions in the first `n` rows are distinct,
because every column is injective. -/
theorem residualUpperRowPosition_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n)
    (c : Fin (n + 1)) :
    Function.Injective (fun i : Fin n => residualUpperRowPosition hn σ i c) := by
  intro i k h
  change residualUpperRowPosition hn σ i c =
    residualUpperRowPosition hn σ k c at h
  have hi := residualFilledEntry_upperRowPosition hn σ i c
  have hk := residualFilledEntry_upperRowPosition hn σ k c
  have hcol :
      residualFilledEntry hn σ i.castSucc (residualUpperRowPosition hn σ i c) =
        residualFilledEntry hn σ k.castSucc (residualUpperRowPosition hn σ i c) := by
    calc
      residualFilledEntry hn σ i.castSucc (residualUpperRowPosition hn σ i c) = c := hi
      _ = residualFilledEntry hn σ k.castSucc (residualUpperRowPosition hn σ k c) := hk.symm
      _ = residualFilledEntry hn σ k.castSucc (residualUpperRowPosition hn σ i c) :=
        congrArg (residualFilledEntry hn σ k.castSucc) h.symm
  have hik : i.castSucc = k.castSucc :=
    residualFilledEntry_column_injective hn σ
      (residualUpperRowPosition hn σ i c) hcol
  exact Fin.castSucc_injective n hik

/-- The final row of the manuscript's completed residual array is injective. -/
theorem residualFilledEntry_lastRow_injective
    {n : ℕ} (hn : 0 < n) (σ : CrownResidualLabeling n) :
    Function.Injective (residualFilledEntry hn σ (Fin.last n)) := by
  classical
  intro j k h
  induction j using Fin.lastCases with
  | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k =>
          simp only [residualFilledEntry_last_last,
            residualFilledEntry_last_castSucc] at h
          exact False.elim
            ((Fin.castSucc_ne_last (residualMissingLabel hn σ k)) h.symm)
  | cast j =>
      induction k using Fin.lastCases with
      | last =>
          simp only [residualFilledEntry_last_last,
            residualFilledEntry_last_castSucc] at h
          exact False.elim
            ((Fin.castSucc_ne_last (residualMissingLabel hn σ j)) h)
      | cast k =>
          simp only [residualFilledEntry_last_castSucc] at h
          have hmissing :
              residualMissingLabel hn σ j = residualMissingLabel hn σ k :=
            (Fin.castSucc_injective n) h
          apply congrArg (fun x : Fin n => x.castSucc)
          by_contra hjk
          let c : Fin (n + 1) := (residualMissingLabel hn σ j).castSucc
          let p : Fin n → Fin (n + 1) :=
            fun i => residualUpperRowPosition hn σ i c
          have hp_inj : Function.Injective p := by
            simpa [p] using residualUpperRowPosition_injective hn σ c
          have hp_ne_j : ∀ i, p i ≠ j.castSucc := by
            intro i hpj
            have hi : residualFilledEntry hn σ i.castSucc (p i) = c := by
              simpa [p] using residualFilledEntry_upperRowPosition hn σ i c
            rw [hpj] at hi
            have hjlast :
                residualFilledEntry hn σ (Fin.last n) j.castSucc = c := by
              simp [c]
            have hrow : i.castSucc = Fin.last n :=
              residualFilledEntry_column_injective hn σ j.castSucc
                (hi.trans hjlast.symm)
            exact (Fin.castSucc_ne_last i) hrow
          have hp_ne_k : ∀ i, p i ≠ k.castSucc := by
            intro i hpk
            have hi : residualFilledEntry hn σ i.castSucc (p i) = c := by
              simpa [p] using residualFilledEntry_upperRowPosition hn σ i c
            rw [hpk] at hi
            have hklast :
                residualFilledEntry hn σ (Fin.last n) k.castSucc = c := by
              rw [residualFilledEntry_last_castSucc]
              dsimp [c]
              exact congrArg (fun x : Fin n => x.castSucc) hmissing.symm
            have hrow : i.castSucc = Fin.last n :=
              residualFilledEntry_column_injective hn σ k.castSucc
                (hi.trans hklast.symm)
            exact (Fin.castSucc_ne_last i) hrow
          have hjkCast : j.castSucc ≠ k.castSucc := by
            intro hjk'
            exact hjk ((Fin.castSucc_injective n) hjk')
          let t : Finset (Fin (n + 1)) :=
            (Finset.univ.erase j.castSucc).erase k.castSucc
          have hjmem : j.castSucc ∈ (Finset.univ : Finset (Fin (n + 1))) :=
            Finset.mem_univ _
          have hkmem :
              k.castSucc ∈ (Finset.univ.erase j.castSucc : Finset (Fin (n + 1))) := by
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            exact fun hkj => hjkCast hkj.symm
          have htcard : t.card = n - 1 := by
            dsimp [t]
            rw [Finset.card_erase_of_mem hkmem, Finset.card_erase_of_mem hjmem]
            simp
          let f : Fin n → {x : Fin (n + 1) // x ∈ t} :=
            fun i => ⟨p i, by
              simp only [t, Finset.mem_erase, Finset.mem_univ, and_true]
              exact ⟨hp_ne_k i, hp_ne_j i⟩⟩
          have hf : Function.Injective f := by
            intro a b hab
            apply hp_inj
            exact congrArg Subtype.val hab
          have hcard :
              Fintype.card (Fin n) ≤ Fintype.card {x : Fin (n + 1) // x ∈ t} :=
            Fintype.card_le_of_injective f hf
          have hcard' : n ≤ t.card := by
            simpa using hcard
          rw [htcard] at hcard'
          omega

end BachThesisLean
