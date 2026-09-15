import BachThesisLean.Basic.Counting
import BachThesisLean.Latin.Counting

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists LatinSquare

/-!
# Ordinary colourings of the canonical residual graph

`crownGraph n` is `K_{n,n}` with the diagonal perfect matching deleted.
Its edges are actual off-diagonal pairs. Filling the deleted diagonal with
the new final symbol and deleting it again give inverse maps between proper
`n - 1` colourings and the constant-diagonal Latin class from v13.23 §4.6.
-/

abbrev CrownEdge (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

def crownGraph (n : ℕ) : BipartiteMultigraph (Fin n) (Fin n) (CrownEdge n) where
  left e := e.1.1
  right e := e.1.2

def crownLeftIncidentEquiv (n : ℕ) (i : Fin n) :
    {e : CrownEdge n // (crownGraph n).left e = i} ≃ {j : Fin n // j ≠ i} where
  toFun e := ⟨e.1.1.2, by
    intro h
    apply e.1.2
    exact e.2.trans h.symm⟩
  invFun j := ⟨⟨(i, j.1), j.2.symm⟩, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.2.symm rfl
  right_inv j := by apply Subtype.ext; rfl

def crownRightIncidentEquiv (n : ℕ) (j : Fin n) :
    {e : CrownEdge n // (crownGraph n).right e = j} ≃ {i : Fin n // i ≠ j} where
  toFun e := ⟨e.1.1.1, by
    intro h
    apply e.1.2
    exact h.trans e.2.symm⟩
  invFun i := ⟨⟨(i.1, j), i.2⟩, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl e.2.symm
  right_inv i := by apply Subtype.ext; rfl

theorem crown_left_regular (n : ℕ) : (crownGraph n).IsLeftRegular (n - 1) := by
  classical
  intro i
  change ((crownGraph n).leftIncident i).card = n - 1
  have hset : (crownGraph n).leftIncident i =
      Finset.univ.filter (fun e : CrownEdge n => (crownGraph n).left e = i) := by
    ext e
    simp
  rw [hset, ← Fintype.card_subtype,
    Fintype.card_congr (crownLeftIncidentEquiv n i)]
  simpa using (Fintype.card_subtype_compl (fun j : Fin n => j = i))

theorem crown_right_regular (n : ℕ) : (crownGraph n).IsRightRegular (n - 1) := by
  classical
  intro j
  change ((crownGraph n).rightIncident j).card = n - 1
  have hset : (crownGraph n).rightIncident j =
      Finset.univ.filter (fun e : CrownEdge n => (crownGraph n).right e = j) := by
    ext e
    simp
  rw [hset, ← Fintype.card_subtype,
    Fintype.card_congr (crownRightIncidentEquiv n j)]
  simpa using (Fintype.card_subtype_compl (fun i : Fin n => i = j))

noncomputable def crownUniformLists (n : ℕ) :
    ExactLeftLists (crownGraph n) (Fin (n - 1)) :=
  uniform (crownGraph n) (n - 1) (crown_left_regular n)

abbrev CrownColoring (n : ℕ) := (crownUniformLists n).AdmissibleLabeling

noncomputable def crownFilledEntry {n : ℕ} (hn : 0 < n) (σ : CrownColoring n)
    (i j : Fin n) : Fin n :=
  if h : i = j then lastSymbol n hn
  else (lastComplementEquiv n hn (σ.1 ⟨(i, j), h⟩)).1

@[simp] theorem crownFilledEntry_diagonal {n : ℕ} (hn : 0 < n)
    (σ : CrownColoring n) (i : Fin n) :
    crownFilledEntry hn σ i i = lastSymbol n hn := by
  simp [crownFilledEntry]

theorem crownFilledEntry_row_injective {n : ℕ} (hn : 0 < n)
    (σ : CrownColoring n) (i : Fin n) : Function.Injective (crownFilledEntry hn σ i) := by
  intro j k h
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · exact hik
    · simp only [crownFilledEntry, dif_pos rfl, dif_neg hik] at h
      exact False.elim ((lastComplementEquiv n hn (σ.1 ⟨(i, k), hik⟩)).2 h.symm)
  · by_cases hik : i = k
    · subst k
      simp only [crownFilledEntry, dif_pos rfl, dif_neg hij] at h
      exact False.elim ((lastComplementEquiv n hn (σ.1 ⟨(i, j), hij⟩)).2 h)
    · simp only [crownFilledEntry, dif_neg hij, dif_neg hik] at h
      have hc := (lastComplementEquiv n hn).injective (Subtype.ext h)
      have he := σ.2.left_injOn i
        ((crownGraph n).mem_leftIncident i ⟨(i, j), hij⟩ |>.2 rfl)
        ((crownGraph n).mem_leftIncident i ⟨(i, k), hik⟩ |>.2 rfl) hc
      exact congrArg (fun e : CrownEdge n => e.1.2) he

theorem crownFilledEntry_column_injective {n : ℕ} (hn : 0 < n)
    (σ : CrownColoring n) (j : Fin n) :
    Function.Injective (fun i => crownFilledEntry hn σ i j) := by
  intro i k h
  by_cases hij : i = j
  · subst i
    by_cases hkj : k = j
    · exact hkj.symm
    · simp only [crownFilledEntry, dif_pos rfl, dif_neg hkj] at h
      exact False.elim ((lastComplementEquiv n hn (σ.1 ⟨(k, j), hkj⟩)).2 h.symm)
  · by_cases hkj : k = j
    · subst k
      simp only [crownFilledEntry, dif_pos rfl, dif_neg hij] at h
      exact False.elim ((lastComplementEquiv n hn (σ.1 ⟨(i, j), hij⟩)).2 h)
    · simp only [crownFilledEntry, dif_neg hij, dif_neg hkj] at h
      have hc := (lastComplementEquiv n hn).injective (Subtype.ext h)
      have he := σ.2.right_injOn j
        ((crownGraph n).mem_rightIncident j ⟨(i, j), hij⟩ |>.2 rfl)
        ((crownGraph n).mem_rightIncident j ⟨(k, j), hkj⟩ |>.2 rfl) hc
      exact congrArg (fun e : CrownEdge n => e.1.1) he

noncomputable def crownColoringToConstantDiagonal {n : ℕ} (hn : 0 < n)
    (σ : CrownColoring n) : ConstantDiagonalClass n hn :=
  ⟨{ entry := crownFilledEntry hn σ
     row_bijective := fun i => ⟨crownFilledEntry_row_injective hn σ i,
       Finite.surjective_of_injective (crownFilledEntry_row_injective hn σ i)⟩
     column_bijective := fun j => ⟨crownFilledEntry_column_injective hn σ j,
       Finite.surjective_of_injective (crownFilledEntry_column_injective hn σ j)⟩ },
    crownFilledEntry_diagonal hn σ⟩

theorem constantDiagonal_offDiagonal_ne_last {n : ℕ} {hn : 0 < n}
    (Q : ConstantDiagonalClass n hn) (e : CrownEdge n) :
    Q.1.entry e.1.1 e.1.2 ≠ lastSymbol n hn := by
  intro h
  have he := (Q.1.row_bijective e.1.1).1 (h.trans (Q.2 e.1.1).symm)
  exact e.2 he.symm

noncomputable def constantDiagonalCrownLabels {n : ℕ} {hn : 0 < n}
    (Q : ConstantDiagonalClass n hn) (e : CrownEdge n) : Fin (n - 1) :=
  (lastComplementEquiv n hn).symm
    ⟨Q.1.entry e.1.1 e.1.2, constantDiagonal_offDiagonal_ne_last Q e⟩

@[simp] theorem embed_constantDiagonalCrownLabels {n : ℕ} {hn : 0 < n}
    (Q : ConstantDiagonalClass n hn) (e : CrownEdge n) :
    (lastComplementEquiv n hn (constantDiagonalCrownLabels Q e)).1 =
      Q.1.entry e.1.1 e.1.2 := by
  simp [constantDiagonalCrownLabels]

theorem constantDiagonalCrownLabels_admissible {n : ℕ} {hn : 0 < n}
    (Q : ConstantDiagonalClass n hn) :
    (crownUniformLists n).IsAdmissible (constantDiagonalCrownLabels Q) := by
  apply (isAdmissible_uniform_iff (n - 1) (crown_left_regular n) _).2
  constructor
  · intro i e he f hf h
    have he' := ((crownGraph n).mem_leftIncident i e).1 he
    have hf' := ((crownGraph n).mem_leftIncident i f).1 hf
    have hentry := congrArg (fun c => (lastComplementEquiv n hn c).1) h
    simp only [embed_constantDiagonalCrownLabels] at hentry
    change e.1.1 = i at he'
    change f.1.1 = i at hf'
    rw [he', hf'] at hentry
    apply Subtype.ext
    exact Prod.ext (he'.trans hf'.symm) ((Q.1.row_bijective i).1 hentry)
  · intro j e he f hf h
    have he' := ((crownGraph n).mem_rightIncident j e).1 he
    have hf' := ((crownGraph n).mem_rightIncident j f).1 hf
    have hentry := congrArg (fun c => (lastComplementEquiv n hn c).1) h
    simp only [embed_constantDiagonalCrownLabels] at hentry
    change e.1.2 = j at he'
    change f.1.2 = j at hf'
    rw [he', hf'] at hentry
    apply Subtype.ext
    exact Prod.ext ((Q.1.column_bijective j).1 hentry) (he'.trans hf'.symm)

noncomputable def constantDiagonalToCrownColoring {n : ℕ} {hn : 0 < n}
    (Q : ConstantDiagonalClass n hn) : CrownColoring n :=
  ⟨constantDiagonalCrownLabels Q, constantDiagonalCrownLabels_admissible Q⟩

theorem crownColoring_roundtrip {n : ℕ} (hn : 0 < n) (σ : CrownColoring n) :
    constantDiagonalToCrownColoring (crownColoringToConstantDiagonal hn σ) = σ := by
  apply Subtype.ext
  funext e
  apply (lastComplementEquiv n hn).injective
  apply Subtype.ext
  change (lastComplementEquiv n hn
    (constantDiagonalCrownLabels (crownColoringToConstantDiagonal hn σ) e)).1 = _
  rw [embed_constantDiagonalCrownLabels]
  simp [crownColoringToConstantDiagonal, crownFilledEntry, e.2]

theorem constantDiagonal_roundtrip {n : ℕ} {hn : 0 < n}
    (Q : ConstantDiagonalClass n hn) :
    crownColoringToConstantDiagonal hn (constantDiagonalToCrownColoring Q) = Q := by
  apply Subtype.ext
  apply LatinSquare.ext
  intro i j
  by_cases h : i = j
  · subst j
    exact (crownFilledEntry_diagonal _ _ _).trans (Q.2 i).symm
  · change crownFilledEntry hn (constantDiagonalToCrownColoring Q) i j = _
    simp [crownFilledEntry, h, constantDiagonalToCrownColoring]

noncomputable def crownColoringEquiv {n : ℕ} (hn : 0 < n) :
    CrownColoring n ≃ ConstantDiagonalClass n hn where
  toFun := crownColoringToConstantDiagonal hn
  invFun := constantDiagonalToCrownColoring
  left_inv := crownColoring_roundtrip hn
  right_inv := constantDiagonal_roundtrip

/-- The manuscript identity `c_(n-1)(R_n) = V_n`, with the fixed palette explicit. -/
theorem crown_ordinaryCount_eq_V (n : ℕ) (hn : 0 < n) :
    ordinaryCount (crownGraph n) (n - 1) (crown_left_regular n) = V n hn := by
  rw [ordinaryCount, count_eq_card, V_eq_card]
  exact Fintype.card_congr (crownColoringEquiv hn)

end BachThesisLean
