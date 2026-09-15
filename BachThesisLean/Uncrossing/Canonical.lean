import BachThesisLean.Uncrossing.SortedNormalForm

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X]

/-!
# Canonical suffix support families

With `m` indexed labels, the zero-based form of the manuscript's nested
terminal system has slot `j` supported exactly on the vertices of degree at
least `m - j`.  When `m` is larger than the maximum degree, the first
`m - K` slots are automatically empty.
-/

/-- The canonical `m`-slot support family determined by the left degree
sequence. -/
noncomputable def canonicalSupport
    (G : BipartiteMultigraph X Y E) (m : ℕ) : SupportFamily X (Fin m) := by
  classical
  exact fun j => Finset.univ.filter (fun x => m - j.val ≤ G.leftDegree x)

@[simp] theorem mem_canonicalSupport
    (G : BipartiteMultigraph X Y E) (m : ℕ) (j : Fin m) (x : X) :
    x ∈ canonicalSupport G m j ↔ m - j.val ≤ G.leftDegree x := by
  classical
  simp [canonicalSupport]

/-- If `K` bounds every left degree, the canonical `K`-slot family has exactly
the required incidence multiplicity at every left vertex. -/
theorem canonicalSupport_exact
    (G : BipartiteMultigraph X Y E) (K : ℕ)
    (hdeg : ∀ x, G.leftDegree x ≤ K) :
    ExactSupportIncidence G (canonicalSupport G K) := by
  classical
  intro x
  let d : ℕ := G.leftDegree x
  have hdK : d ≤ K := hdeg x
  by_cases hd : d = 0
  · have hempty : listsOfSupports (canonicalSupport G K) x = ∅ := by
      ext j
      simp only [mem_listsOfSupports, mem_canonicalSupport,
        Finset.not_mem_empty, iff_false]
      intro h
      have hj : j.val < K := j.isLt
      change K - j.val ≤ d at h
      rw [hd] at h
      omega
    rw [hempty]
    simp [d, hd]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let j₀ : Fin K := ⟨K - d, by omega⟩
    have hset : listsOfSupports (canonicalSupport G K) x = Finset.Ici j₀ := by
      ext j
      simp only [mem_listsOfSupports, mem_canonicalSupport, Finset.mem_Ici]
      change K - j.val ≤ d ↔ K - d ≤ j.val
      omega
    rw [hset, Fin.card_Ici]
    dsimp [j₀, d]
    omega

/-- The sorted normal form is literally the canonical support family. -/
theorem sortedSupport_eq_canonicalSupport
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [DecidableEq E]
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) (hnested : IsNested S) :
    sortedSupport S = canonicalSupport G (Fintype.card Λ) := by
  classical
  funext j
  exact sortedSupport_normalForm G S hS hnested j

/-- If all left degrees are at most `K`, every canonical slot strictly below
the final `K` positions is empty. -/
theorem canonicalSupport_eq_empty_of_lt_offset
    (G : BipartiteMultigraph X Y E) {m K : ℕ}
    (hdeg : ∀ x, G.leftDegree x ≤ K)
    (j : Fin m) (hj : j.val < m - K) :
    canonicalSupport G m j = ∅ := by
  classical
  ext x
  simp only [mem_canonicalSupport, Finset.not_mem_empty, iff_false]
  intro hmem
  have hmk : K < m - j.val := by omega
  exact (not_le_of_gt hmk) (hmem.trans (hdeg x))

/-- For a suffix slot `m-K+j`, the `m`-slot canonical threshold reduces to the
`K`-slot threshold. -/
theorem canonicalSupport_suffix
    (G : BipartiteMultigraph X Y E) {m K : ℕ} (hKm : K ≤ m)
    (j : Fin K) :
    canonicalSupport G m
      ⟨m - K + j.val, by omega⟩ = canonicalSupport G K j := by
  classical
  ext x
  simp only [mem_canonicalSupport]
  omega

end BachThesisLean
