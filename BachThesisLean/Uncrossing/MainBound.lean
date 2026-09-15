import BachThesisLean.Uncrossing.Monotonicity
import BachThesisLean.Uncrossing.CommonPalette
import BachThesisLean.Uncrossing.NormalForm
import BachThesisLean.Conjectures.Status

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]

/-!
# The regular exact-list lower bound

The local fibre injection, global component flip, finite termination, and
nested normal form are assembled here into the manuscript's regular main
theorem.  A nested exact support family on a nonempty `k`-regular left shore
has one common palette of size `k`; relabelling that palette by `Fin k`
identifies its completions with ordinary proper `k`-edge-colourings.
-/

/-- If the left shore is empty then the edge-copy type is empty as well, so
there is exactly one admissible labeling for every exact list assignment. -/
theorem count_eq_one_of_isEmpty_left
    [IsEmpty X] (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G Λ) :
    L.count = 1 := by
  classical
  letI : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
  let σ₀ : E → Λ := fun e => isEmptyElim e
  have hσ₀ : L.IsAdmissible σ₀ := by
    constructor
    · intro x
      exact isEmptyElim x
    · intro y
      have hempty : G.rightIncident y = ∅ := by
        ext e
        exact isEmptyElim e
      simp [labelsUsedAtRight, hempty]
  rw [count_eq_card]
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨σ₀, hσ₀⟩, ?_⟩
  intro s
  apply Subtype.ext
  funext e
  exact isEmptyElim e

/-- A nested exact support system on a nonempty regular left shore has the
same number of completions as the ordinary fixed-palette coloring problem. -/
theorem nested_regular_count_eq_ordinary
    [DecidableEq X] [DecidableEq Λ] [Nonempty X]
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (T : SupportFamily X Λ) (hT : ExactSupportIncidence G T)
    (hnested : IsNested T) :
    (exactListsOfSupports T hT).count = ordinaryCount G k hG := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let P : Finset Λ := listsOfSupports T x₀
  have hP : P.card = k := by
    dsimp [P]
    rw [hT x₀, hG x₀]
  have hlabels : ∀ x, (exactListsOfSupports T hT).labels x = P := by
    intro x
    change listsOfSupports T x = P
    dsimp [P]
    apply listsOfSupports_eq_of_nested_of_card T hnested x x₀
    rw [hT x, hT x₀, hG x, hG x₀]
  exact count_eq_ordinary_of_common_palette
    G k hG (exactListsOfSupports T hT) P hlabels hP

/-- Support-family form of the regular lower bound. -/
theorem exactSupport_regular_lowerBound
    [DecidableEq X] [DecidableEq Λ] [DecidableEq E] [Nonempty X]
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (S : SupportFamily X Λ) (hS : ExactSupportIncidence G S) :
    ordinaryCount G k hG ≤ (exactListsOfSupports S hS).count := by
  classical
  obtain ⟨T, hT, _hST, hnested, hcount⟩ :=
    exists_nested_exact_uncrossing_count_le G S hS
  have hterminal := nested_regular_count_eq_ordinary G k hG T hT hnested
  calc
    ordinaryCount G k hG = (exactListsOfSupports T hT).count := hterminal.symm
    _ ≤ (exactListsOfSupports S hS).count := hcount

/-- Exact-list form of the regular lower bound when the left shore is
nonempty. -/
theorem exactListLowerBound_of_nonempty_left
    [DecidableEq X] [DecidableEq Λ] [DecidableEq E] [Nonempty X]
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (L : ExactLeftLists G Λ) :
    ordinaryCount G k hG ≤ L.count := by
  classical
  let S : SupportFamily X Λ := supportFamilyOfLists L
  have hS : ExactSupportIncidence G S := by
    simpa [S] using supportFamilyOfLists_exact G L
  have hbound := exactSupport_regular_lowerBound G k hG S hS
  calc
    ordinaryCount G k hG ≤ (exactListsOfSupports S hS).count := hbound
    _ = L.count := by
      have hproof : hS = supportFamilyOfLists_exact G L := Subsingleton.elim _ _
      subst hS
      simpa [S] using exactListsOfSupports_supportFamilyOfLists_count G L

/-- Exact-list form of the regular lower bound when the left shore is empty. -/
theorem exactListLowerBound_of_isEmpty_left
    [IsEmpty X]
    (G : BipartiteMultigraph X Y E) (k : ℕ) (hG : G.IsLeftRegular k)
    (L : ExactLeftLists G Λ) :
    ordinaryCount G k hG ≤ L.count := by
  classical
  have hL : L.count = 1 := count_eq_one_of_isEmpty_left G L
  have hU : (uniform G k hG).count = 1 :=
    count_eq_one_of_isEmpty_left G (uniform G k hG)
  unfold ordinaryCount
  rw [hL, hU]

/-- Kernel-checked proof of the proposition recorded as `ExactListLowerBound`.
No additional regularity, simplicity, or palette hypothesis is used. -/
theorem exactListLowerBound_machineChecked : ExactListLowerBound := by
  classical
  unfold ExactListLowerBound
  intro X Y E Λ hFX hFY hFE hFΛ G k hG L
  cases isEmpty_or_nonempty X
  · exact exactListLowerBound_of_isEmpty_left G k hG L
  · exact exactListLowerBound_of_nonempty_left G k hG L

end BachThesisLean
