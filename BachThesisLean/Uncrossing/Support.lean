import BachThesisLean.Basic.ExactLists
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace BachThesisLean

open BipartiteMultigraph
open ExactLeftLists
open scoped BigOperators

universe u v w z

/-!
## Supports and the elementary uncrossing operation

The family is indexed by labels, not quotiented to a set: equal supports for
two different labels remain two indexed slots. This is the convention used by
the capstone and is required for exact counting.
-/

abbrev SupportFamily (X : Type u) (Λ : Type z) := Λ → Finset X

variable {X : Type u} {Λ : Type z}
variable [Fintype X] [Fintype Λ] [DecidableEq X] [DecidableEq Λ]

noncomputable def listsOfSupports
    (S : SupportFamily X Λ) (x : X) : Finset Λ :=
  by
    classical
    exact Finset.univ.filter (fun c => x ∈ S c)

@[simp] theorem mem_listsOfSupports
    (S : SupportFamily X Λ) (x : X) (c : Λ) :
    c ∈ listsOfSupports S x ↔ x ∈ S c := by
  classical
  simp [listsOfSupports]

noncomputable def supportOfLists
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ) (c : Λ) :
    Finset X :=
  by
    classical
    exact Finset.univ.filter (fun x => c ∈ L.labels x)

theorem supportOf_listsOfSupports
    (S : SupportFamily X Λ) (c : Λ) :
    Finset.univ.filter (fun x => c ∈ listsOfSupports S x) = S c := by
  classical
  ext x
  simp [listsOfSupports]

/-!
`supportFamilyOfLists` records, for each indexed label, the left vertices at
which that label occurs.  The next theorem is the exact inverse statement
needed when passing between list language and support language: no quotienting
of equal supports is performed.
-/

noncomputable def supportFamilyOfLists
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    {G : BipartiteMultigraph X Y E}
    (L : ExactLeftLists G Λ) : SupportFamily X Λ :=
  fun c => supportOfLists L c

theorem listsOfSupports_supportFamilyOfLists
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    {G : BipartiteMultigraph X Y E}
    (L : ExactLeftLists G Λ) (x : X) :
    listsOfSupports (supportFamilyOfLists L) x = L.labels x := by
  classical
  ext c
  simp [supportFamilyOfLists, supportOfLists, listsOfSupports]

def ExactSupportIncidence
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ) : Prop :=
  ∀ x, (listsOfSupports S x).card = G.leftDegree x

noncomputable def exactListsOfSupports
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    {G : BipartiteMultigraph X Y E}
    (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) : ExactLeftLists G Λ where
  labels := listsOfSupports S
  card_labels := hS

noncomputable def uncross
    (S : SupportFamily X Λ) (a b : Λ) : SupportFamily X Λ :=
  by
    classical
    exact fun c => if c = a then S a ∪ S b else if c = b then S a ∩ S b else S c

theorem uncross_at_left
    (S : SupportFamily X Λ) {a b : Λ} (h : a ≠ b) :
    uncross S a b a = S a ∪ S b := by
  simp [uncross, h]

theorem uncross_at_right
    (S : SupportFamily X Λ) {a b : Λ} (h : a ≠ b) :
    uncross S a b b = S a ∩ S b := by
  have hba : b ≠ a := Ne.symm h
  simp [uncross, h, hba]

theorem uncross_away
    (S : SupportFamily X Λ) {a b c : Λ} (hca : c ≠ a) (hcb : c ≠ b) :
    uncross S a b c = S c := by
  simp [uncross, hca, hcb]

/-!
## Exact-incidence preservation

Uncrossing changes only the two indexed supports.  At a fixed left vertex,
the pair of membership bits `(a,b)` is replaced by `(a ∨ b, a ∧ b)`, so its
cardinality is unchanged.  The only nontrivial case is when the vertex lies
in `S b` but not `S a`; there the two labels are exchanged, witnessed below
by `Equiv.swap`.
-/

theorem exactSupportIncidence_uncross
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (hab : a ≠ b)
    (hS : ExactSupportIncidence G S) :
    ExactSupportIncidence G (uncross S a b) := by
  intro x
  have hcard :
      (listsOfSupports (uncross S a b) x).card =
        (listsOfSupports S x).card := by
    by_cases ha : x ∈ S a
    · by_cases hb : x ∈ S b
      · apply congrArg Finset.card
        ext c
        by_cases hca : c = a
        · subst c
          simp [listsOfSupports, uncross, ha, hb, hab]
        · by_cases hcb : c = b
          · subst c
            simp [listsOfSupports, uncross, ha, hb, hab, hca]
          · simp [listsOfSupports, uncross, hca, hcb]
      · apply congrArg Finset.card
        ext c
        by_cases hca : c = a
        · subst c
          simp [listsOfSupports, uncross, ha, hb, hab]
        · by_cases hcb : c = b
          · subst c
            simp [listsOfSupports, uncross, ha, hb, hab, hca]
          · simp [listsOfSupports, uncross, hca, hcb]
    · by_cases hb : x ∈ S b
      · let e : Equiv.Perm Λ := Equiv.swap a b
        symm
        refine Finset.card_bij
          (s := listsOfSupports S x)
          (t := listsOfSupports (uncross S a b) x)
          (fun c _ => e c) ?_ ?_ ?_
        · intro c hc
          rw [mem_listsOfSupports] at hc ⊢
          by_cases hca : c = a
          · subst c
            simp [e, Equiv.swap_apply_def, ha] at hc
          · by_cases hcb : c = b
            · subst c
              simp [e, Equiv.swap_apply_def, uncross, hb, hab, hca]
            · simpa [e, Equiv.swap_apply_def, uncross, hca, hcb] using hc
        · intro c hc c' hc' heq
          exact e.injective heq
        · intro c hc
          refine ⟨e c, ?_, ?_⟩
          · rw [mem_listsOfSupports]
            rw [mem_listsOfSupports] at hc
            by_cases hca : c = a
            · subst c
              simp [e, Equiv.swap_apply_def, uncross, hb, hab] at hc ⊢
            · by_cases hcb : c = b
              · subst c
                simp [e, Equiv.swap_apply_def, uncross, hab, hca, ha] at hc
              · simpa [e, Equiv.swap_apply_def, uncross, hca, hcb] using hc
          · simpa [e] using (e.symm_apply_apply c)
      · apply congrArg Finset.card
        ext c
        by_cases hca : c = a
        · subst c
          simp [listsOfSupports, uncross, ha, hb, hab]
        · by_cases hcb : c = b
          · subst c
            simp [listsOfSupports, uncross, ha, hb, hab, hca]
          · simp [listsOfSupports, uncross, hca, hcb]
  exact hcard.trans (hS x)

noncomputable def supportPotential
    (S : SupportFamily X Λ) : ℤ :=
  ∑ c, ((S c).card : ℤ) ^ 2

def IsIncomparable (A B : Finset X) : Prop :=
  ¬ A ⊆ B ∧ ¬ B ⊆ A

/-!
## Strict cardinality increase

This is the finite-set part of the support-potential argument.  The two
strict inclusions supplied by incomparability make both difference regions
nonempty.  Writing their cardinalities as `p` and `q`, the increase is the
identity `2 * p * q`.
-/

theorem card_sq_union_inter_gt
    {A B : Finset X} (h : IsIncomparable A B) :
    (A ∪ B).card ^ 2 + (A ∩ B).card ^ 2 >
      A.card ^ 2 + B.card ^ 2 := by
  have hIA : (A ∩ B).card < A.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro hEq
    apply h.1
    intro x hx
    have hx' : x ∈ A ∩ B := by
      rw [hEq]
      exact hx
    exact (Finset.mem_inter.mp hx').2
  have hIB : (A ∩ B).card < B.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
    intro hEq
    apply h.2
    intro x hx
    have hx' : x ∈ A ∩ B := by
      rw [hEq]
      exact hx
    exact (Finset.mem_inter.mp hx').1
  let p : ℕ := A.card - (A ∩ B).card
  let q : ℕ := B.card - (A ∩ B).card
  have hA : A.card = (A ∩ B).card + p := by
    dsimp [p]
    omega
  have hB : B.card = (A ∩ B).card + q := by
    dsimp [q]
    omega
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hU : (A ∪ B).card = (A ∩ B).card + p + q := by
    have hcard := Finset.card_union_add_card_inter A B
    omega
  have hpq : 0 < 2 * p * q := by
    exact Nat.mul_pos (Nat.mul_pos (by decide) hp) hq
  calc
    (A ∪ B).card ^ 2 + (A ∩ B).card ^ 2 =
        ((A ∩ B).card + p + q) ^ 2 + (A ∩ B).card ^ 2 := by
          rw [hU]
    _ = ((A ∩ B).card + p) ^ 2 +
        ((A ∩ B).card + q) ^ 2 + 2 * p * q := by ring
    _ > ((A ∩ B).card + p) ^ 2 +
        ((A ∩ B).card + q) ^ 2 := Nat.lt_add_of_pos_right hpq
    _ = A.card ^ 2 + B.card ^ 2 := by rw [hA, hB]

/-- The change of the whole indexed potential is exactly the change in its
two selected slots. Distinctness matters even when the two supports agree. -/
theorem supportPotential_uncross_sub
    (S : SupportFamily X Λ) {a b : Λ} (hab : a ≠ b) :
    supportPotential (uncross S a b) - supportPotential S =
      ((S a ∪ S b).card : ℤ) ^ 2 + ((S a ∩ S b).card : ℤ) ^ 2 -
        (S a).card ^ 2 - (S b).card ^ 2 := by
  classical
  have hslot (c : Λ) :
      ((uncross S a b c).card : ℤ) ^ 2 =
        ((S c).card : ℤ) ^ 2 +
          (if c = a then ((S a ∪ S b).card : ℤ) ^ 2 - (S a).card ^ 2 else 0) +
          (if c = b then ((S a ∩ S b).card : ℤ) ^ 2 - (S b).card ^ 2 else 0) := by
    by_cases hca : c = a
    · subst c
      simp [uncross, hab]
    · by_cases hcb : c = b
      · subst c
        simp [uncross, hca]
      · simp [uncross, hca, hcb]
  unfold supportPotential
  simp_rw [hslot]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The exact integer identity in v13.23, Section `sec:main` (Termination). -/
theorem supportPotential_uncross_change
    (S : SupportFamily X Λ) {a b : Λ} (hab : a ≠ b) :
    supportPotential (uncross S a b) - supportPotential S =
      2 * ((S a \ S b).card : ℤ) * ((S b \ S a).card : ℤ) := by
  rw [supportPotential_uncross_sub S hab]
  have hU := Finset.card_union_add_card_inter (S a) (S b)
  have hA := Finset.card_sdiff_add_card_inter (S a) (S b)
  have hB := Finset.card_sdiff_add_card_inter (S b) (S a)
  rw [Finset.inter_comm (S b) (S a)] at hB
  have hU' : ((S a ∪ S b).card : ℤ) + (S a ∩ S b).card =
      (S a).card + (S b).card := by exact_mod_cast hU
  have hA' : ((S a \ S b).card : ℤ) + (S a ∩ S b).card =
      (S a).card := by exact_mod_cast hA
  have hB' : ((S b \ S a).card : ℤ) + (S a ∩ S b).card =
      (S b).card := by exact_mod_cast hB
  nlinarith

/-- Incomparable supports strictly increase the full potential. No graph
regularity or labeling-count hypothesis is needed for this finite-set fact. -/
theorem supportPotential_uncross_gt
    (S : SupportFamily X Λ) {a b : Λ}
    (h : IsIncomparable (S a) (S b)) :
    supportPotential S < supportPotential (uncross S a b) := by
  have hab : a ≠ b := by
    intro hab
    subst b
    exact h.1 (Finset.Subset.refl _)
  have hcard : ((S a).card : ℤ) ^ 2 + ((S b).card : ℤ) ^ 2 <
      ((S a ∪ S b).card : ℤ) ^ 2 + ((S a ∩ S b).card : ℤ) ^ 2 := by
    exact_mod_cast card_sq_union_inter_gt h
  have hchange := supportPotential_uncross_sub S hab
  linarith

/-- The former proof target is now a proved theorem, with its original
quantifiers and hypotheses. -/
theorem PotentialIncreaseStatement :
    ∀ (S : SupportFamily X Λ) (a b : Λ),
      IsIncomparable (S a) (S b) →
        supportPotential (uncross S a b) > supportPotential S := by
  intro S a b h
  exact supportPotential_uncross_gt S h

/-- The explicit finite upper bound used in the manuscript's termination
argument; empty label slots remain in the index type. -/
theorem supportPotential_le (S : SupportFamily X Λ) :
    supportPotential S ≤ (Fintype.card Λ : ℤ) * (Fintype.card X : ℤ) ^ 2 := by
  classical
  calc
    supportPotential S ≤ ∑ _c : Λ, (Fintype.card X : ℤ) ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      have hcard : ((S c).card : ℤ) ≤ Fintype.card X := by
        exact_mod_cast Finset.card_le_univ (S c)
      have hnonneg : (0 : ℤ) ≤ (S c).card := by positivity
      nlinarith
    _ = _ := by simp [mul_comm]

end BachThesisLean
