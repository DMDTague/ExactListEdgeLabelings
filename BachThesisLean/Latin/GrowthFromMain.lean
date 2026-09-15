import BachThesisLean.Uncrossing.MainBound
import BachThesisLean.Latin.ResidualEquiv
import BachThesisLean.Latin.Regression
import BachThesisLean.Latin.GrowthBound

namespace BachThesisLean

open ExactLeftLists LatinSquare
open scoped BigOperators

/-!
# Unconditional Latin growth from the exact-list theorem

The crown graph `R_n = K_{n,n} - M` supplies the manuscript's bridge from the
exact-list lower bound to Latin-square growth.  Its ordinary `(n-1)`-colouring
count is `V_n`, while its canonical residual-list count is `U_{n+1}`.  The
machine-checked main theorem therefore gives `V_n ≤ U_{n+1}`.  Normalization
then converts this to `L_{n+1} ≥ (n+1)! L_n` and hence to the superfactorial
lower bound.
-/

/-- The crown-graph one-step inequality `V_n ≤ U_{n+1}`. -/
theorem V_le_U_succ (n : ℕ) (hn : 0 < n) :
    V n hn ≤ U (n + 1) (Nat.succ_pos n) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbound :
      ordinaryCount (crownGraph n) (n - 1) (crown_left_regular n) ≤
        (crownResidualLists n).count :=
    exactListLowerBound_of_nonempty_left
      (crownGraph n) (n - 1) (crown_left_regular n) (crownResidualLists n)
  calc
    V n hn = ordinaryCount (crownGraph n) (n - 1) (crown_left_regular n) :=
      (crown_ordinaryCount_eq_V n hn).symm
    _ ≤ (crownResidualLists n).count := hbound
    _ = U (n + 1) (Nat.succ_pos n) := crownResidual_count_eq_U n hn

/-- Canonical-count form of the one-step inequality. -/
theorem factorial_mul_U_le_U_succ (n : ℕ) (hn : 0 < n) :
    Nat.factorial (n - 1) * U n hn ≤ U (n + 1) (Nat.succ_pos n) := by
  rw [← V_eq_factorial_mul_U n hn]
  exact V_le_U_succ n hn

/-- Reduced-count form of the one-step inequality. -/
theorem factorial_mul_rho_le_rho_succ (n : ℕ) (hn : 0 < n) :
    Nat.factorial (n - 1) * ρ n hn ≤
      ρ (n + 1) (Nat.succ_pos n) := by
  rw [← U_eq_rho n hn, ← U_eq_rho (n + 1) (Nat.succ_pos n)]
  exact factorial_mul_U_le_U_succ n hn

/-- The manuscript's total Latin-square growth step,
`L_{n+1} ≥ (n+1)! L_n`. -/
theorem latin_growth_step (n : ℕ) (hn : 1 ≤ n) :
    Nat.factorial (n + 1) * L n ≤ L (n + 1) := by
  have hnpos : 0 < n := hn
  have hrho := factorial_mul_rho_le_rho_succ n hnpos
  calc
    Nat.factorial (n + 1) * L n =
        Nat.factorial (n + 1) *
          (Nat.factorial n * Nat.factorial (n - 1) * ρ n hnpos) := by
      rw [L_eq_factorial_mul_factorial_mul_rho n hnpos]
    _ = (Nat.factorial (n + 1) * Nat.factorial n) *
          (Nat.factorial (n - 1) * ρ n hnpos) := by
      ac_rfl
    _ ≤ (Nat.factorial (n + 1) * Nat.factorial n) *
          ρ (n + 1) (Nat.succ_pos n) :=
      Nat.mul_le_mul_left _ hrho
    _ = Nat.factorial (n + 1) * Nat.factorial ((n + 1) - 1) *
          ρ (n + 1) (Nat.succ_pos n) := by
      simp only [Nat.add_sub_cancel]
    _ = L (n + 1) :=
      (L_eq_factorial_mul_factorial_mul_rho
        (n + 1) (Nat.succ_pos n)).symm

/-- The conditional step assumed in `GrowthBound.lean` is now discharged by
the kernel-checked graph-theoretic development. -/
theorem latin_growth_step_machineChecked :
    ∀ n ≥ 1, L (n + 1) ≥ Nat.factorial (n + 1) * L n := by
  intro n hn
  exact latin_growth_step n hn

/-- Unconditional superfactorial lower bound for the total number of Latin
squares, obtained by iterating the machine-checked growth step. -/
theorem latin_superfactorial_lowerBound :
    ∀ n ≥ 1, L n ≥ ∏ j in Finset.Icc 1 n, Nat.factorial j :=
  superfactorial_of_step L L_one latin_growth_step_machineChecked

end BachThesisLean
