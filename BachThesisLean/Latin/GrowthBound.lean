import BachThesisLean.Latin.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorial.Basic

namespace BachThesisLean

open scoped BigOperators

/-!
## A kernel-checked conditional superfactorial bound

The manuscript obtains the one-step inequality from the uncrossing theorem.
This file intentionally proves the arithmetic iteration as a standalone
theorem: its hypothesis is explicit, so the result does not silently claim
that the graph-theoretic step has already been formalized.
-/

theorem superfactorial_of_step
    (L : ℕ → ℕ)
    (hL1 : L 1 = 1)
    (hstep : ∀ n ≥ 1, L (n + 1) ≥ Nat.factorial (n + 1) * L n) :
    ∀ n ≥ 1, L n ≥ ∏ j in Finset.Icc 1 n, Nat.factorial j := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn
      by_cases hzero : n = 0
      · subst n
        simpa [hL1]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hzero
        have hprev : L n ≥ ∏ j in Finset.Icc 1 n, Nat.factorial j := ih hnpos
        have hIcc : Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hprod :
            (∏ j in Finset.Icc 1 (n + 1), Nat.factorial j) =
              Nat.factorial (n + 1) *
                ∏ j in Finset.Icc 1 n, Nat.factorial j := by
          rw [hIcc]
          exact Finset.prod_insert (by
            simp only [Finset.mem_Icc]
            omega)
        calc
          L (n + 1) ≥ Nat.factorial (n + 1) * L n := hstep n hnpos
          _ ≥ Nat.factorial (n + 1) *
              (∏ j in Finset.Icc 1 n, Nat.factorial j) :=
            Nat.mul_le_mul_left _ hprev
          _ = ∏ j in Finset.Icc 1 (n + 1), Nat.factorial j := hprod.symm

theorem superfactorial_of_step_at
    (L : ℕ → ℕ)
    (hstep : ∀ n ≥ 1, L (n + 1) ≥ Nat.factorial (n + 1) * L n)
    (n : ℕ) (hn : 1 ≤ n) (hL1 : L 1 = 1) :
    L n ≥ ∏ j in Finset.Icc 1 n, Nat.factorial j :=
  superfactorial_of_step L hL1 hstep n hn

end BachThesisLean
