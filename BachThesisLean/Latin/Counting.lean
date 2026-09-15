import BachThesisLean.Latin.Reduced
import Mathlib.Data.Fintype.Perm

namespace BachThesisLean

open LatinSquare

/-!
# Finite cardinalities of the Latin normalization classes

All counts here refer to the subtypes in `Latin.Defs`. In particular, no
enumeration table is used, and all positive orders, including one, are covered.
-/

noncomputable instance lastFixingPermFintype (m : ℕ) (hm : 0 < m) :
    Fintype (LastFixingPerm m hm) := by
  classical
  unfold LastFixingPerm
  infer_instance

/-- Remove the distinguished final index. When `m = 1` the result is empty. -/
def lastComplementEquiv (m : ℕ) (hm : 0 < m) :
    Fin (m - 1) ≃ {i : Fin m // i ≠ lastSymbol m hm} := by
  cases m with
  | zero => omega
  | succ n =>
    simpa [lastSymbol, lastIndex] using (finSuccAboveEquiv (Fin.last n))

private def lastFixingPointwiseEquiv (m : ℕ) (hm : 0 < m) :
    LastFixingPerm m hm ≃
      {p : Equiv.Perm (Fin m) // ∀ i, ¬(i ≠ lastSymbol m hm) → p i = i} where
  toFun p := ⟨p.1, by
    intro i hi
    have h : i = lastSymbol m hm := not_not.mp hi
    simpa [h] using p.2⟩
  invFun p := ⟨p.1, p.2 _ (by simp)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

/-- Restrict a final-symbol-fixing permutation to the other `m - 1` symbols. -/
noncomputable def lastFixingPermEquiv (m : ℕ) (hm : 0 < m) :
    LastFixingPerm m hm ≃ Equiv.Perm (Fin (m - 1)) :=
  (lastFixingPointwiseEquiv m hm).trans
    ((Equiv.Perm.subtypeEquivSubtypePerm (fun i => i ≠ lastSymbol m hm)).symm.trans
      (Equiv.permCongr (lastComplementEquiv m hm).symm))

theorem card_lastFixingPerm (m : ℕ) (hm : 0 < m) :
    Fintype.card (LastFixingPerm m hm) = Nat.factorial (m - 1) := by
  rw [Fintype.card_congr (lastFixingPermEquiv m hm), Fintype.card_perm,
    Fintype.card_fin]

theorem V_eq_factorial_mul_U (m : ℕ) (hm : 0 < m) :
    V m hm = Nat.factorial (m - 1) * U m hm := by
  rw [V_eq_card, U_eq_card, card_constantDiagonalClass hm, card_lastFixingPerm]

theorem U_eq_rho (m : ℕ) (hm : 0 < m) : U m hm = ρ m hm := by
  rw [U_eq_card, rho_eq_card]
  exact Fintype.card_congr (canonicalReducedEquiv hm)

theorem V_eq_factorial_mul_rho (m : ℕ) (hm : 0 < m) :
    V m hm = Nat.factorial (m - 1) * ρ m hm := by
  rw [V_eq_factorial_mul_U, U_eq_rho]

end BachThesisLean
