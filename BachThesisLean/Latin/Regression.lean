import BachThesisLean.Latin.TotalNormalization
import Mathlib.Tactic.FinCases

namespace BachThesisLean

open LatinSquare

/-!
# Small-order normalization certificates

Orders one and two are proved by explicit squares and uniqueness arguments.
The numerical counts are consequences of those certificates and the proved
normalization formula, rather than imported enumeration data.
-/

def singletonLatinSquare : LatinSquare 1 where
  entry := fun i _ => i
  row_bijective := fun _ =>
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun j => ⟨j, Subsingleton.elim _ _⟩⟩
  column_bijective := fun _ => Function.bijective_id

theorem singletonLatinSquare_unique (Q : LatinSquare 1) : Q = singletonLatinSquare := by
  apply LatinSquare.ext
  intro i j
  exact Subsingleton.elim _ _

theorem L_one : L 1 = 1 := by
  letI : Unique (LatinSquare 1) :=
    ⟨⟨singletonLatinSquare⟩, singletonLatinSquare_unique⟩
  exact Fintype.card_unique

theorem rho_one : ρ 1 (by decide) = 1 := by
  have h := L_eq_factorial_mul_factorial_mul_rho 1 (by decide)
  simpa [L_one] using h.symm

theorem U_one : U 1 (by decide) = 1 := by
  rw [U_eq_rho, rho_one]

theorem V_one : V 1 (by decide) = 1 := by
  rw [V_eq_factorial_mul_rho]
  simp [rho_one]

theorem lastFixingPerm_card_one :
    Fintype.card (LastFixingPerm 1 (by decide)) = 1 := by
  rw [card_lastFixingPerm]
  rfl

def binaryLatinSquare : LatinSquare 2 where
  entry := fun i j => i + j
  row_bijective := fun i => (Equiv.addLeft i).bijective
  column_bijective := fun j => (Equiv.addRight j).bijective

def binaryReducedSquare : ReducedClass 2 (by decide) :=
  ⟨binaryLatinSquare, by
    constructor
    · intro j
      change 0 + j = j
      exact zero_add j
    · intro i
      change i + 0 = i
      exact add_zero i⟩

theorem binaryReducedSquare_unique (Q : ReducedClass 2 (by decide)) :
    Q = binaryReducedSquare := by
  apply Subtype.ext
  apply LatinSquare.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact Q.2.1 0
  · exact Q.2.1 1
  · exact Q.2.2 1
  · have hne : Q.1.entry 1 1 ≠ (1 : Fin 2) := by
      intro h
      have hfirst : Q.1.entry 1 0 = 1 := Q.2.2 1
      have hindex := (Q.1.row_bijective 1).1 (h.trans hfirst.symm)
      exact (by decide : (1 : Fin 2) ≠ 0) hindex
    have hval : (Q.1.entry 1 1).val ≠ 1 := fun h => hne (Fin.ext h)
    apply Fin.ext
    change (Q.1.entry 1 1).val = 0
    omega

theorem rho_two : ρ 2 (by decide) = 1 := by
  letI : Unique (ReducedClass 2 (by decide)) :=
    ⟨⟨binaryReducedSquare⟩, binaryReducedSquare_unique⟩
  rw [rho_eq_card]
  exact Fintype.card_unique

theorem U_two : U 2 (by decide) = 1 := by
  rw [U_eq_rho, rho_two]

theorem V_two : V 2 (by decide) = 1 := by
  rw [V_eq_factorial_mul_rho]
  simp [rho_two]

theorem L_two : L 2 = 2 := by
  rw [L_eq_factorial_mul_factorial_mul_rho 2 (by decide)]
  simp [rho_two, Nat.factorial]

theorem latin_growth_at_one : L 2 = Nat.factorial 2 * L 1 := by
  rw [L_two, L_one]
  rfl

end BachThesisLean
