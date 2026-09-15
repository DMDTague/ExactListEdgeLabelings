import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic

namespace BachThesisLean

/-!
# Latin squares and the normalized classes used by the canonical family

The manuscript numbers rows, columns, and symbols from `1` through `m`.
This file uses the equivalent zero-based `Fin m` representation.  Thus
`lastSymbol m hm` is the manuscript's symbol `m`, and `lastIndex m hm` is
its final row or column.

The definitions are deliberately separate from the numerical tables.  A
cardinality such as `reducedCount` is a cardinality of a finite type, not an
imported enumeration claim.
-/

universe u

structure LatinSquare (m : ℕ) where
  entry : Fin m → Fin m → Fin m
  row_bijective : ∀ i, Function.Bijective (fun j => entry i j)
  column_bijective : ∀ j, Function.Bijective (fun i => entry i j)

@[ext] theorem LatinSquare.ext {Q R : LatinSquare m}
    (h : ∀ i j, Q.entry i j = R.entry i j) : Q = R := by
  cases Q with
  | mk q qr qc =>
    cases R with
    | mk r rr rc =>
      have hqr : q = r := by
        funext i j
        exact h i j
      cases hqr
      rfl

namespace LatinSquare

instance finite (m : ℕ) : Finite (LatinSquare m) :=
  Finite.of_injective (fun Q => Q.entry) (by
    intro Q Q' h
    cases Q
    cases Q'
    cases h
    rfl)

noncomputable instance fintype (m : ℕ) : Fintype (LatinSquare m) := Fintype.ofFinite _

def firstIndex (m : ℕ) (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

def lastIndex (m : ℕ) (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩

abbrev lastSymbol (m : ℕ) (hm : 0 < m) : Fin m := lastIndex m hm

def IsConstantDiagonal (Q : LatinSquare m) (s : Fin m) : Prop :=
  ∀ i, Q.entry i i = s

def IsFinalColumnIdentity (Q : LatinSquare m) (hm : 0 < m) : Prop :=
  ∀ i, Q.entry i (lastIndex m hm) = i

def IsCanonical (Q : LatinSquare m) (hm : 0 < m) : Prop :=
  IsConstantDiagonal Q (lastSymbol m hm) ∧ IsFinalColumnIdentity Q hm

def IsConstantDiagonalSquare (Q : LatinSquare m) (hm : 0 < m) : Prop :=
  IsConstantDiagonal Q (lastSymbol m hm)

def IsReduced (Q : LatinSquare m) (hm : 0 < m) : Prop :=
  (∀ j, Q.entry (firstIndex m hm) j = j) ∧
  (∀ i, Q.entry i (firstIndex m hm) = i)

def CanonicalClass (m : ℕ) (hm : 0 < m) :=
  {Q : LatinSquare m // IsCanonical Q hm}

def ConstantDiagonalClass (m : ℕ) (hm : 0 < m) :=
  {Q : LatinSquare m // IsConstantDiagonalSquare Q hm}

def ReducedClass (m : ℕ) (hm : 0 < m) :=
  {Q : LatinSquare m // IsReduced Q hm}

noncomputable instance canonicalClassFintype (m : ℕ) (hm : 0 < m) :
    Fintype (CanonicalClass m hm) := by
  classical
  unfold CanonicalClass
  infer_instance

noncomputable instance constantDiagonalClassFintype (m : ℕ) (hm : 0 < m) :
    Fintype (ConstantDiagonalClass m hm) := by
  classical
  unfold ConstantDiagonalClass
  infer_instance

noncomputable instance reducedClassFintype (m : ℕ) (hm : 0 < m) :
    Fintype (ReducedClass m hm) := by
  classical
  unfold ReducedClass
  infer_instance

noncomputable def U (m : ℕ) (hm : 0 < m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun Q : LatinSquare m => IsCanonical Q hm)).card

noncomputable def V (m : ℕ) (hm : 0 < m) : ℕ := by
  classical
  exact
    (Finset.univ.filter
      (fun Q : LatinSquare m => IsConstantDiagonalSquare Q hm)).card

noncomputable def ρ (m : ℕ) (hm : 0 < m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun Q : LatinSquare m => IsReduced Q hm)).card

noncomputable def L (m : ℕ) : ℕ := by
  exact Fintype.card (LatinSquare m)

theorem U_eq_card (m : ℕ) (hm : 0 < m) :
    U m hm = Fintype.card (CanonicalClass m hm) := by
  classical
  unfold U CanonicalClass
  rw [Fintype.card_subtype]

theorem V_eq_card (m : ℕ) (hm : 0 < m) :
    V m hm = Fintype.card (ConstantDiagonalClass m hm) := by
  classical
  unfold V ConstantDiagonalClass
  rw [Fintype.card_subtype]

theorem rho_eq_card (m : ℕ) (hm : 0 < m) :
    ρ m hm = Fintype.card (ReducedClass m hm) := by
  classical
  unfold ρ ReducedClass
  rw [Fintype.card_subtype]

theorem L_eq_card (m : ℕ) : L m = Fintype.card (LatinSquare m) := rfl

theorem canonical_property (Q : CanonicalClass m hm) :
    IsCanonical Q.1 hm := Q.2

theorem constantDiagonal_property (Q : ConstantDiagonalClass m hm) :
    IsConstantDiagonalSquare Q.1 hm := Q.2

theorem reduced_property (Q : ReducedClass m hm) :
    IsReduced Q.1 hm := Q.2

end LatinSquare
end BachThesisLean
