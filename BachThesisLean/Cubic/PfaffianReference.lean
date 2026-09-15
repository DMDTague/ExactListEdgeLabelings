import BachThesisLean.Cubic.PfaffianCore

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Independence of the shore reference

The determinant sign of a bipartite perfect matching is defined in
`PfaffianCore` relative to a harmless fixed equivalence `X ≃ Y`.  Replacing
that equivalence multiplies the permutation sign of *every* perfect matching
by the same constant sign.  Hence the property that all signed matching terms
agree is independent of the chosen reference.
-/

/-- Changing the shore identification composes every matching permutation on
the left by the same permutation. -/
theorem PerfectMatching.referencePerm_change
    (r s : X ≃ Y) (P : G.PerfectMatching) :
    P.referencePerm s =
      (r.trans s.symm : Equiv.Perm X) * P.referencePerm r := by
  ext x
  simp [PerfectMatching.referencePerm, Equiv.Perm.mul_apply]

/-- Consequently every signed matching term changes by one constant sign,
independent of the matching. -/
theorem PerfectMatching.signedTerm_changeReference
    (r s : X ≃ Y) (edgeSign : E → ℤˣ) (P : G.PerfectMatching) :
    P.signedTerm s edgeSign =
      Equiv.Perm.sign (r.trans s.symm : Equiv.Perm X) *
        P.signedTerm r edgeSign := by
  rw [PerfectMatching.signedTerm, PerfectMatching.signedTerm,
    P.referencePerm_change r s, Equiv.Perm.sign_mul]
  ac_rfl

/-- A Pfaffian signing relative to one shore identification is a Pfaffian
signing relative to every other shore identification, with the same edge-copy
signs. -/
def PfaffianSigning.changeReference
    {r s : X ≃ Y} (S : PfaffianSigning G r) : PfaffianSigning G s where
  edgeSign := S.edgeSign
  terms_eq := by
    intro P Q
    rw [P.signedTerm_changeReference r s S.edgeSign,
      Q.signedTerm_changeReference r s S.edgeSign]
    exact congrArg
      (Equiv.Perm.sign (r.trans s.symm : Equiv.Perm X) * ·)
      (S.terms_eq P Q)

@[simp] theorem PfaffianSigning.changeReference_edgeSign
    {r s : X ≃ Y} (S : PfaffianSigning G r) :
    (S.changeReference : PfaffianSigning G s).edgeSign = S.edgeSign := rfl

/-- Reference change is reversible at the level of existence of a signing. -/
theorem exists_pfaffianSigning_iff_reference
    (r s : X ≃ Y) :
    Nonempty (PfaffianSigning G r) ↔ Nonempty (PfaffianSigning G s) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.changeReference⟩
  · rintro ⟨S⟩
    exact ⟨S.changeReference⟩

end BipartiteMultigraph
end BachThesisLean
