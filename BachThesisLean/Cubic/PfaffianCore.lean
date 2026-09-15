import BachThesisLean.Cubic.MatchingShoreEquiv
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Pfaffian signing core

For a bipartite graph, a perfect matching determines a bijection from the left
shore to the right shore.  Relative to one fixed shore equivalence
`reference : X ≃ Y`, this is a permutation of `X`; mathlib's canonical
`Equiv.Perm.sign : ℤˣ` is therefore exactly the permutation sign appearing in
the determinant term.

An edge signing is a function from *actual edge copies* to `ℤˣ` (hence to
`±1`).  The signed matching term is the permutation sign times the product of
the signs of the selected copies.  A Pfaffian signing is one for which all
perfect-matching terms agree.

This file contains definitions only; it deliberately makes no claim that an
arbitrary graph admits such a signing.
-/

/-- The permutation represented by a perfect matching relative to a fixed
identification of the two shores. -/
noncomputable def PerfectMatching.referencePerm
    (reference : X ≃ Y) (P : G.PerfectMatching) : Equiv.Perm X :=
  P.shoreEquiv.trans reference.symm

/-- Determinant term of a perfect matching for a fixed edge signing. -/
noncomputable def PerfectMatching.signedTerm
    (reference : X ≃ Y) (edgeSign : E → ℤˣ)
    (P : G.PerfectMatching) : ℤˣ :=
  (P.referencePerm reference).sign * ∏ e ∈ P.val, edgeSign e

/-- A Pfaffian signing relative to a fixed shore identification: every perfect
matching has the same signed determinant term. -/
structure PfaffianSigning
    (G : BipartiteMultigraph X Y E) (reference : X ≃ Y) where
  edgeSign : E → ℤˣ
  terms_eq : ∀ P Q : G.PerfectMatching,
    P.signedTerm reference edgeSign = Q.signedTerm reference edgeSign

/-- A Pfaffian witness packages the harmless choice of shore identification
together with a signing whose perfect-matching terms all agree. -/
structure PfaffianWitness (G : BipartiteMultigraph X Y E) where
  reference : X ≃ Y
  signing : PfaffianSigning G reference

/-- The equality supplied by a Pfaffian signing, exposed with the matching
arguments first for convenient rewriting. -/
theorem PfaffianSigning.signedTerm_eq
    {reference : X ≃ Y} (S : PfaffianSigning G reference)
    (P Q : G.PerfectMatching) :
    P.signedTerm reference S.edgeSign = Q.signedTerm reference S.edgeSign :=
  S.terms_eq P Q

end BipartiteMultigraph
end BachThesisLean
