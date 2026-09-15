import BachThesisLean.Cubic.OddPathSmoothingPfaffian
import BachThesisLean.Cubic.PfaffianReference
import Mathlib.Data.Fintype.Card

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Pfaffian-witness closure under odd-path smoothing

`OddPathSmoothingPfaffian` proves the signing calculation relative to a chosen
equivalence of the reduced shores.  A packaged `PfaffianWitness` initially
comes with an arbitrary ambient shore equivalence.  Since smoothing removes
one left and one right vertex, the reduced shores still have equal cardinality;
we may therefore choose a reduced equivalence, change the ambient signing to
its canonical extension, and apply the already-proved smoothing theorem.
-/

/-- Removing one vertex from each of two equivalent finite shores leaves
equivalent reduced shores. -/
noncomputable def reducedShoreEquiv (ambient : X ≃ Y) :
    Q.ReducedLeft ≃ Q.ReducedRight :=
  Fintype.equivOfCardEq (by
    change Fintype.card {x : X // x ≠ Q.w} =
      Fintype.card {y : Y // y ≠ Q.z}
    rw [Fintype.card_subtype_compl (fun x : X => x = Q.w),
      Fintype.card_subtype_eq Q.w,
      Fintype.card_subtype_compl (fun y : Y => y = Q.z),
      Fintype.card_subtype_eq Q.z,
      Fintype.card_congr ambient])

/-- A Pfaffian witness descends through smoothing a saturated odd three-edge
path.  This is the witness-level form of the manuscript's elementary
odd-path-smoothing closure. -/
noncomputable def PfaffianWitness.smoothOddPath
    (W : PfaffianWitness G) : PfaffianWitness Q.smooth := by
  let reference : Q.ReducedLeft ≃ Q.ReducedRight :=
    Q.reducedShoreEquiv W.reference
  let signing : PfaffianSigning G (Q.extendReducedEquiv reference) :=
    W.signing.changeReference
  exact
    { reference := reference
      signing := PfaffianSigning.smoothOddPath Q reference signing }

/-- Existence form: Pfaffianness, represented by a packaged witness, is
preserved by odd-path smoothing. -/
theorem exists_pfaffianWitness_smoothOddPath
    (h : Nonempty (PfaffianWitness G)) :
    Nonempty (PfaffianWitness Q.smooth) := by
  rcases h with ⟨W⟩
  exact ⟨PfaffianWitness.smoothOddPath Q W⟩

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
