import BachThesisLean.Cubic.StarProductPortCriterion
import BachThesisLean.Cubic.Regression

namespace BachThesisLean
namespace BipartiteMultigraph

open CubicRegression

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# The fixed four-vertex amplifier

`CubicRegression.amplifier` is the manuscript graph

    [2 1]
    [1 2]

with the two parallel ports at the first left vertex indexed `0,1` and the
third port indexed `2`.  `amplifier_vertexRootMask` already proves that the
other left vertex has root mask `{0,1}`.  The result below packages the second
half of Lemma `lem:four-vertex-amplifier`: a singleton edge-root mask can be
sent to the missing amplifier port and therefore becomes an empty star-product
intersection.
-/

/-- Swap the unique source port with the amplifier's missing port. -/
def portPermutationToThird (i : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap i (2 : Fin 3)

@[simp] theorem portPermutationToThird_apply (i : Fin 3) :
    portPermutationToThird i i = (2 : Fin 3) := by
  simp [portPermutationToThird]

/-- Right-root form of the four-vertex amplification lemma.  If a surviving
edge has a singleton edge-root mask, a suitable port permutation makes the
corresponding cross-shore edge/vertex pair fail EVP in the star product with
the fixed four-vertex graph. -/
theorem singleton_edgeRootMask_amplified_failure_right
    (A : BipartiteMultigraph X Y E) (hA : A.IsCubic)
    (r : Y) (p : A.PortEnumeration (.inr r))
    (e : {e : E // A.right e ≠ r}) (i : Fin 3)
    (hmask : A.edgeRootMask (.inr r) p e.1 = {i}) :
    ∃ σ : Equiv.Perm (Fin 3),
      ¬ (A.starProduct amplifier r 0 p amplifierPorts σ).EdgeVertexWitness
        (Sum.inl e : StarEdge A amplifier r 0)
        (A.starBVertexMap amplifier r 0 amplifierPorts
          (Sum.inl (1 : Fin 2))) := by
  classical
  let σ : Equiv.Perm (Fin 3) := portPermutationToThird i
  refine ⟨σ, ?_⟩
  intro hEV
  have hinter :
      (A.starPortMaskIntersection amplifier r 0 p amplifierPorts σ e.1
        (Sum.inl (1 : Fin 2))).Nonempty :=
    (A.starEdgeVertexWitness_iff_portMaskIntersection_nonempty
      amplifier r 0 p amplifierPorts σ hA amplifier_cubic e
      (Sum.inl (1 : Fin 2)) (by decide)).1 hEV
  obtain ⟨j, hj⟩ := hinter
  have hj' :=
    (A.mem_starPortMaskIntersection amplifier r 0 p amplifierPorts σ e.1
      (Sum.inl (1 : Fin 2)) j).1 hj
  have hjSingleton : j ∈ ({i} : Finset (Fin 3)) := by
    rw [← hmask]
    exact hj'.1
  have hji : j = i := by simpa using hjSingleton
  subst j
  have hAmp : σ i ∈ ({0, 1} : Finset (Fin 3)) := by
    rw [← amplifier_vertexRootMask]
    exact hj'.2
  have hsigma : σ i = (2 : Fin 3) := by
    simp [σ]
  rw [hsigma] at hAmp
  exact (by decide : ¬ ((2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)))) hAmp

/-- The same amplification statement at the global EVP level: the singleton
mask produces a concrete edge/vertex pair witnessing failure of `HasEVP`. -/
theorem singleton_edgeRootMask_amplified_not_hasEVP_right
    (A : BipartiteMultigraph X Y E) (hA : A.IsCubic)
    (r : Y) (p : A.PortEnumeration (.inr r))
    (e : {e : E // A.right e ≠ r}) (i : Fin 3)
    (hmask : A.edgeRootMask (.inr r) p e.1 = {i}) :
    ∃ σ : Equiv.Perm (Fin 3),
      ¬ (A.starProduct amplifier r 0 p amplifierPorts σ).HasEVP := by
  obtain ⟨σ, hfail⟩ :=
    A.singleton_edgeRootMask_amplified_failure_right hA r p e i hmask
  refine ⟨σ, ?_⟩
  intro hEVP
  exact hfail (hEVP
    (Sum.inl e : StarEdge A amplifier r 0)
    (A.starBVertexMap amplifier r 0 amplifierPorts
      (Sum.inl (1 : Fin 2))))

end BipartiteMultigraph
end BachThesisLean
