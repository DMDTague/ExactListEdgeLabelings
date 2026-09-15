import BachThesisLean.Cubic.ShoreSwapAmplifier
import BachThesisLean.Cubic.PortMaskCharacterization

namespace BachThesisLean
namespace BipartiteMultigraph

open CubicRegression

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Pointwise universal-amplification reduction

This is the constructive core of manuscript Theorem
`thm:universal-eep-evp`.  If a connected cubic graph fails EEP, the port-mask
characterization produces a nonincident edge--root pair with a mask of size at
most one.  A zero mask already gives an EVP failure in the original graph.  A
singleton mask is sent to the fixed four-vertex amplifier, exchanging shores
when the bad root lies on the left.
-/

/-- Sharp pointwise form of the manuscript's universal EEP--EVP amplification
argument.  The second and third alternatives are the two possible root
orientations of `A star D`; the third uses `shoreSwap` to put a left root into
the right-root convention of `starProduct`. -/
theorem not_hasEEP_implies_not_hasEVP_or_fourVertexAmplifier
    (A : BipartiteMultigraph X Y E) (hconn : A.IsConnected) (hA : A.IsCubic)
    (hnotEEP : ¬ A.HasEEP) :
    (¬ A.HasEVP) ∨
      (∃ (r : Y) (σ : Equiv.Perm (Fin 3)),
        ¬ (A.starProduct amplifier r 0
            (A.portsOfCubic hA (.inr r)) amplifierPorts σ).HasEVP) ∨
      (∃ (x : X) (σ : Equiv.Perm (Fin 3)),
        ¬ (A.shoreSwap.starProduct amplifier x 0
            (A.shoreSwapPortEnumeration (.inl x)
              (A.portsOfCubic hA (.inl x))) amplifierPorts σ).HasEVP) := by
  classical
  have hchar := A.hasEEP_iff_edgeRootMask_card_ge_two hconn hA
  have hbadAll :
      ¬ (∀ (r : X ⊕ Y) (e : E), ¬ A.Incident e r →
        2 ≤ (A.edgeRootMask r (A.portsOfCubic hA r) e).card) := by
    intro hall
    exact hnotEEP (hchar.2 hall)
  obtain ⟨r, hr⟩ := Classical.not_forall.mp hbadAll
  obtain ⟨e, he⟩ := Classical.not_forall.mp hr
  have hne : ¬ A.Incident e r := by
    intro hinc
    apply he
    intro hne'
    exact (hne' hinc).elim
  have hnotge :
      ¬ 2 ≤ (A.edgeRootMask r (A.portsOfCubic hA r) e).card := by
    intro hge
    apply he
    intro _
    exact hge
  have hle : (A.edgeRootMask r (A.portsOfCubic hA r) e).card ≤ 1 := by
    omega
  by_cases hzero : (A.edgeRootMask r (A.portsOfCubic hA r) e).card = 0
  · left
    intro hEVP
    have hfail : ¬ A.EdgeVertexWitness e r :=
      (A.edgeRootMask_card_eq_zero_iff_not_edgeVertexWitness
        r (A.portsOfCubic hA r) e).1 hzero
    exact hfail (hEVP e r)
  · have hone : (A.edgeRootMask r (A.portsOfCubic hA r) e).card = 1 := by
      omega
    obtain ⟨i, hmask⟩ := Finset.card_eq_one.mp hone
    right
    cases r with
    | inl x =>
        right
        have hleft : A.left e ≠ x := by
          intro hx
          apply hne
          simpa [Incident] using hx
        let e' : {d : E // A.left d ≠ x} := ⟨e, hleft⟩
        obtain ⟨σ, hfail⟩ :=
          A.singleton_edgeRootMask_amplified_not_hasEVP_left hA x
            (A.portsOfCubic hA (.inl x)) e' i (by
              simpa [e'] using hmask)
        exact ⟨x, σ, hfail⟩
    | inr y =>
        left
        have hright : A.right e ≠ y := by
          intro hy
          apply hne
          simpa [Incident] using hy
        let e' : {d : E // A.right d ≠ y} := ⟨e, hright⟩
        obtain ⟨σ, hfail⟩ :=
          A.singleton_edgeRootMask_amplified_not_hasEVP_right hA y
            (A.portsOfCubic hA (.inr y)) e' i (by
              simpa [e'] using hmask)
        exact ⟨y, σ, hfail⟩

end BipartiteMultigraph
end BachThesisLean
