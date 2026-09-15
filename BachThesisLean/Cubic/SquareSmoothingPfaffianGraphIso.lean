import BachThesisLean.Cubic.SquareSmoothingPfaffianIso

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Edge-copy isomorphism for the Pfaffian square factorization

After the pairing restriction and two odd-path smoothings, there are exactly
three kinds of remaining edge copies:

* an original copy surviving the whole square deletion;
* the fresh copy created by the first odd-path smoothing;
* the fresh copy created by the second odd-path smoothing.

They correspond respectively to an old square-smoothing survivor, fresh edge
`false`, and fresh edge `true`.  Together with the shore equivalences from
`SquareSmoothingPfaffianIso`, this gives the explicit graph isomorphism needed
for Pfaffian transport.
-/

/-- A square-smoothing survivor, regarded as a survivor of the first retained
odd path. -/
noncomputable def squareSurvivorAfterFirst (swap : Bool) (e : Q.Survivor) :
    (Q.firstPairingOddPathFrame swap).Survivor := by
  let a : {g : E // g ∈ Q.pairingRestrictionEdges swap} :=
    ⟨e.val, (Q.mem_pairingRestrictionEdges swap e.val).2 (Or.inl e.property.1)⟩
  refine ⟨a, ?_⟩
  constructor
  · change G.left e.val ≠ Q.leftVertex (squarePair swap false)
    exact Q.survivor_left_ne e (squarePair swap false)
  · change G.right e.val ≠ Q.rightVertex false
    exact Q.survivor_right_ne e false

/-- A square-smoothing survivor remains an old copy after the second retained
odd path as well. -/
noncomputable def squareSurvivorAfterSecond (swap : Bool) (e : Q.Survivor) :
    (Q.secondPairingOddPathFrame swap).Survivor := by
  let F := Q.firstPairingOddPathFrame swap
  let b : F.Survivor := Q.squareSurvivorAfterFirst swap e
  refine ⟨F.oldEdge b, ?_⟩
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change G.left e.val = Q.leftVertex (squarePair swap true) at hv
    exact Q.survivor_left_ne e (squarePair swap true) hv
  · intro h
    have hv := congrArg Subtype.val h
    change G.right e.val = Q.rightVertex true at hv
    exact Q.survivor_right_ne e true hv

/-- The fresh copy created by the first retained odd path survives the second
smoothing. -/
noncomputable def firstFreshAfterSecond (swap : Bool) :
    (Q.secondPairingOddPathFrame swap).Survivor := by
  let F := Q.firstPairingOddPathFrame swap
  refine ⟨F.freshEdge, ?_⟩
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change Q.externalLeft false = Q.leftVertex (squarePair swap true) at hv
    exact Q.externalLeft_ne false (squarePair swap true) hv
  · intro h
    have hv := congrArg Subtype.val h
    change Q.externalRight (squarePair swap false) = Q.rightVertex true at hv
    exact Q.externalRight_ne (squarePair swap false) true hv

/-- Flatten the nested two-step smoothing edge-copy type into the direct square
smoothing edge-copy type.  The two fresh copies retain distinct Boolean tags. -/
noncomputable def twoStepEdgeEquiv (swap : Bool) :
    (Q.secondPairingOddPathFrame swap).SmoothEdge ≃ Q.SmoothEdge := by
  let F := Q.firstPairingOddPathFrame swap
  let S := Q.secondPairingOddPathFrame swap
  refine
    { toFun := fun a =>
        match a with
        | .inr _ => .inr true
        | .inl ⟨.inr _, _⟩ => .inr false
        | .inl ⟨.inl b, h⟩ =>
            .inl ⟨b.val.val, Q.survives_after_pairing_two_smoothings swap b h⟩
      invFun := fun a =>
        match a with
        | .inr false => S.oldEdge (Q.firstFreshAfterSecond swap)
        | .inr true => S.freshEdge
        | .inl e => S.oldEdge (Q.squareSurvivorAfterSecond swap e)
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    cases a with
    | inr t =>
        cases t
        rfl
    | inl s =>
        rcases s with ⟨a, ha⟩
        cases a with
        | inr t =>
            cases t
            apply congrArg Sum.inl
            apply Subtype.ext
            rfl
        | inl b =>
            apply congrArg Sum.inl
            apply Subtype.ext
            change F.oldEdge (Q.squareSurvivorAfterFirst swap
              ⟨b.val.val, Q.survives_after_pairing_two_smoothings swap b ha⟩) =
                F.oldEdge b
            apply congrArg F.oldEdge
            apply Subtype.ext
            apply Subtype.ext
            rfl
  · intro a
    cases a with
    | inl e =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
    | inr i =>
        cases i <;> rfl

/-- The graph obtained by the pairing restriction followed by two odd-path
smoothings is isomorphic, edge-copy for edge-copy, to the direct square
smoothing for the same pairing. -/
noncomputable def twoStepGraphIso (swap : Bool) :
    GraphIso
      (Q.secondPairingOddPathFrame swap).smooth
      (Q.smooth swap) where
  leftEquiv := Q.twoStepLeftEquiv swap
  rightEquiv := Q.twoStepRightEquiv swap
  edgeEquiv := Q.twoStepEdgeEquiv swap
  map_left := by
    intro a
    cases a with
    | inr t =>
        cases t
        apply Subtype.ext
        rfl
    | inl s =>
        rcases s with ⟨a, ha⟩
        cases a with
        | inr t =>
            cases t
            apply Subtype.ext
            rfl
        | inl b =>
            apply Subtype.ext
            rfl
  map_right := by
    intro a
    cases a with
    | inr t =>
        cases t
        apply Subtype.ext
        rfl
    | inl s =>
        rcases s with ⟨a, ha⟩
        cases a with
        | inr t =>
            cases t
            apply Subtype.ext
            rfl
        | inl b =>
            apply Subtype.ext
            rfl

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
