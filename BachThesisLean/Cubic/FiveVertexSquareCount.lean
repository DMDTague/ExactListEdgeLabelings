import BachThesisLean.Cubic.BraceStrictHall
import BachThesisLean.Cubic.SquareFrameFromCorners
import BachThesisLean.Cubic.FourVertexBraceCase

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Square counting on five vertices per shore

For a simple cubic brace with five vertices on each shore, strict Hall applied
to two left vertices says that they have at most two common right neighbours.
Whenever equality holds, the corresponding `K₂,₂` gives four actual edge
copies and hence, by `SquareFrameFromCorners`, a genuine smoothing frame.

The global double count is built on top of these local facts.
-/

/-- Common right neighbours of two left vertices. -/
noncomputable def commonRightSet (G : BipartiteMultigraph X Y E)
    (x x' : X) : Finset Y :=
  G.rightNeighborSet x ∩ G.rightNeighborSet x'

@[simp] theorem mem_commonRightSet
    (G : BipartiteMultigraph X Y E) (x x' : X) (y : Y) :
    y ∈ G.commonRightSet x x' ↔
      y ∈ G.rightNeighborSet x ∧ y ∈ G.rightNeighborSet x' := by
  classical
  simp [commonRightSet]

/-- The two-element `biUnion` is the union of the two neighbour sets. -/
theorem biUnion_pair_rightNeighborSet
    (G : BipartiteMultigraph X Y E) (x x' : X) :
    ({x, x'} : Finset X).biUnion G.rightNeighborSet =
      G.rightNeighborSet x ∪ G.rightNeighborSet x' := by
  classical
  ext y
  simp [or_comm, or_left_comm, or_assoc]

/-- In a five-left-vertex cubic brace, two distinct left vertices have at most
two common right neighbours.  This is the strict-Hall inequality for the
left pair written in intersection form. -/
theorem IsBrace.commonRightSet_card_le_two_of_card_left_eq_five
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : Fintype.card X = 5)
    {x x' : X} (hxx : x ≠ x') :
    (G.commonRightSet x x').card ≤ 2 := by
  classical
  let S : Finset X := {x, x'}
  have hScard : S.card = 2 := by
    simp [S, hxx]
  have hSnonempty : S.Nonempty := by
    simp [S]
  have hroom : S.card + 2 ≤ Fintype.card X := by
    rw [hScard, hX]
    omega
  have hHall := hbrace.rightNeighbor_union_card_ge_add_two hG S hSnonempty hroom
  have hUnion :
      4 ≤ (G.rightNeighborSet x ∪ G.rightNeighborSet x').card := by
    rw [G.biUnion_pair_rightNeighborSet x x', hScard] at hHall
    simpa using hHall
  have hsimple : G.IsSimple :=
    hbrace.isSimple_of_three_le_card_left hG (by omega)
  have hxcard : (G.rightNeighborSet x).card = 3 :=
    G.rightNeighborSet_card_eq_three_of_simple_cubic hsimple hG x
  have hx'card : (G.rightNeighborSet x').card = 3 :=
    G.rightNeighborSet_card_eq_three_of_simple_cubic hsimple hG x'
  have hIE := Finset.card_union_add_card_inter
    (G.rightNeighborSet x) (G.rightNeighborSet x')
  change
    (G.rightNeighborSet x ∪ G.rightNeighborSet x').card +
      (G.commonRightSet x x').card =
      (G.rightNeighborSet x).card + (G.rightNeighborSet x').card at hIE
  rw [hxcard, hx'card] at hIE
  omega

/-- Turn four occupied endpoint cells into square corners.  The supplied edge
copies are chosen from the four cells; endpoint separation makes them distinct
as copies even before simplicity is used. -/
noncomputable def squareCornersOfCommonNeighbors
    (G : BipartiteMultigraph X Y E)
    (x0 x1 : X) (hx : x0 ≠ x1)
    (y0 y1 : Y) (hy : y0 ≠ y1)
    (hy00 : y0 ∈ G.rightNeighborSet x0)
    (hy01 : y1 ∈ G.rightNeighborSet x0)
    (hy10 : y0 ∈ G.rightNeighborSet x1)
    (hy11 : y1 ∈ G.rightNeighborSet x1) :
    SquareCorners G := by
  classical
  let lx : Bool → X := fun i => if i then x1 else x0
  let ry : Bool → Y := fun j => if j then y1 else y0
  have hlx : Function.Injective lx := by
    intro i k hik
    cases i <;> cases k <;> simp_all [lx, hx]
  have hry : Function.Injective ry := by
    intro j l hjl
    cases j <;> cases l <;> simp_all [ry, hy]
  have hcell : ∀ i j : Bool,
      ∃ e : E, G.left e = lx i ∧ G.right e = ry j := by
    intro i j
    cases i <;> cases j
    · obtain ⟨e, heI, heR⟩ := (mem_rightNeighborSet G x0 y0).1 hy00
      exact ⟨e, (G.mem_leftIncident x0 e).1 heI, heR⟩
    · obtain ⟨e, heI, heR⟩ := (mem_rightNeighborSet G x0 y1).1 hy01
      exact ⟨e, (G.mem_leftIncident x0 e).1 heI, heR⟩
    · obtain ⟨e, heI, heR⟩ := (mem_rightNeighborSet G x1 y0).1 hy10
      exact ⟨e, (G.mem_leftIncident x1 e).1 heI, heR⟩
    · obtain ⟨e, heI, heR⟩ := (mem_rightNeighborSet G x1 y1).1 hy11
      exact ⟨e, (G.mem_leftIncident x1 e).1 heI, heR⟩
  choose edge hedgeLeft hedgeRight using hcell
  exact
    { leftVertex := lx
      rightVertex := ry
      square := edge
      leftVertex_ne := by
        change lx false ≠ lx true
        simpa [lx] using hx
      rightVertex_ne := by
        change ry false ≠ ry true
        simpa [ry] using hy
      square_left := hedgeLeft
      square_right := hedgeRight
      square_injective := by
        intro p q hpq
        apply Prod.ext
        · apply hlx
          exact (hedgeLeft p.1 p.2).symm.trans
            ((congrArg G.left hpq).trans (hedgeLeft q.1 q.2))
        · apply hry
          exact (hedgeRight p.1 p.2).symm.trans
            ((congrArg G.right hpq).trans (hedgeRight q.1 q.2)) }

/-- Exactly two common right neighbours determine some full square frame in a
simple cubic graph.  This is kept existential so no proposition is eliminated
into data; callers that need a canonical chosen frame can make their own
noncomputable choice from finite endpoint data. -/
theorem exists_squareFrame_of_commonRightCardTwo
    (G : BipartiteMultigraph X Y E)
    (hsimple : G.IsSimple) (hG : G.IsCubic)
    {x x' : X} (hxx : x ≠ x')
    (hcommon : (G.commonRightSet x x').card = 2) :
    ∃ Q : SquareFrame G, True := by
  classical
  obtain ⟨y0, y1, hy, hset⟩ := Finset.card_eq_two.mp hcommon
  have hy0 : y0 ∈ G.commonRightSet x x' := by simp [hset]
  have hy1 : y1 ∈ G.commonRightSet x x' := by simp [hset]
  have h0 := (G.mem_commonRightSet x x' y0).1 hy0
  have h1 := (G.mem_commonRightSet x x' y1).1 hy1
  refine ⟨(G.squareCornersOfCommonNeighbors x x' hxx y0 y1 hy
      h0.1 h1.1 h0.2 h1.2).toSquareFrame hsimple hG, trivial⟩

end BipartiteMultigraph
end BachThesisLean
