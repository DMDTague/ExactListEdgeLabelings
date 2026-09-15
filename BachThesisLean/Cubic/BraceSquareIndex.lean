import BachThesisLean.Cubic.FiveVertexMinimalCounterexample

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Indexing every square in a nontrivial cubic brace

The five-shore counting proof used a strict-Hall bound only under the equality
`|X| = 5`.  The local bound itself needs much less: two left vertices leave
room for the strict-Hall `+2` as soon as `4 ≤ |X|`.  Consequently, in a simple
cubic brace of that size, any displayed `K₂,₂` has exactly the two displayed
right vertices as common neighbours and is represented by `squareLeftPairs`.
-/

/-- In a cubic brace with at least four left vertices, two distinct left
vertices have at most two common right neighbours. -/
theorem IsBrace.commonRightSet_card_le_two_of_four_le_card_left
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : 4 ≤ Fintype.card X)
    {x x' : X} (hxx : x ≠ x') :
    (G.commonRightSet x x').card ≤ 2 := by
  classical
  let S : Finset X := {x, x'}
  have hScard : S.card = 2 := by
    simp [S, hxx]
  have hSnonempty : S.Nonempty := by
    simp [S]
  have hroom : S.card + 2 ≤ Fintype.card X := by
    rw [hScard]
    exact hX
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

namespace SquareFrame

/-- Every displayed square in a cubic brace with at least four left vertices
is captured by the unordered-left-pair square index. -/
theorem IsBrace.leftSupport_mem_squareLeftPairs
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : 4 ≤ Fintype.card X) (Q : SquareFrame G) :
    ({Q.leftVertex false, Q.leftVertex true} : Finset X) ∈
      G.squareLeftPairs := by
  classical
  let S : Finset X := {Q.leftVertex false, Q.leftVertex true}
  let T : Finset Y := {Q.rightVertex false, Q.rightVertex true}
  have hScard : S.card = 2 := by
    simp [S, Q.leftVertex_ne]
  have hTcard : T.card = 2 := by
    simp [T, Q.rightVertex_ne]
  have hcommonLe :
      (G.commonRightSet (Q.leftVertex false) (Q.leftVertex true)).card ≤ 2 :=
    hbrace.commonRightSet_card_le_two_of_four_le_card_left
      hG hX Q.leftVertex_ne
  have hTsub :
      T ⊆ G.commonRightSet (Q.leftVertex false) (Q.leftVertex true) := by
    intro y hy
    apply (G.mem_commonRightSet (Q.leftVertex false) (Q.leftVertex true) y).2
    constructor
    · exact Q.right_mem_rightNeighborSet_of_mem_support
        (by simp [S]) (by simpa [T] using hy)
    · exact Q.right_mem_rightNeighborSet_of_mem_support
        (by simp [S]) (by simpa [T] using hy)
  have hcommonGe :
      2 ≤ (G.commonRightSet (Q.leftVertex false) (Q.leftVertex true)).card := by
    have h := Finset.card_le_card hTsub
    rw [hTcard] at h
    exact h
  have hcommonEq :
      (G.commonRightSet (Q.leftVertex false) (Q.leftVertex true)).card = 2 := by
    omega
  apply (G.mem_squareLeftPairs S).2
  refine ⟨hScard, ?_⟩
  rw [show S = {Q.leftVertex false, Q.leftVertex true} by rfl,
    G.pairCommonRightSet_pair]
  exact hcommonEq

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
