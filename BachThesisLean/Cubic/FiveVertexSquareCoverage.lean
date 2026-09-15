import BachThesisLean.Cubic.FiveVertexSquareCountGlobal

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# How many left-indexed squares can one edge cover?

A square indexed by an unordered left pair `S` can contain an edge `e` only if
`G.left e ∈ S` and every vertex of `S` is adjacent to `G.right e`.  At a simple
cubic right vertex there are exactly three left neighbours, one of which is
`G.left e`.  Thus there are at most two such two-element left pairs.
-/

/-- Left-indexed squares that could contain a fixed edge, expressed entirely
in endpoint-neighbourhood language. -/
noncomputable def squareLeftPairsAtEdge
    (G : BipartiteMultigraph X Y E) (e : E) : Finset (Finset X) :=
  G.squareLeftPairs.filter fun S =>
    G.left e ∈ S ∧ S ⊆ G.leftNeighborSet (G.right e)

@[simp] theorem mem_squareLeftPairsAtEdge
    (G : BipartiteMultigraph X Y E) (e : E) (S : Finset X) :
    S ∈ G.squareLeftPairsAtEdge e ↔
      S ∈ G.squareLeftPairs ∧ G.left e ∈ S ∧
        S ⊆ G.leftNeighborSet (G.right e) := by
  classical
  simp [squareLeftPairsAtEdge]

/-- The left endpoint of an edge is one of the left neighbours of its right
endpoint. -/
theorem left_mem_leftNeighborSet_right
    (G : BipartiteMultigraph X Y E) (e : E) :
    G.left e ∈ G.leftNeighborSet (G.right e) := by
  apply (G.mem_leftNeighborSet (G.right e) (G.left e)).2
  exact ⟨e, (G.mem_rightIncident (G.right e) e).2 rfl, rfl⟩

/-- Removing the edge's own left endpoint from the three left neighbours of its
right endpoint leaves exactly two vertices. -/
theorem leftNeighborSet_erase_left_card_eq_two
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (e : E) :
    ((G.leftNeighborSet (G.right e)).erase (G.left e)).card = 2 := by
  classical
  have hcard : (G.leftNeighborSet (G.right e)).card = 3 :=
    G.leftNeighborSet_card_eq_three_of_simple_cubic hsimple hG (G.right e)
  have hmem : G.left e ∈ G.leftNeighborSet (G.right e) :=
    G.left_mem_leftNeighborSet_right e
  have hadd := Finset.card_erase_add_one hmem
  omega

/-- A fixed edge can cover at most two left-indexed squares in a simple cubic
graph.  The proof maps each covered pair to its singleton of "the other" left
vertex. -/
theorem squareLeftPairsAtEdge_card_le_two
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (e : E) :
    (G.squareLeftPairsAtEdge e).card ≤ 2 := by
  classical
  let F : Finset (Finset X) := G.squareLeftPairsAtEdge e
  let N : Finset X := (G.leftNeighborSet (G.right e)).erase (G.left e)
  let eraseLeft : Finset X → Finset X := fun S => S.erase (G.left e)
  have hinj : Set.InjOn eraseLeft F := by
    intro S hSF T hTF hEq
    have hS := (G.mem_squareLeftPairsAtEdge e S).1 (by simpa [F] using hSF)
    have hT := (G.mem_squareLeftPairsAtEdge e T).1 (by simpa [F] using hTF)
    rw [← Finset.insert_erase hS.2.1, ← Finset.insert_erase hT.2.1]
    exact congrArg (fun U : Finset X => insert (G.left e) U) hEq
  let I : Finset (Finset X) := F.image eraseLeft
  have hcardImage : I.card = F.card := by
    dsimp [I]
    exact Finset.card_image_iff.mpr hinj
  have hsub : I ⊆ N.powersetCard 1 := by
    intro U hUI
    obtain ⟨S, hSF, rfl⟩ := Finset.mem_image.mp (by simpa [I] using hUI)
    have hS := (G.mem_squareLeftPairsAtEdge e S).1 (by simpa [F] using hSF)
    have hScard : S.card = 2 :=
      (G.mem_squareLeftPairs S).1 hS.1 |>.1
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro z hz
      have hz' := Finset.mem_erase.mp hz
      apply Finset.mem_erase.mpr
      exact ⟨hz'.1, hS.2.2 hz'.2⟩
    · rw [Finset.card_erase_of_mem hS.2.1, hScard]
  have hNcard : N.card = 2 := by
    simpa [N] using G.leftNeighborSet_erase_left_card_eq_two hsimple hG e
  have hPowCard : (N.powersetCard 1).card = 2 := by
    simp [hNcard]
  have hle := Finset.card_le_card hsub
  rw [hcardImage, hPowCard] at hle
  simpa [F] using hle

end BipartiteMultigraph
end BachThesisLean
