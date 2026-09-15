import BachThesisLean.Cubic.FiveVertexSquareCount
import BachThesisLean.Cubic.FourVertexBraceCase
import Mathlib.Data.Finset.Powerset

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# The five-shore square double count

Index a square by its unordered pair of left vertices.  For a two-element left
set `S`, `pairCommonRightSet G S` is its set of common right neighbours.  In a
five-shore cubic brace strict Hall bounds this common-neighbour set by two.
Double counting incidences `(S,y)` with `|S| = 2` and every vertex of `S`
adjacent to `y` gives fifteen incidences: each of the five right vertices has
three left neighbours and therefore three two-subsets.  Since there are ten
left pairs and each contributes at most two incidences, at least five left
pairs contribute two, hence index genuine squares.
-/

/-- All unordered two-element subsets of the left shore. -/
noncomputable def leftPairs (X : Type u) [Fintype X] [DecidableEq X] :
    Finset (Finset X) :=
  (Finset.univ : Finset X).powersetCard 2

/-- Right vertices adjacent to every vertex in a finite left set. -/
noncomputable def pairCommonRightSet
    (G : BipartiteMultigraph X Y E) (S : Finset X) : Finset Y :=
  (Finset.univ : Finset Y).filter fun y =>
    ∀ x ∈ S, y ∈ G.rightNeighborSet x

/-- Two-element left subsets with exactly two common right neighbours. -/
noncomputable def squareLeftPairs
    (G : BipartiteMultigraph X Y E) : Finset (Finset X) :=
  (leftPairs X).filter fun S => (G.pairCommonRightSet S).card = 2

@[simp] theorem mem_leftPairs (S : Finset X) :
    S ∈ leftPairs X ↔ S.card = 2 := by
  classical
  simp [leftPairs]

@[simp] theorem mem_pairCommonRightSet
    (G : BipartiteMultigraph X Y E) (S : Finset X) (y : Y) :
    y ∈ G.pairCommonRightSet S ↔
      ∀ x ∈ S, y ∈ G.rightNeighborSet x := by
  classical
  simp [pairCommonRightSet]

@[simp] theorem mem_squareLeftPairs (G : BipartiteMultigraph X Y E)
    (S : Finset X) :
    S ∈ G.squareLeftPairs ↔
      S.card = 2 ∧ (G.pairCommonRightSet S).card = 2 := by
  classical
  simp [squareLeftPairs]

/-- On a literal two-element pair, the unordered common-neighbour definition
agrees with the ordered intersection used by the local strict-Hall lemma. -/
theorem pairCommonRightSet_pair
    (G : BipartiteMultigraph X Y E) (x x' : X) :
    G.pairCommonRightSet {x, x'} = G.commonRightSet x x' := by
  classical
  ext y
  simp [pairCommonRightSet, commonRightSet, and_left_comm, and_assoc]

/-- There are ten unordered left pairs when the left shore has five vertices. -/
theorem leftPairs_card_eq_ten (hX : Fintype.card X = 5) :
    (leftPairs X).card = 10 := by
  classical
  simp [leftPairs, hX, Nat.choose]

/-- Every left pair in a five-shore cubic brace has at most two common right
neighbours. -/
theorem IsBrace.pairCommonRightSet_card_le_two_of_card_left_eq_five
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : Fintype.card X = 5)
    {S : Finset X} (hS : S ∈ leftPairs X) :
    (G.pairCommonRightSet S).card ≤ 2 := by
  classical
  have hScard : S.card = 2 := (mem_leftPairs S).1 hS
  obtain ⟨x, x', hxx, hpair⟩ := Finset.card_eq_two.mp hScard
  subst S
  rw [G.pairCommonRightSet_pair x x']
  exact hbrace.commonRightSet_card_le_two_of_card_left_eq_five hG hX hxx

/-- For a fixed right vertex, the left pairs all of whose vertices meet that
right vertex are exactly the two-subsets of its left-neighbour set. -/
theorem leftPairs_filter_at_right
    (G : BipartiteMultigraph X Y E) (y : Y) :
    (leftPairs X).filter (fun S =>
      ∀ x ∈ S, y ∈ G.rightNeighborSet x) =
      (G.leftNeighborSet y).powersetCard 2 := by
  classical
  ext S
  simp only [Finset.mem_filter, mem_leftPairs, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hcard, hall⟩
    refine ⟨?_, hcard⟩
    intro x hx
    exact (G.mem_leftNeighborSet_iff_mem_rightNeighborSet x y).2
      (hall x hx)
  · rintro ⟨hsub, hcard⟩
    refine ⟨hcard, ?_⟩
    intro x hx
    exact (G.mem_leftNeighborSet_iff_mem_rightNeighborSet x y).1
      (hsub hx)

/-- The common-neighbour cardinality is the sum of its membership indicators. -/
theorem pairCommonRightSet_card_eq_indicator_sum
    (G : BipartiteMultigraph X Y E) (S : Finset X) :
    (G.pairCommonRightSet S).card =
      ∑ y : Y, if (∀ x ∈ S, y ∈ G.rightNeighborSet x) then 1 else 0 := by
  classical
  symm
  simpa [pairCommonRightSet] using
    (Finset.sum_boole (R := ℕ)
      (fun y : Y => ∀ x ∈ S, y ∈ G.rightNeighborSet x)
      (Finset.univ : Finset Y))

/-- Double counting `(left pair, common right neighbour)` gives exactly fifteen
incidences in a simple cubic five-by-five graph. -/
theorem sum_pairCommonRightSet_card_eq_fifteen
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (hX : Fintype.card X = 5) :
    (∑ S ∈ leftPairs X, (G.pairCommonRightSet S).card) = 15 := by
  classical
  have hY : Fintype.card Y = 5 := by
    calc
      Fintype.card Y = Fintype.card X :=
        (G.card_left_eq_card_right_of_cubic hG).symm
      _ = 5 := hX
  calc
    (∑ S ∈ leftPairs X, (G.pairCommonRightSet S).card)
        = ∑ S ∈ leftPairs X,
            ∑ y : Y,
              if (∀ x ∈ S, y ∈ G.rightNeighborSet x) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact G.pairCommonRightSet_card_eq_indicator_sum S
    _ = ∑ y : Y,
          ∑ S ∈ leftPairs X,
            if (∀ x ∈ S, y ∈ G.rightNeighborSet x) then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ y : Y, 3 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_boole]
          rw [G.leftPairs_filter_at_right y]
          simp [G.leftNeighborSet_card_eq_three_of_simple_cubic hsimple hG y]
    _ = 15 := by simp [hY]

/-- At least five unordered left pairs index squares in a five-shore cubic
brace. -/
theorem IsBrace.five_le_squareLeftPairs_card
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : Fintype.card X = 5) :
    5 ≤ G.squareLeftPairs.card := by
  classical
  have hsimple : G.IsSimple :=
    hbrace.isSimple_of_three_le_card_left hG (by omega)
  have htotal := G.sum_pairCommonRightSet_card_eq_fifteen hsimple hG hX
  have hPcard := leftPairs_card_eq_ten (X := X) hX
  let P : Finset (Finset X) := leftPairs X
  let Q : Finset (Finset X) := G.squareLeftPairs
  have hpoint : ∀ S ∈ P,
      (G.pairCommonRightSet S).card ≤
        1 + if (G.pairCommonRightSet S).card = 2 then 1 else 0 := by
    intro S hS
    have hle := hbrace.pairCommonRightSet_card_le_two_of_card_left_eq_five
      hG hX (by simpa [P] using hS)
    by_cases htwo : (G.pairCommonRightSet S).card = 2
    · simp [htwo]
    · have hone : (G.pairCommonRightSet S).card ≤ 1 := by omega
      simpa [htwo] using hone
  have hsumle :
      (∑ S ∈ P, (G.pairCommonRightSet S).card) ≤
        ∑ S ∈ P,
          (1 + if (G.pairCommonRightSet S).card = 2 then 1 else 0) := by
    exact Finset.sum_le_sum fun S hS => hpoint S hS
  have hrhs :
      (∑ S ∈ P,
          (1 + if (G.pairCommonRightSet S).card = 2 then 1 else 0)) =
        P.card + Q.card := by
    rw [Finset.sum_add_distrib]
    have hQ :
        P.filter (fun S => (G.pairCommonRightSet S).card = 2) = Q := by
      rfl
    rw [Finset.sum_boole]
    simp [hQ]
  have hsum : (∑ S ∈ P, (G.pairCommonRightSet S).card) = 15 := by
    simpa [P] using htotal
  have hpc : P.card = 10 := by simpa [P] using hPcard
  have hbound : 15 ≤ 10 + Q.card := by
    rw [hsum, hrhs, hpc] at hsumle
    exact hsumle
  simpa [Q] using (show 5 ≤ Q.card by omega)

end BipartiteMultigraph
end BachThesisLean
