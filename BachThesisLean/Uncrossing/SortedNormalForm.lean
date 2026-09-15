import BachThesisLean.Uncrossing.Reindex
import BachThesisLean.Uncrossing.NormalForm
import Mathlib.Data.Fin.Tuple.Sort

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# Sorting an unordered nested terminal family

`IsNested` records a total inclusion chain but deliberately does not choose an
order on the label type.  For a finite label type we first enumerate the slots
by `Fin (card Λ)` and then use `Tuple.sort` on support cardinalities.  Nestedness
upgrades the resulting weak cardinality order to actual support inclusion.
This supplies the ordered hypothesis required by `monotone_support_normalForm`.
-/

/-- Support cardinalities in an arbitrary finite enumeration of the labels. -/
noncomputable def supportCardTuple (S : SupportFamily X Λ) :
    Fin (Fintype.card Λ) → ℕ :=
  fun i => (S ((Fintype.equivFin Λ).symm i)).card

/-- The equivalence that enumerates support slots in nondecreasing order of
support cardinality. -/
noncomputable def supportSortEquiv (S : SupportFamily X Λ) :
    Fin (Fintype.card Λ) ≃ Λ :=
  (Tuple.sort (supportCardTuple S)).trans (Fintype.equivFin Λ).symm

/-- A nested support family with its indexed slots sorted by cardinality. -/
noncomputable def sortedSupport (S : SupportFamily X Λ) :
    SupportFamily X (Fin (Fintype.card Λ)) :=
  reindexSupport S (supportSortEquiv S)

/-- Sorting a nested family by cardinality sorts it by inclusion as well. -/
theorem sortedSupport_monotone
    (S : SupportFamily X Λ) (hnested : IsNested S) :
    Monotone (sortedSupport S) := by
  classical
  intro i j hij
  have hcard :
      (S (supportSortEquiv S i)).card ≤
        (S (supportSortEquiv S j)).card := by
    have hmono := Tuple.monotone_sort (supportCardTuple S)
    have hij' := hmono hij
    simpa [supportCardTuple, supportSortEquiv] using hij'
  rcases hnested (supportSortEquiv S i) (supportSortEquiv S j) with hsub | hsub
  · exact hsub
  · have heq :
        S (supportSortEquiv S j) = S (supportSortEquiv S i) :=
      Finset.eq_of_subset_of_card_le hsub hcard
    simpa [sortedSupport, reindexSupport, heq]

/-- Exact incidence survives the sorting reindexing. -/
theorem exactSupportIncidence_sortedSupport
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) :
    ExactSupportIncidence G (sortedSupport S) := by
  classical
  exact exactSupportIncidence_reindex G S (supportSortEquiv S) hS

/-- Sorting the support slots leaves the completion count unchanged. -/
theorem sortedSupport_count_eq
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) :
    (exactListsOfSupports (sortedSupport S)
      (exactSupportIncidence_sortedSupport G S hS)).count =
      (exactListsOfSupports S hS).count := by
  classical
  exact exactListsOfSupports_reindex_count G S (supportSortEquiv S) hS

/-- An arbitrary nested exact support family, after canonical sorting of its
indexed slots, has exactly the threshold form determined by the degree
sequence. -/
theorem sortedSupport_normalForm
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) (hnested : IsNested S)
    (j : Fin (Fintype.card Λ)) :
    sortedSupport S j =
      Finset.univ.filter
        (fun x => Fintype.card Λ - j.val ≤ G.leftDegree x) := by
  classical
  exact monotone_support_normalForm G (sortedSupport S)
    (sortedSupport_monotone S hnested)
    (exactSupportIncidence_sortedSupport G S hS) j

end BachThesisLean
