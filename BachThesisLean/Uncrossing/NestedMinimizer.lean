import BachThesisLean.Uncrossing.CanonicalPalette
import BachThesisLean.Uncrossing.Monotonicity

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# The degree-sequence nested minimizer

The one-step component injection is iterated to a nested terminal family.  Its
labels are sorted by support cardinality, where `sortedSupport_normalForm`
identifies it with the canonical threshold family.  Empty prefix slots are
then deleted by `canonicalSupport_count_eq_of_le`.
-/

/-- Canonical minimization for any chosen degree bound `K` that fits inside
the ambient finite label type. The manuscript's `K = max_x d(x)` is a special
case. -/
theorem exactList_count_ge_canonical
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G Λ)
    (K : ℕ) (hdeg : ∀ x, G.leftDegree x ≤ K)
    (hKcard : K ≤ Fintype.card Λ) :
    (exactListsOfSupports (canonicalSupport G K)
      (canonicalSupport_exact G K hdeg)).count ≤ L.count := by
  classical
  let S : SupportFamily X Λ := supportFamilyOfLists L
  have hS : ExactSupportIncidence G S := by
    simpa [S] using supportFamilyOfLists_exact G L
  obtain ⟨T, hT, _hST, hnested, hcount⟩ :=
    exists_nested_exact_uncrossing_count_le G S hS
  have hdegCard : ∀ x, G.leftDegree x ≤ Fintype.card Λ := by
    intro x
    exact (hdeg x).trans hKcard
  let hSorted : ExactSupportIncidence G (sortedSupport T) :=
    exactSupportIncidence_sortedSupport G T hT
  let hCardCanonical :
      ExactSupportIncidence G (canonicalSupport G (Fintype.card Λ)) :=
    canonicalSupport_exact G (Fintype.card Λ) hdegCard
  have hshape :
      sortedSupport T = canonicalSupport G (Fintype.card Λ) :=
    sortedSupport_eq_canonicalSupport G T hT hnested
  have hcanonicalSorted :
      (exactListsOfSupports (canonicalSupport G (Fintype.card Λ))
        hCardCanonical).count =
        (exactListsOfSupports (sortedSupport T) hSorted).count := by
    exact (exactListsOfSupports_count_eq_of_eq
      G hSorted hCardCanonical hshape).symm
  have hsortedT :
      (exactListsOfSupports (sortedSupport T) hSorted).count =
        (exactListsOfSupports T hT).count := by
    have h := sortedSupport_count_eq G T hT
    exact h.trans
      (exactListsOfSupports_count_proof_irrel G T _ _)
  have hcanonicalK :
      (exactListsOfSupports (canonicalSupport G (Fintype.card Λ))
        (canonicalSupport_exact G (Fintype.card Λ) hdegCard)).count =
        (exactListsOfSupports (canonicalSupport G K)
          (canonicalSupport_exact G K hdeg)).count :=
    canonicalSupport_count_eq_of_le G hKcard hdeg
  have hSL : (exactListsOfSupports S hS).count = L.count := by
    have hproof : hS = supportFamilyOfLists_exact G L := Subsingleton.elim _ _
    subst hS
    simpa [S] using exactListsOfSupports_supportFamilyOfLists_count G L
  calc
    (exactListsOfSupports (canonicalSupport G K)
      (canonicalSupport_exact G K hdeg)).count =
        (exactListsOfSupports (canonicalSupport G (Fintype.card Λ))
          (canonicalSupport_exact G (Fintype.card Λ) hdegCard)).count :=
      hcanonicalK.symm
    _ = (exactListsOfSupports (canonicalSupport G (Fintype.card Λ))
          hCardCanonical).count :=
      exactListsOfSupports_count_proof_irrel G _ _ _
    _ = (exactListsOfSupports (sortedSupport T) hSorted).count := hcanonicalSorted
    _ = (exactListsOfSupports T hT).count := hsortedT
    _ ≤ (exactListsOfSupports S hS).count := hcount
    _ = L.count := hSL

/-- The maximum degree on the left shore, with value zero when that shore is
empty. -/
noncomputable def leftMaxDegree (G : BipartiteMultigraph X Y E) : ℕ := by
  classical
  exact Finset.univ.sup G.leftDegree

/-- Every left degree is bounded by the finite maximum left degree. -/
theorem leftDegree_le_leftMaxDegree
    (G : BipartiteMultigraph X Y E) (x : X) :
    G.leftDegree x ≤ leftMaxDegree G := by
  classical
  unfold leftMaxDegree
  exact Finset.le_sup (f := G.leftDegree) (Finset.mem_univ x)

/-- Exactness of an ambient list assignment forces the maximum left degree to
fit inside its finite label type. -/
theorem leftMaxDegree_le_labelCard
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G Λ) :
    leftMaxDegree G ≤ Fintype.card Λ := by
  classical
  unfold leftMaxDegree
  apply Finset.sup_le
  intro x hx
  rw [← L.card_labels x]
  exact Finset.card_le_univ (L.labels x)

/-- The manuscript's canonical degree-sequence suffix assignment, represented
zero-based: vertex `x` receives precisely the final `d(x)` labels in
`Fin (leftMaxDegree G)`. -/
noncomputable def degreeSequenceCanonicalLists
    (G : BipartiteMultigraph X Y E) :
    ExactLeftLists G (Fin (leftMaxDegree G)) :=
  exactListsOfSupports (canonicalSupport G (leftMaxDegree G))
    (canonicalSupport_exact G (leftMaxDegree G)
      (leftDegree_le_leftMaxDegree G))

/-- Manuscript v13.23 `thm:nested`: among exact left-list assignments, the
canonical suffix family determined only by the left degree sequence minimizes
the number of admissible completions. -/
theorem nested_minimizer
    (G : BipartiteMultigraph X Y E) (L : ExactLeftLists G Λ) :
    (degreeSequenceCanonicalLists G).count ≤ L.count := by
  exact exactList_count_ge_canonical G L (leftMaxDegree G)
    (leftDegree_le_leftMaxDegree G) (leftMaxDegree_le_labelCard G L)

end BachThesisLean
