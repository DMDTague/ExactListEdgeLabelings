import BachThesisLean.Uncrossing.Fibre
import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]

/-- Every element of the two-element finite type is `0` or `1`. -/
theorem finTwo_eq_zero_or_one (c : Fin 2) : c = 0 ∨ c = 1 := by
  by_cases hc : c.val = 0
  · exact Or.inl (Fin.ext hc)
  · right
    apply Fin.ext
    omega

/-!
# The edge-copy line graph of a two-label fibre

Vertices of `fibreLineGraph G` are actual edge copies of the bipartite
multigraph. Two distinct copies are adjacent exactly when they share a left
or right endpoint. Thus parallel copies remain distinct vertices joined by an
edge; in particular the manuscript's parallel two-edge component is not
collapsed.
-/

/-- The simple line graph on actual edge copies of a bipartite multigraph. -/
def fibreLineGraph (G : BipartiteMultigraph X Y E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ (G.left e = G.left f ∨ G.right e = G.right f)
  symm := by
    rintro e f ⟨hne, hleft | hright⟩
    · exact ⟨hne.symm, Or.inl hleft.symm⟩
    · exact ⟨hne.symm, Or.inr hright.symm⟩
  loopless := by
    intro e h
    exact h.1 rfl

@[simp] theorem fibreLineGraph_adj (G : BipartiteMultigraph X Y E) (e f : E) :
    (fibreLineGraph G).Adj e f ↔
      e ≠ f ∧ (G.left e = G.left f ∨ G.right e = G.right f) :=
  Iff.rfl

/-- Every admissible edge labeling is a proper coloring of the edge-copy line
 graph. This packages left and right injectivity into the graph-theoretic
 object used for the alternating path/cycle argument. -/
def admissibleFibreColoring
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ)
    (σ : E → Λ) (hσ : L.IsAdmissible σ) :
    (fibreLineGraph G).Coloring Λ := by
  refine SimpleGraph.Coloring.mk σ ?_
  intro e f hef
  rcases hef.2 with hleft | hright
  · intro hcolor
    apply hef.1
    exact hσ.left_injOn (G.left e)
      ((G.mem_leftIncident (G.left e) e).2 rfl)
      ((G.mem_leftIncident (G.left e) f).2 hleft.symm) hcolor
  · intro hcolor
    apply hef.1
    exact hσ.right_injOn (G.right e)
      ((G.mem_rightIncident (G.right e) e).2 rfl)
      ((G.mem_rightIncident (G.right e) f).2 hright.symm) hcolor

@[simp] theorem admissibleFibreColoring_apply
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ)
    (σ : E → Λ) (hσ : L.IsAdmissible σ) (e : E) :
    admissibleFibreColoring L σ hσ e = σ e := rfl

/-- In finite edge-copy graphs the line-graph neighbors of `e` are exactly
all other copies at its left endpoint or all other copies at its right
endpoint. -/
noncomputable def fibreNeighbors [DecidableEq E]
    (G : BipartiteMultigraph X Y E) (e : E) : Finset E :=
  (G.leftIncident (G.left e)).erase e ∪
    (G.rightIncident (G.right e)).erase e

@[simp] theorem mem_fibreNeighbors [DecidableEq E]
    (G : BipartiteMultigraph X Y E) (e f : E) :
    f ∈ fibreNeighbors G e ↔ (fibreLineGraph G).Adj e f := by
  classical
  simp only [fibreNeighbors, Finset.mem_union, Finset.mem_erase,
    G.mem_leftIncident, G.mem_rightIncident, fibreLineGraph_adj]
  constructor
  · rintro (⟨hne, hleft⟩ | ⟨hne, hright⟩)
    · exact ⟨hne.symm, Or.inl hleft.symm⟩
    · exact ⟨hne.symm, Or.inr hright.symm⟩
  · rintro ⟨hne, hleft | hright⟩
    · exact Or.inl ⟨hne.symm, hleft.symm⟩
    · exact Or.inr ⟨hne.symm, hright.symm⟩

/-- If both shores have degree at most two, each edge copy has at most two
neighbors in the line graph. -/
theorem fibreNeighbors_card_le_two [DecidableEq E]
    (G : BipartiteMultigraph X Y E)
    (hleft : ∀ x, G.leftDegree x ≤ 2)
    (hright : ∀ y, G.rightDegree y ≤ 2)
    (e : E) : (fibreNeighbors G e).card ≤ 2 := by
  classical
  have heL : e ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) e).2 rfl
  have heR : e ∈ G.rightIncident (G.right e) :=
    (G.mem_rightIncident (G.right e) e).2 rfl
  have hLlt : ((G.leftIncident (G.left e)).erase e).card < 2 := by
    exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem heL) (hleft (G.left e))
  have hRlt : ((G.rightIncident (G.right e)).erase e).card < 2 := by
    exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem heR) (hright (G.right e))
  have hL : ((G.leftIncident (G.left e)).erase e).card ≤ 1 :=
    Nat.lt_succ_iff.mp hLlt
  have hR : ((G.rightIncident (G.right e)).erase e).card ≤ 1 :=
    Nat.lt_succ_iff.mp hRlt
  calc
    (fibreNeighbors G e).card ≤
        ((G.leftIncident (G.left e)).erase e).card +
          ((G.rightIncident (G.right e)).erase e).card := by
      exact Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add hL hR
    _ = 2 := rfl

/-- In the degree-at-most-two branch of a two-label fibre, the edge-copy line
 graph therefore has maximum finite neighbor count at most two. -/
theorem twoLabel_fibreNeighbors_card_le_two [DecidableEq E] [DecidableEq X]
    (G : BipartiteMultigraph X Y E) (A B : Finset X)
    (hdeg : ∀ x, G.leftDegree x =
      (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0))
    (hright : ∀ y, G.rightDegree y ≤ 2) (e : E) :
    (fibreNeighbors G e).card ≤ 2 :=
  fibreNeighbors_card_le_two G (twoLabel_leftDegree_le_two G A B hdeg) hright e

end BachThesisLean
