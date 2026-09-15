import BachThesisLean.Cubic.TightCutContractionDegrees

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Cubicity of right-oriented tight-cut contractions

Away from the contraction root, incidence is inherited bijectively from the
original graph.  The hypothesis `cutFromLeft W = ∅` is exactly what ensures
that an edge at a surviving left-inside/right-outside vertex cannot disappear
from the chosen contraction model.  The contraction root degree was identified
with `cutFromRight W` in `TightCutContractionDegrees`.
-/

/-- Incidence at an inside left vertex is preserved by `G / Wᶜ`. -/
theorem contractComplement_leftIncident_inside_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hOrient : G.cutFromLeft W = ∅)
    (x : {x : X // (Sum.inl x : X ⊕ Y) ∈ W}) :
    ((G.contractComplement W).leftIncident (.inl x)).card =
      (G.leftIncident x.1).card := by
  classical
  let F : ∀ e, e ∈ G.leftIncident x.1 → ContractComplementEdge G W :=
    fun e he => ⟨e, by
      have hleft : G.left e = x.1 := (G.mem_leftIncident x.1 e).1 he
      have hx : (Sum.inl (G.left e) : X ⊕ Y) ∈ W := by
        simpa [hleft] using x.2
      by_contra hout
      have hcut : e ∈ G.cutFromLeft W :=
        (G.mem_cutFromLeft W e).2 ⟨hx, hout⟩
      rw [hOrient] at hcut
      simpa using hcut⟩
  symm
  refine Finset.card_bij
    (s := G.leftIncident x.1)
    (t := (G.contractComplement W).leftIncident (.inl x))
    F ?_ ?_ ?_
  · intro e he
    have hleft : G.left e = x.1 := (G.mem_leftIncident x.1 e).1 he
    have hx : (Sum.inl (G.left e) : X ⊕ Y) ∈ W := by
      simpa [hleft] using x.2
    apply ((G.contractComplement W).mem_leftIncident (.inl x) (F e he)).2
    rw [G.contractComplement_left_of_mem W (F e he) hx]
    apply congrArg Sum.inl
    exact Subtype.ext hleft
  · intro e he f hf hef
    exact congrArg Subtype.val hef
  · intro se hse
    have hleftStar := ((G.contractComplement W).mem_leftIncident (.inl x) se).1 hse
    have hin : (Sum.inl (G.left se.1) : X ⊕ Y) ∈ W := by
      by_contra hout
      rw [G.contractComplement_left_of_not_mem W se hout] at hleftStar
      simp [contractComplementRoot] at hleftStar
    have hleftStar' := hleftStar
    rw [G.contractComplement_left_of_mem W se hin] at hleftStar'
    have hsub :
        (⟨G.left se.1, hin⟩ : {z : X // (Sum.inl z : X ⊕ Y) ∈ W}) = x :=
      Sum.inl.inj hleftStar'
    have hleft : G.left se.1 = x.1 := congrArg Subtype.val hsub
    have he : se.1 ∈ G.leftIncident x.1 := (G.mem_leftIncident x.1 se.1).2 hleft
    refine ⟨se.1, he, ?_⟩
    apply Subtype.ext
    rfl

/-- Incidence at an inside right vertex is preserved by `G / Wᶜ`. -/
theorem contractComplement_rightIncident_inside_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (y : {y : Y // (Sum.inr y : X ⊕ Y) ∈ W}) :
    ((G.contractComplement W).rightIncident y).card =
      (G.rightIncident y.1).card := by
  classical
  let F : ∀ e, e ∈ G.rightIncident y.1 → ContractComplementEdge G W :=
    fun e he => ⟨e, by
      have hright : G.right e = y.1 := (G.mem_rightIncident y.1 e).1 he
      simpa [hright] using y.2⟩
  symm
  refine Finset.card_bij
    (s := G.rightIncident y.1)
    (t := (G.contractComplement W).rightIncident y)
    F ?_ ?_ ?_
  · intro e he
    have hright : G.right e = y.1 := (G.mem_rightIncident y.1 e).1 he
    apply ((G.contractComplement W).mem_rightIncident y (F e he)).2
    rw [G.contractComplement_right W (F e he)]
    exact Subtype.ext hright
  · intro e he f hf hef
    exact congrArg Subtype.val hef
  · intro se hse
    have hrightStar := ((G.contractComplement W).mem_rightIncident y se).1 hse
    rw [G.contractComplement_right W se] at hrightStar
    have hright : G.right se.1 = y.1 := congrArg Subtype.val hrightStar
    have he : se.1 ∈ G.rightIncident y.1 :=
      (G.mem_rightIncident y.1 se.1).2 hright
    refine ⟨se.1, he, ?_⟩
    apply Subtype.ext
    rfl

/-- Incidence at an outside left vertex is preserved by `G / W`. -/
theorem contractSet_leftIncident_outside_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (x : {x : X // (Sum.inl x : X ⊕ Y) ∉ W}) :
    ((G.contractSet W).leftIncident x).card = (G.leftIncident x.1).card := by
  classical
  let F : ∀ e, e ∈ G.leftIncident x.1 → ContractSetEdge G W :=
    fun e he => ⟨e, by
      have hleft : G.left e = x.1 := (G.mem_leftIncident x.1 e).1 he
      simpa [hleft] using x.2⟩
  symm
  refine Finset.card_bij
    (s := G.leftIncident x.1)
    (t := (G.contractSet W).leftIncident x)
    F ?_ ?_ ?_
  · intro e he
    have hleft : G.left e = x.1 := (G.mem_leftIncident x.1 e).1 he
    apply ((G.contractSet W).mem_leftIncident x (F e he)).2
    rw [G.contractSet_left W (F e he)]
    exact Subtype.ext hleft
  · intro e he f hf hef
    exact congrArg Subtype.val hef
  · intro se hse
    have hleftStar := ((G.contractSet W).mem_leftIncident x se).1 hse
    rw [G.contractSet_left W se] at hleftStar
    have hleft : G.left se.1 = x.1 := congrArg Subtype.val hleftStar
    have he : se.1 ∈ G.leftIncident x.1 := (G.mem_leftIncident x.1 se.1).2 hleft
    refine ⟨se.1, he, ?_⟩
    apply Subtype.ext
    rfl

/-- Incidence at an outside right vertex is preserved by `G / W`. -/
theorem contractSet_rightIncident_outside_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hOrient : G.cutFromLeft W = ∅)
    (y : {y : Y // (Sum.inr y : X ⊕ Y) ∉ W}) :
    ((G.contractSet W).rightIncident (.inl y)).card =
      (G.rightIncident y.1).card := by
  classical
  let F : ∀ e, e ∈ G.rightIncident y.1 → ContractSetEdge G W :=
    fun e he => ⟨e, by
      have hright : G.right e = y.1 := (G.mem_rightIncident y.1 e).1 he
      have hy : (Sum.inr (G.right e) : X ⊕ Y) ∉ W := by
        simpa [hright] using y.2
      by_contra hin
      have hcut : e ∈ G.cutFromLeft W :=
        (G.mem_cutFromLeft W e).2 ⟨hin, hy⟩
      rw [hOrient] at hcut
      simpa using hcut⟩
  symm
  refine Finset.card_bij
    (s := G.rightIncident y.1)
    (t := (G.contractSet W).rightIncident (.inl y))
    F ?_ ?_ ?_
  · intro e he
    have hright : G.right e = y.1 := (G.mem_rightIncident y.1 e).1 he
    have hy : (Sum.inr (G.right e) : X ⊕ Y) ∉ W := by
      simpa [hright] using y.2
    apply ((G.contractSet W).mem_rightIncident (.inl y) (F e he)).2
    rw [G.contractSet_right_of_not_mem W (F e he) hy]
    apply congrArg Sum.inl
    exact Subtype.ext hright
  · intro e he f hf hef
    exact congrArg Subtype.val hef
  · intro se hse
    have hrightStar := ((G.contractSet W).mem_rightIncident (.inl y) se).1 hse
    have hout : (Sum.inr (G.right se.1) : X ⊕ Y) ∉ W := by
      intro hin
      rw [G.contractSet_right_of_mem W se hin] at hrightStar
      simp [contractSetRoot] at hrightStar
    have hrightStar' := hrightStar
    rw [G.contractSet_right_of_not_mem W se hout] at hrightStar'
    have hsub :
        (⟨G.right se.1, hout⟩ : {z : Y // (Sum.inr z : X ⊕ Y) ∉ W}) = y :=
      Sum.inl.inj hrightStar'
    have hright : G.right se.1 = y.1 := congrArg Subtype.val hsub
    have he : se.1 ∈ G.rightIncident y.1 :=
      (G.mem_rightIncident y.1 se.1).2 hright
    refine ⟨se.1, he, ?_⟩
    apply Subtype.ext
    rfl

/-- In the manuscript's right-oriented case, a three-edge cut in a cubic graph
produces a cubic `G / Wᶜ`. -/
theorem contractComplement_isCubic_of_right_oriented
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hG : G.IsCubic) (hOrient : G.cutFromLeft W = ∅)
    (hCut : (G.cutFromRight W).card = 3) :
    (G.contractComplement W).IsCubic := by
  exact G.contractComplement_isCubic W hG hOrient hCut

/-- In the same orientation, the opposite contraction `G / W` is cubic. -/
theorem contractSet_isCubic_of_right_oriented
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hG : G.IsCubic) (hOrient : G.cutFromLeft W = ∅)
    (hCut : (G.cutFromRight W).card = 3) :
    (G.contractSet W).IsCubic := by
  exact G.contractSet_isCubic W hG hOrient hCut

/-- Connected cubic tight cuts in the right-oriented branch therefore have
cubic contractions on both sides. -/
theorem IsTightCut.right_oriented_contractions_cubic
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hOrient : G.cutFromLeft W = ∅) :
    (G.contractComplement W).IsCubic ∧ (G.contractSet W).IsCubic := by
  have hEdge : (G.edgeCut W).card = 3 :=
    hT.edgeCut_card_eq_three_of_connected_cubic hconn hG
  have hCut : (G.cutFromRight W).card = 3 := by
    rw [G.edgeCut_eq_oriented_union W, hOrient] at hEdge
    simpa using hEdge
  exact ⟨G.contractComplement_isCubic_of_right_oriented W hG hOrient hCut,
    G.contractSet_isCubic_of_right_oriented W hG hOrient hCut⟩

end BipartiteMultigraph
end BachThesisLean
