import BachThesisLean.Cubic.TightCutContraction

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Degrees in the explicit tight-cut contractions

The equivalences below forget only the subtype witnesses. They preserve each
individual edge copy, including parallel copies, and identify the incidence
at either contraction root with the right-oriented boundary copies.
-/

/-- With no left-oriented boundary, every edge from a left vertex in `W`
ends at a right vertex in `W`. -/
theorem right_mem_of_left_mem_of_cutFromLeft_eq_empty
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) {e : E}
    (he : (Sum.inl (G.left e) : X ⊕ Y) ∈ W) :
    (Sum.inr (G.right e) : X ⊕ Y) ∈ W := by
  by_contra hn
  have hc := (G.mem_cutFromLeft W e).2 ⟨he, hn⟩
  simp [hW] at hc

/-- The contrapositive endpoint form of the orientation condition. -/
theorem left_not_mem_of_right_not_mem_of_cutFromLeft_eq_empty
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) {e : E}
    (he : (Sum.inr (G.right e) : X ⊕ Y) ∉ W) :
    (Sum.inl (G.left e) : X ⊕ Y) ∉ W := by
  intro hl
  exact he (G.right_mem_of_left_mem_of_cutFromLeft_eq_empty W hW hl)

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] in
@[simp] theorem contractComplement_left_eq_inl_iff
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractComplementEdge G W) (x : {x : X // (Sum.inl x : X ⊕ Y) ∈ W}) :
    (G.contractComplement W).left e = .inl x ↔ G.left e.1 = x.1 := by
  by_cases h : (Sum.inl (G.left e.1) : X ⊕ Y) ∈ W
  · simp [contractComplement, h, Subtype.ext_iff]
  · have hn : G.left e.1 ≠ x.1 := by
      intro he
      exact h (he ▸ x.2)
    simp [contractComplement, h, hn]

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] in
@[simp] theorem contractComplement_left_eq_root_iff
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractComplementEdge G W) :
    (G.contractComplement W).left e = contractComplementRoot W ↔
      (Sum.inl (G.left e.1) : X ⊕ Y) ∉ W := by
  simp [contractComplement, contractComplementRoot]

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] in
@[simp] theorem contractSet_right_eq_inl_iff
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractSetEdge G W) (y : {y : Y // (Sum.inr y : X ⊕ Y) ∉ W}) :
    (G.contractSet W).right e = .inl y ↔ G.right e.1 = y.1 := by
  by_cases h : (Sum.inr (G.right e.1) : X ⊕ Y) ∈ W
  · have hn : G.right e.1 ≠ y.1 := by
      intro he
      exact y.2 (he ▸ h)
    simp [contractSet, h, hn]
  · simp [contractSet, h, Subtype.ext_iff]

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] in
@[simp] theorem contractSet_right_eq_root_iff
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractSetEdge G W) :
    (G.contractSet W).right e = contractSetRoot W ↔
      (Sum.inr (G.right e.1) : X ⊕ Y) ∈ W := by
  simp [contractSet, contractSetRoot]

/-- Incidence at an uncontracted left vertex preserves the original copies. -/
def contractComplementLeftIncidentEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) (x : {x : X // (Sum.inl x : X ⊕ Y) ∈ W}) :
    {e : ContractComplementEdge G W // e ∈ (G.contractComplement W).incidentEdges (.inl (.inl x))} ≃
      {e : E // e ∈ G.incidentEdges (.inl x.1)} := by
  refine
      { toFun := fun e => ⟨e.1.1, ?_⟩
        invFun := fun e => ⟨⟨e.1, ?_⟩, ?_⟩
        left_inv := fun e => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun e => by apply Subtype.ext; rfl }
  · simpa [Incident] using e.2
  · apply G.right_mem_of_left_mem_of_cutFromLeft_eq_empty W hW
    have he : G.left e.1 = x.1 := by simpa [Incident] using e.2
    simpa only [he] using x.2
  · simpa [Incident] using e.2

/-- Incidence at an uncontracted right vertex preserves the original copies. -/
def contractComplementRightIncidentEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (y : ContractComplementRight X Y W) :
    {e : ContractComplementEdge G W // e ∈ (G.contractComplement W).incidentEdges (.inr y)} ≃
      {e : E // e ∈ G.incidentEdges (.inr y.1)} where
  toFun e := ⟨e.1.1, by simpa [Incident, Subtype.ext_iff] using e.2⟩
  invFun e := ⟨⟨e.1, by
    have he : G.right e.1 = y.1 := by simpa [Incident] using e.2
    simpa only [he] using y.2⟩, by simpa [Incident, Subtype.ext_iff] using e.2⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Incidence at the new left root is exactly the right-oriented cut copies. -/
noncomputable def contractComplementRootIncidentEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    {e : ContractComplementEdge G W //
      e ∈ (G.contractComplement W).incidentEdges (.inl (contractComplementRoot W))} ≃
      {e : E // e ∈ G.cutFromRight W} where
  toFun e := ⟨e.1.1, (G.mem_cutFromRight W e.1.1).2
    ⟨by simpa [Incident] using e.2, e.1.2⟩⟩
  invFun e := ⟨⟨e.1, ((G.mem_cutFromRight W e.1).1 e.2).2⟩,
    by simpa [Incident] using ((G.mem_cutFromRight W e.1).1 e.2).1⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Incidence at an uncontracted left vertex of `G / W` is unchanged. -/
def contractSetLeftIncidentEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (x : ContractSetLeft X Y W) :
    {e : ContractSetEdge G W // e ∈ (G.contractSet W).incidentEdges (.inl x)} ≃
      {e : E // e ∈ G.incidentEdges (.inl x.1)} where
  toFun e := ⟨e.1.1, by simpa [Incident, Subtype.ext_iff] using e.2⟩
  invFun e := ⟨⟨e.1, by
    have he : G.left e.1 = x.1 := by simpa [Incident] using e.2
    simpa only [he] using x.2⟩, by simpa [Incident, Subtype.ext_iff] using e.2⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Incidence at an uncontracted right vertex of `G / W` is unchanged. -/
def contractSetRightIncidentEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) (y : {y : Y // (Sum.inr y : X ⊕ Y) ∉ W}) :
    {e : ContractSetEdge G W // e ∈ (G.contractSet W).incidentEdges (.inr (.inl y))} ≃
      {e : E // e ∈ G.incidentEdges (.inr y.1)} := by
  refine
    { toFun := fun e => ⟨e.1.1, ?_⟩
      invFun := fun e => ⟨⟨e.1, ?_⟩, ?_⟩
      left_inv := fun e => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun e => by apply Subtype.ext; rfl }
  · simpa [Incident] using e.2
  · apply G.left_not_mem_of_right_not_mem_of_cutFromLeft_eq_empty W hW
    have he : G.right e.1 = y.1 := by simpa [Incident] using e.2
    simpa only [he] using y.2
  · simpa [Incident] using e.2

/-- Incidence at the new right root is exactly the same individual cut copies. -/
noncomputable def contractSetRootIncidentEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    {e : ContractSetEdge G W //
      e ∈ (G.contractSet W).incidentEdges (.inr (contractSetRoot W))} ≃
      {e : E // e ∈ G.cutFromRight W} where
  toFun e := ⟨e.1.1, (G.mem_cutFromRight W e.1.1).2
    ⟨e.1.2, by simpa [Incident] using e.2⟩⟩
  invFun e := ⟨⟨e.1, ((G.mem_cutFromRight W e.1).1 e.2).1⟩,
    by simpa [Incident] using ((G.mem_cutFromRight W e.1).1 e.2).2⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

theorem contractComplement_left_incidentEdges_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) (x : {x : X // (Sum.inl x : X ⊕ Y) ∈ W}) :
    ((G.contractComplement W).incidentEdges (.inl (.inl x))).card =
      (G.incidentEdges (.inl x.1)).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (G.contractComplementLeftIncidentEquiv W hW x)

theorem contractComplement_right_incidentEdges_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (y : ContractComplementRight X Y W) :
    ((G.contractComplement W).incidentEdges (.inr y)).card =
      (G.incidentEdges (.inr y.1)).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (G.contractComplementRightIncidentEquiv W y)

theorem contractComplement_root_incidentEdges_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    ((G.contractComplement W).incidentEdges (.inl (contractComplementRoot W))).card =
      (G.cutFromRight W).card := by
  classical
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (G.contractComplementRootIncidentEquiv W)

theorem contractSet_left_incidentEdges_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (x : ContractSetLeft X Y W) :
    ((G.contractSet W).incidentEdges (.inl x)).card =
      (G.incidentEdges (.inl x.1)).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (G.contractSetLeftIncidentEquiv W x)

theorem contractSet_right_incidentEdges_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) (y : {y : Y // (Sum.inr y : X ⊕ Y) ∉ W}) :
    ((G.contractSet W).incidentEdges (.inr (.inl y))).card =
      (G.incidentEdges (.inr y.1)).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (G.contractSetRightIncidentEquiv W hW y)

theorem contractSet_root_incidentEdges_card
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) :
    ((G.contractSet W).incidentEdges (.inr (contractSetRoot W))).card =
      (G.cutFromRight W).card := by
  classical
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (G.contractSetRootIncidentEquiv W)

/-- Contracting the complement preserves cubicity for a right-oriented
three-copy boundary. No simplicity or edge-connectivity hypothesis is used. -/
theorem contractComplement_isCubic
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hG : G.IsCubic) (hW : G.cutFromLeft W = ∅)
    (hcut : (G.cutFromRight W).card = 3) : (G.contractComplement W).IsCubic := by
  intro v
  rcases v with (x | u) | y
  · rw [G.contractComplement_left_incidentEdges_card W hW x]
    exact hG (.inl x.1)
  · cases u
    exact (G.contractComplement_root_incidentEdges_card W).trans hcut
  · rw [G.contractComplement_right_incidentEdges_card W y]
    exact hG (.inr y.1)

/-- Contracting `W` preserves cubicity under the same oriented three-copy
boundary hypotheses. -/
theorem contractSet_isCubic
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hG : G.IsCubic) (hW : G.cutFromLeft W = ∅)
    (hcut : (G.cutFromRight W).card = 3) : (G.contractSet W).IsCubic := by
  intro v
  rcases v with x | (y | u)
  · rw [G.contractSet_left_incidentEdges_card W x]
    exact hG (.inl x.1)
  · rw [G.contractSet_right_incidentEdges_card W hW y]
    exact hG (.inr y.1)
  · cases u
    exact (G.contractSet_root_incidentEdges_card W).trans hcut

end BipartiteMultigraph
end BachThesisLean
