import BachThesisLean.Cubic.TightCutContraction
import BachThesisLean.Cubic.StarProduct
import BachThesisLean.Cubic.Isomorphism

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

/-- Removing the added contraction vertex recovers the retained vertex type. -/
def sumUnitNonrootEquiv (α : Type u) : {a : α ⊕ Unit // a ≠ Sum.inr ()} ≃ α where
  toFun
    | ⟨.inl a, _⟩ => a
    | ⟨.inr (), h⟩ => False.elim (h rfl)
  invFun a := ⟨.inl a, Sum.inl_ne_inr⟩
  left_inv a := by
    rcases a with ⟨a | ⟨⟩, h⟩
    · rfl
    · exact (h rfl).elim
  right_inv _ := rfl

/-- The outside and inside subtypes partition the original type. -/
def cutPartitionEquiv {α : Type u} (P : α → Prop) [DecidablePred P] :
    {a // ¬ P a} ⊕ {a // P a} ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : P a then .inr ⟨a, h⟩ else .inl ⟨a, h⟩
  left_inv a := by
    rcases a with a | a <;> simp [a.property]
  right_inv a := by
    by_cases h : P a <;> simp [h]

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- All original edge copies are retained or replaced by a cut port in the star
product of the two contractions. The same enumeration labels both ends. -/
def contractSetPorts
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W}) :
    (G.contractSet W).PortEnumeration (.inr (contractSetRoot W)) where
  toFun i := ⟨⟨(c i).val, ((G.mem_cutFromRight W _).mp (c i).property).1⟩, by
    simp only [mem_incidentEdges, Incident]
    exact G.contractSet_right_of_mem W _
      (((G.mem_cutFromRight W _).mp (c i).property).2)⟩
  invFun e := c.symm ⟨e.val.val, (G.mem_cutFromRight W _).mpr ⟨e.val.property, by
    have h := (mem_incidentEdges _ _ _).mp e.property
    change (G.contractSet W).right e.val = contractSetRoot W at h
    by_contra hn
    simp [contractSet, contractSetRoot, hn] at h⟩⟩
  left_inv i := by simp
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- Complementary contraction ports enumerate the identical boundary copies. -/
def contractComplementPorts
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W}) :
    (G.contractComplement W).PortEnumeration (.inl (contractComplementRoot W)) where
  toFun i := ⟨⟨(c i).val, ((G.mem_cutFromRight W _).mp (c i).property).2⟩, by
    simp only [mem_incidentEdges, Incident]
    exact G.contractComplement_left_of_not_mem W _
      (((G.mem_cutFromRight W _).mp (c i).property).1)⟩
  invFun e := c.symm ⟨e.val.val, (G.mem_cutFromRight W _).mpr ⟨by
    have h := (mem_incidentEdges _ _ _).mp e.property
    change (G.contractComplement W).left e.val = contractComplementRoot W at h
    intro hm
    simp [contractComplement, contractComplementRoot, hm] at h, e.val.property⟩⟩
  left_inv i := by simp
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The canonical three-port reconstruction, before identifying its types. -/
def tightCutStarProduct
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W}) :=
  (G.contractSet W).starProduct (G.contractComplement W)
    (contractSetRoot W) (contractComplementRoot W)
    (G.contractSetPorts W c) (G.contractComplementPorts W c) (Equiv.refl _)

/-- Explicit left-shore relabelling after deleting the two contraction roots. -/
def tightCutLeftEquiv (W : Finset (X ⊕ Y)) :
    StarLeft (ContractSetLeft X Y W) (ContractComplementLeft X Y W)
      (contractComplementRoot W) ≃ X :=
  (Equiv.sumCongr (Equiv.refl _) (sumUnitNonrootEquiv _)).trans
    (cutPartitionEquiv (fun x => (Sum.inl x : X ⊕ Y) ∈ W))

/-- Explicit right-shore relabelling after deleting the contraction roots. -/
def tightCutRightEquiv (W : Finset (X ⊕ Y)) :
    StarRight (ContractSetRight X Y W) (ContractComplementRight X Y W)
      (contractSetRoot W) ≃ Y :=
  (Equiv.sumCongr (sumUnitNonrootEquiv _) (Equiv.refl _)).trans
    (cutPartitionEquiv (fun y => (Sum.inr y : X ⊕ Y) ∈ W))

/-- An internal edge in the outside contraction has its right endpoint outside. -/
theorem contractSet_internal_right_not_mem
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : {e : ContractSetEdge G W //
      (G.contractSet W).right e ≠ contractSetRoot W}) :
    (Sum.inr (G.right e.val.val) : X ⊕ Y) ∉ W := by
  intro h
  exact e.property (G.contractSet_right_of_mem W _ h)

/-- An internal edge in the inside contraction has its left endpoint inside. -/
theorem contractComplement_internal_left_mem
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : {e : ContractComplementEdge G W //
      (G.contractComplement W).left e ≠ contractComplementRoot W}) :
    (Sum.inl (G.left e.val.val) : X ⊕ Y) ∈ W := by
  by_contra h
  exact e.property (G.contractComplement_left_of_not_mem W _ h)

/-- Erase only the tags added by contraction and gluing; each bridge recovers
its own enumerated original cut copy. -/
def tightCutEdgeErase
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W}) :
    StarEdge (G.contractSet W) (G.contractComplement W)
      (contractSetRoot W) (contractComplementRoot W) → E
  | .inl e => e.val.val
  | .inr (.inl e) => e.val.val
  | .inr (.inr i) => (c i).val

/-- Reconstruct the three disjoint edge-copy classes explicitly. -/
def tightCutEdgeInsert
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (hO : G.cutFromLeft W = ∅) (e : E) :
    StarEdge (G.contractSet W) (G.contractComplement W)
      (contractSetRoot W) (contractComplementRoot W) :=
  if hR : (Sum.inr (G.right e) : X ⊕ Y) ∈ W then
    if hL : (Sum.inl (G.left e) : X ⊕ Y) ∈ W then
      .inr (.inl ⟨⟨e, hR⟩, by
        simp [contractComplement, contractComplementRoot, hL]⟩)
    else
      .inr (.inr (c.symm ⟨e, (G.mem_cutFromRight W e).mpr ⟨hL, hR⟩⟩))
  else
    .inl ⟨⟨e, by
      intro hL
      have he := (G.mem_cutFromLeft W e).mpr ⟨hL, hR⟩
      simp [hO] at he⟩, by
        simp [contractSet, contractSetRoot, hR]⟩

/-- Every inserted edge recovers precisely the original edge copy. -/
@[simp] theorem tightCutEdgeErase_insert
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (hO : G.cutFromLeft W = ∅) (e : E) :
    G.tightCutEdgeErase W c (G.tightCutEdgeInsert W c hO e) = e := by
  by_cases hR : (Sum.inr (G.right e) : X ⊕ Y) ∈ W
  · by_cases hL : (Sum.inl (G.left e) : X ⊕ Y) ∈ W <;>
      simp [tightCutEdgeInsert, tightCutEdgeErase, hR, hL]
  · simp [tightCutEdgeInsert, tightCutEdgeErase, hR]

/-- No edge copies are lost or merged by erasing the contraction tags. -/
@[simp] theorem tightCutEdgeInsert_erase
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (hO : G.cutFromLeft W = ∅)
    (e : StarEdge (G.contractSet W) (G.contractComplement W)
      (contractSetRoot W) (contractComplementRoot W)) :
    G.tightCutEdgeInsert W c hO (G.tightCutEdgeErase W c e) = e := by
  rcases e with e | e | i
  · have hR := G.contractSet_internal_right_not_mem W e
    simp [tightCutEdgeInsert, tightCutEdgeErase, hR]
  · have hR := e.val.property
    have hL := G.contractComplement_internal_left_mem W e
    simp [tightCutEdgeInsert, tightCutEdgeErase, hR, hL]
  · have h := (G.mem_cutFromRight W _).mp (c i).property
    simp [tightCutEdgeInsert, tightCutEdgeErase, h.1, h.2]

/-- An explicit equivalence of edge copies, including repeated boundary endpoints. -/
def tightCutEdgeEquiv
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (hO : G.cutFromLeft W = ∅) :
    StarEdge (G.contractSet W) (G.contractComplement W)
      (contractSetRoot W) (contractComplementRoot W) ≃ E where
  toFun := G.tightCutEdgeErase W c
  invFun := G.tightCutEdgeInsert W c hO
  left_inv := G.tightCutEdgeInsert_erase W c hO
  right_inv := G.tightCutEdgeErase_insert W c hO

/-- The original graph is exactly the star product of its two oriented
three-port contractions, up to explicit shore and edge-copy equivalences.
Tightness and cubicity are needed to obtain the orientation and three ports,
not for the reconstruction itself. -/
def tightCutReconstructionIso
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (c : Fin 3 ≃ {e // e ∈ G.cutFromRight W})
    (hO : G.cutFromLeft W = ∅) : GraphIso (G.tightCutStarProduct W c) G where
  leftEquiv := tightCutLeftEquiv W
  rightEquiv := tightCutRightEquiv W
  edgeEquiv := G.tightCutEdgeEquiv W c hO
  map_left e := by
    rcases e with e | e | i
    · rfl
    · have hL := G.contractComplement_internal_left_mem W e
      simp [tightCutEdgeEquiv, tightCutEdgeErase, tightCutStarProduct,
        tightCutLeftEquiv, cutPartitionEquiv, sumUnitNonrootEquiv,
        starProduct, contractComplement, hL]
      rfl
    · rfl
  map_right e := by
    rcases e with e | e | i
    · have hR := G.contractSet_internal_right_not_mem W e
      simp [tightCutEdgeEquiv, tightCutEdgeErase, tightCutStarProduct,
        tightCutRightEquiv, cutPartitionEquiv, sumUnitNonrootEquiv,
        starProduct, contractSet, hR]
      rfl
    · rfl
    · rfl

/-- Enumerate the three distinct boundary edge copies without choosing distinct
neighbouring vertices. -/
noncomputable def tightCutBoundaryEnumeration
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hthree : (G.cutFromRight W).card = 3) :
    Fin 3 ≃ {e // e ∈ G.cutFromRight W} :=
  (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans hthree)).symm

end BipartiteMultigraph
end BachThesisLean
