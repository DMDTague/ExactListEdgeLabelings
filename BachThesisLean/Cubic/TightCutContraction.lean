import BachThesisLean.Cubic.TightCutThree

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Explicit tight-cut contractions

Assume the manuscript orientation in which every boundary edge leaves `W`
from its right shore.  The two contraction graphs can then be represented
without quotient types.  Contracting the complement adds one new left vertex;
contracting `W` adds one new right vertex.  The edge types are subtypes of the
original edge-copy type, so parallel cut edges remain distinct automatically.

The definitions make sense for every `W`; the orientation hypothesis is only
needed later when proving cubicity and the matching correspondence.
-/

/-- Left shore of `G / Wᶜ`: left vertices in `W` plus the contraction vertex. -/
abbrev ContractComplementLeft (X : Type u) (Y : Type v)
    (W : Finset (X ⊕ Y)) :=
  {x : X // (Sum.inl x : X ⊕ Y) ∈ W} ⊕ Unit

/-- Right shore of `G / Wᶜ`: precisely the right vertices in `W`. -/
abbrev ContractComplementRight (X : Type u) (Y : Type v)
    (W : Finset (X ⊕ Y)) :=
  {y : Y // (Sum.inr y : X ⊕ Y) ∈ W}

/-- Edge copies of `G / Wᶜ`: exactly the copies whose right endpoint lies in
`W`.  Under the manuscript orientation these are the internal copies and the
three cut copies. -/
abbrev ContractComplementEdge (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) :=
  {e : E // (Sum.inr (G.right e) : X ⊕ Y) ∈ W}

/-- The contraction vertex of `G / Wᶜ`. -/
def contractComplementRoot (W : Finset (X ⊕ Y)) :
    ContractComplementLeft X Y W := .inr ()

/-- Explicit edge-copy model of `G / Wᶜ`. -/
def contractComplement (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) :
    BipartiteMultigraph (ContractComplementLeft X Y W)
      (ContractComplementRight X Y W) (ContractComplementEdge G W) where
  left e :=
    if h : (Sum.inl (G.left e.1) : X ⊕ Y) ∈ W then
      .inl ⟨G.left e.1, h⟩
    else
      .inr ()
  right e := ⟨G.right e.1, e.2⟩

@[simp] theorem contractComplement_right
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractComplementEdge G W) :
    (G.contractComplement W).right e = ⟨G.right e.1, e.2⟩ := rfl

@[simp] theorem contractComplement_left_of_mem
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractComplementEdge G W)
    (h : (Sum.inl (G.left e.1) : X ⊕ Y) ∈ W) :
    (G.contractComplement W).left e = .inl ⟨G.left e.1, h⟩ := by
  simp [contractComplement, h]

@[simp] theorem contractComplement_left_of_not_mem
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractComplementEdge G W)
    (h : (Sum.inl (G.left e.1) : X ⊕ Y) ∉ W) :
    (G.contractComplement W).left e = contractComplementRoot W := by
  simp [contractComplement, contractComplementRoot, h]

/-- Left shore of `G / W`: precisely the left vertices outside `W`. -/
abbrev ContractSetLeft (X : Type u) (Y : Type v)
    (W : Finset (X ⊕ Y)) :=
  {x : X // (Sum.inl x : X ⊕ Y) ∉ W}

/-- Right shore of `G / W`: right vertices outside `W` plus the contraction
vertex. -/
abbrev ContractSetRight (X : Type u) (Y : Type v)
    (W : Finset (X ⊕ Y)) :=
  {y : Y // (Sum.inr y : X ⊕ Y) ∉ W} ⊕ Unit

/-- Edge copies of `G / W`: exactly the copies whose left endpoint lies
outside `W`. -/
abbrev ContractSetEdge (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) :=
  {e : E // (Sum.inl (G.left e) : X ⊕ Y) ∉ W}

/-- The contraction vertex of `G / W`. -/
def contractSetRoot (W : Finset (X ⊕ Y)) : ContractSetRight X Y W := .inr ()

/-- Explicit edge-copy model of `G / W`. -/
def contractSet (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) :
    BipartiteMultigraph (ContractSetLeft X Y W)
      (ContractSetRight X Y W) (ContractSetEdge G W) where
  left e := ⟨G.left e.1, e.2⟩
  right e :=
    if h : (Sum.inr (G.right e.1) : X ⊕ Y) ∈ W then
      .inr ()
    else
      .inl ⟨G.right e.1, h⟩

@[simp] theorem contractSet_left
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractSetEdge G W) :
    (G.contractSet W).left e = ⟨G.left e.1, e.2⟩ := rfl

@[simp] theorem contractSet_right_of_mem
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractSetEdge G W)
    (h : (Sum.inr (G.right e.1) : X ⊕ Y) ∈ W) :
    (G.contractSet W).right e = contractSetRoot W := by
  simp [contractSet, contractSetRoot, h]

@[simp] theorem contractSet_right_of_not_mem
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (e : ContractSetEdge G W)
    (h : (Sum.inr (G.right e.1) : X ⊕ Y) ∉ W) :
    (G.contractSet W).right e = .inl ⟨G.right e.1, h⟩ := by
  simp [contractSet, h]

/-- Every right-oriented cut edge appears in both explicit contractions. -/
theorem cutFromRight_mem_contractComplementEdge
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    {e : E} (he : e ∈ G.cutFromRight W) :
    (Sum.inr (G.right e) : X ⊕ Y) ∈ W :=
  ((G.mem_cutFromRight W e).1 he).2

/-- The same boundary edge also appears in `G / W`. -/
theorem cutFromRight_mem_contractSetEdge
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    {e : E} (he : e ∈ G.cutFromRight W) :
    (Sum.inl (G.left e) : X ⊕ Y) ∉ W :=
  ((G.mem_cutFromRight W e).1 he).1

end BipartiteMultigraph
end BachThesisLean
