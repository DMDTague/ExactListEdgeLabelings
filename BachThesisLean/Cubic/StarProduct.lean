import BachThesisLean.Cubic.PortMaskCharacterization

namespace BachThesisLean
namespace BipartiteMultigraph

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-!
# Star products of cubic bipartite multigraphs

This is the edge-copy construction used in manuscript Proposition
`prop:star-port-criterion`. A right root of `A` and a left root of `B` are
deleted. Internal edge copies survive as subtypes, while the three deleted
port pairs are replaced by three new bridge edge copies indexed by `Fin 3`.
The permutation acts on the `B` port index.
-/

/-- Left shore of the star product: every `A`-left vertex survives, while the
chosen `B`-left root is deleted. -/
abbrev StarLeft (XA : Type uA) (XB : Type uB) (ell : XB) :=
  XA ⊕ {x : XB // x ≠ ell}

/-- Right shore of the star product: the chosen `A`-right root is deleted,
while every `B`-right vertex survives. -/
abbrev StarRight (YA : Type vA) (YB : Type vB) (r : YA) :=
  {y : YA // y ≠ r} ⊕ YB

/-- Edge copies of the star product. The first two summands are surviving
internal copies; the final `Fin 3` summand is the new three-edge join. -/
abbrev StarEdge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) :=
  {e : EA // A.right e ≠ r} ⊕ ({e : EB // B.left e ≠ ell} ⊕ Fin 3)

/-- The manuscript star product `A ⋆_σ B`, retaining actual edge copies. -/
def starProduct
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB)
    (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) :
    BipartiteMultigraph (StarLeft XA XB ell) (StarRight YA YB r)
      (StarEdge A B r ell) where
  left
    | .inl e => .inl (A.left e.1)
    | .inr (.inl e) => .inr ⟨B.left e.1, e.2⟩
    | .inr (.inr i) => .inl (A.left (p i).1)
  right
    | .inl e => .inl ⟨A.right e.1, e.2⟩
    | .inr (.inl e) => .inr (B.right e.1)
    | .inr (.inr i) => .inr (B.right (q (σ i)).1)

@[simp] theorem starProduct_left_aInternal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : {e : EA // A.right e ≠ r}) :
    (A.starProduct B r ell p q σ).left (.inl e) = .inl (A.left e.1) := rfl

@[simp] theorem starProduct_right_aInternal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : {e : EA // A.right e ≠ r}) :
    (A.starProduct B r ell p q σ).right (.inl e) = .inl ⟨A.right e.1, e.2⟩ := rfl

@[simp] theorem starProduct_left_bInternal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : {e : EB // B.left e ≠ ell}) :
    (A.starProduct B r ell p q σ).left (.inr (.inl e)) =
      .inr ⟨B.left e.1, e.2⟩ := rfl

@[simp] theorem starProduct_right_bInternal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (e : {e : EB // B.left e ≠ ell}) :
    (A.starProduct B r ell p q σ).right (.inr (.inl e)) = .inr (B.right e.1) := rfl

@[simp] theorem starProduct_left_bridge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) :
    (A.starProduct B r ell p q σ).left (.inr (.inr i)) =
      .inl (A.left (p i).1) := rfl

@[simp] theorem starProduct_right_bridge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) :
    (A.starProduct B r ell p q σ).right (.inr (.inr i)) =
      .inr (B.right (q (σ i)).1) := rfl

/-- An `A` port really has the selected right root as its right endpoint. -/
@[simp] theorem port_right_eq
    (A : BipartiteMultigraph XA YA EA) (r : YA)
    (p : A.PortEnumeration (.inr r)) (i : Fin 3) :
    A.right (p i).1 = r := by
  have h := (mem_incidentEdges A (.inr r) (p i).1).1 (p i).property
  change A.right (p i).1 = r at h
  exact h

/-- A `B` port really has the selected left root as its left endpoint. -/
@[simp] theorem port_left_eq
    (B : BipartiteMultigraph XB YB EB) (ell : XB)
    (q : B.PortEnumeration (.inl ell)) (i : Fin 3) :
    B.left (q i).1 = ell := by
  have h := (mem_incidentEdges B (.inl ell) (q i).1).1 (q i).property
  change B.left (q i).1 = ell at h
  exact h

end BipartiteMultigraph
end BachThesisLean
