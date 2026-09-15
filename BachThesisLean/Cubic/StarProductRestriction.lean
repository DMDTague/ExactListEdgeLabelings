import BachThesisLean.Cubic.StarProductBridge

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
# Restricting a star-product matching to its factors

The edge maps `starAEdge` and `starBEdge` replace a source root edge by the
corresponding bridge.  Pulling a star edge set back along those maps restores
edge sets on the original factors.
-/

noncomputable def starRestrictedA
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (P : Finset (StarEdge A B r ell)) : Finset EA := by
  classical
  exact Finset.univ.filter (fun e => A.starAEdge B r ell p e ∈ P)

noncomputable def starRestrictedB
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell)) : Finset EB := by
  classical
  exact Finset.univ.filter (fun e => A.starBEdge B r ell q σ e ∈ P)

@[simp] theorem mem_starRestrictedA
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (P : Finset (StarEdge A B r ell)) (e : EA) :
    e ∈ A.starRestrictedA B r ell p P ↔ A.starAEdge B r ell p e ∈ P := by
  classical
  simp [starRestrictedA]

@[simp] theorem mem_starRestrictedB
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell)) (e : EB) :
    e ∈ A.starRestrictedB B r ell q σ P ↔ A.starBEdge B r ell q σ e ∈ P := by
  classical
  simp [starRestrictedB]

@[simp] theorem starAEdge_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r)) (i : Fin 3) :
    A.starAEdge B r ell p (p i).1 =
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) := by
  classical
  have hroot : A.right (p i).1 = r := A.port_right_eq r p i
  simp [starAEdge, hroot]

@[simp] theorem starBEdge_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    A.starBEdge B r ell q σ (q (σ i)).1 =
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) := by
  classical
  have hroot : B.left (q (σ i)).1 = ell := B.port_left_eq ell q (σ i)
  simp [starBEdge, hroot]

@[simp] theorem mem_starRestrictedA_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (P : Finset (StarEdge A B r ell)) (i : Fin 3) :
    (p i).1 ∈ A.starRestrictedA B r ell p P ↔
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P := by
  simp

@[simp] theorem mem_starRestrictedB_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (P : Finset (StarEdge A B r ell)) (i : Fin 3) :
    (q (σ i)).1 ∈ A.starRestrictedB B r ell q σ P ↔
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P := by
  simp

@[simp] theorem mem_starRestrictedA_internal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (P : Finset (StarEdge A B r ell))
    (e : {e : EA // A.right e ≠ r}) :
    e.1 ∈ A.starRestrictedA B r ell p P ↔
      (Sum.inl e : StarEdge A B r ell) ∈ P := by
  simp [starAEdge, e.2]

@[simp] theorem mem_starRestrictedB_internal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (P : Finset (StarEdge A B r ell))
    (e : {e : EB // B.left e ≠ ell}) :
    e.1 ∈ A.starRestrictedB B r ell q σ P ↔
      (Sum.inr (Sum.inl e) : StarEdge A B r ell) ∈ P := by
  simp [starBEdge, e.2]

end BipartiteMultigraph
end BachThesisLean
