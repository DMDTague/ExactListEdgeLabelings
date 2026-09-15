import BachThesisLean.Cubic.StarProduct

namespace BachThesisLean
namespace BipartiteMultigraph

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-- Replace an `A` edge incident with the deleted right root by its bridge
copy; all other `A` edges survive as internal copies. -/
def starAEdge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (e : EA) : StarEdge A B r ell :=
  if h : A.right e = r then
    .inr (.inr (p.symm ⟨e, (mem_incidentEdges A (.inr r) e).2 (by
      simpa [Incident] using h)⟩))
  else
    .inl ⟨e, h⟩

/-- Recover the original `A` edge from an internal or bridge copy. -/
def starARecover
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r)) :
    StarEdge A B r ell → Option EA
  | .inl e => some e.1
  | .inr (.inl _) => none
  | .inr (.inr i) => some (p i).1

@[simp] theorem starARecover_starAEdge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r)) (e : EA) :
    A.starARecover B r ell p (A.starAEdge B r ell p e) = some e := by
  classical
  by_cases h : A.right e = r
  · simp [starAEdge, starARecover, h]
  · simp [starAEdge, starARecover, h]

theorem starAEdge_injective
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r)) :
    Function.Injective (A.starAEdge B r ell p) := by
  intro e f hef
  have h := congrArg (A.starARecover B r ell p) hef
  simpa using h

@[simp] theorem starAEdge_left
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3)) (e : EA) :
    (A.starProduct B r ell p q σ).left (A.starAEdge B r ell p e) =
      .inl (A.left e) := by
  classical
  by_cases h : A.right e = r
  · simp [starAEdge, h]
  · simp [starAEdge, h]

/-- Replace a `B` edge incident with the deleted left root by the bridge whose
index maps to its `B` port under `σ`; all other `B` edges survive internally. -/
def starBEdge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (e : EB) : StarEdge A B r ell :=
  if h : B.left e = ell then
    .inr (.inr (σ.symm (q.symm ⟨e, (mem_incidentEdges B (.inl ell) e).2 (by
      simpa [Incident] using h)⟩)))
  else
    .inr (.inl ⟨e, h⟩)

/-- Recover the original `B` edge from an internal or bridge copy. -/
def starBRecover
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) : StarEdge A B r ell → Option EB
  | .inl _ => none
  | .inr (.inl e) => some e.1
  | .inr (.inr i) => some (q (σ i)).1

@[simp] theorem starBRecover_starBEdge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (e : EB) :
    A.starBRecover B r ell q σ (A.starBEdge B r ell q σ e) = some e := by
  classical
  by_cases h : B.left e = ell
  · simp [starBEdge, starBRecover, h]
  · simp [starBEdge, starBRecover, h]

theorem starBEdge_injective
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (A.starBEdge B r ell q σ) := by
  intro e f hef
  have h := congrArg (A.starBRecover B r ell q σ) hef
  simpa using h

@[simp] theorem starBEdge_right
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3)) (e : EB) :
    (A.starProduct B r ell p q σ).right (A.starBEdge B r ell q σ e) =
      .inr (B.right e) := by
  classical
  by_cases h : B.left e = ell
  · simp [starBEdge, h]
  · simp [starBEdge, h]

/-- Degrees at surviving `A`-left vertices are unchanged. -/
theorem starProduct_leftIncident_a
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3)) (x : XA) :
    ((A.starProduct B r ell p q σ).leftIncident (.inl x)).card =
      (A.leftIncident x).card := by
  classical
  symm
  refine Finset.card_nbij (A.starAEdge B r ell p) ?_ ?_ ?_
  · intro e he
    apply ((A.starProduct B r ell p q σ).mem_leftIncident (.inl x)
      (A.starAEdge B r ell p e)).2
    rw [starAEdge_left]
    exact congrArg Sum.inl ((A.mem_leftIncident x e).1 he)
  · intro e he f hf hef
    exact A.starAEdge_injective B r ell p hef
  · intro s hs
    have hsleft := ((A.starProduct B r ell p q σ).mem_leftIncident (.inl x) s).1 hs
    rcases s with ea | rest
    · have hleft : A.left ea.1 = x := by simpa using hsleft
      refine ⟨ea.1, (A.mem_leftIncident x ea.1).2 hleft, ?_⟩
      simp [starAEdge, ea.2]
    · rcases rest with eb | i
      · have : False := by simpa using hsleft
        exact this.elim
      · have hleft : A.left (p i).1 = x := by simpa using hsleft
        refine ⟨(p i).1, (A.mem_leftIncident x (p i).1).2 hleft, ?_⟩
        have hroot : A.right (p i).1 = r := A.port_right_eq r p i
        simp [starAEdge, hroot]

/-- Degrees at surviving `B`-right vertices are unchanged. -/
theorem starProduct_rightIncident_b
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3)) (y : YB) :
    ((A.starProduct B r ell p q σ).rightIncident (.inr y)).card =
      (B.rightIncident y).card := by
  classical
  symm
  refine Finset.card_nbij (A.starBEdge B r ell q σ) ?_ ?_ ?_
  · intro e he
    apply ((A.starProduct B r ell p q σ).mem_rightIncident (.inr y)
      (A.starBEdge B r ell q σ e)).2
    rw [starBEdge_right]
    exact congrArg Sum.inr ((B.mem_rightIncident y e).1 he)
  · intro e he f hf hef
    exact A.starBEdge_injective B r ell q σ hef
  · intro s hs
    have hsright := ((A.starProduct B r ell p q σ).mem_rightIncident (.inr y) s).1 hs
    rcases s with ea | rest
    · have : False := by simpa using hsright
      exact this.elim
    · rcases rest with eb | i
      · have hright : B.right eb.1 = y := by simpa using hsright
        refine ⟨eb.1, (B.mem_rightIncident y eb.1).2 hright, ?_⟩
        simp [starBEdge, eb.2]
      · have hright : B.right (q (σ i)).1 = y := by simpa using hsright
        refine ⟨(q (σ i)).1, (B.mem_rightIncident y (q (σ i)).1).2 hright, ?_⟩
        have hroot : B.left (q (σ i)).1 = ell := B.port_left_eq ell q (σ i)
        simp [starBEdge, hroot]

/-- Degrees at surviving non-root `A`-right vertices are unchanged. -/
theorem starProduct_rightIncident_a
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (y : {y : YA // y ≠ r}) :
    ((A.starProduct B r ell p q σ).rightIncident (.inl y)).card =
      (A.rightIncident y.1).card := by
  classical
  symm
  refine Finset.card_nbij (A.starAEdge B r ell p) ?_ ?_ ?_
  · intro e he
    have hright : A.right e = y.1 := (A.mem_rightIncident y.1 e).1 he
    have hyne : y.1 ≠ r := y.2
    apply ((A.starProduct B r ell p q σ).mem_rightIncident (.inl y)
      (A.starAEdge B r ell p e)).2
    simp [starAEdge, hright, hyne]
  · intro e he f hf hef
    exact A.starAEdge_injective B r ell p hef
  · intro s hs
    have hsright := ((A.starProduct B r ell p q σ).mem_rightIncident (.inl y) s).1 hs
    rcases s with ea | rest
    · have hright : A.right ea.1 = y.1 := by
        simpa using congrArg (fun z => Sum.elim Subtype.val (fun _ => r) z) hsright
      refine ⟨ea.1, (A.mem_rightIncident y.1 ea.1).2 hright, ?_⟩
      simp [starAEdge, ea.2]
    · rcases rest with eb | i
      · have : False := by simpa using hsright
        exact this.elim
      · have : False := by simpa using hsright
        exact this.elim

/-- Degrees at surviving non-root `B`-left vertices are unchanged. -/
theorem starProduct_leftIncident_b
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (x : {x : XB // x ≠ ell}) :
    ((A.starProduct B r ell p q σ).leftIncident (.inr x)).card =
      (B.leftIncident x.1).card := by
  classical
  symm
  refine Finset.card_nbij (A.starBEdge B r ell q σ) ?_ ?_ ?_
  · intro e he
    have hleft : B.left e = x.1 := (B.mem_leftIncident x.1 e).1 he
    have hxne : x.1 ≠ ell := x.2
    apply ((A.starProduct B r ell p q σ).mem_leftIncident (.inr x)
      (A.starBEdge B r ell q σ e)).2
    simp [starBEdge, hleft, hxne]
  · intro e he f hf hef
    exact A.starBEdge_injective B r ell q σ hef
  · intro s hs
    have hsleft := ((A.starProduct B r ell p q σ).mem_leftIncident (.inr x) s).1 hs
    rcases s with ea | rest
    · have : False := by simpa using hsleft
      exact this.elim
    · rcases rest with eb | i
      · have hleft : B.left eb.1 = x.1 := by
          simpa using congrArg (fun z => Sum.elim (fun _ => ell) Subtype.val z) hsleft
        refine ⟨eb.1, (B.mem_leftIncident x.1 eb.1).2 hleft, ?_⟩
        simp [starBEdge, eb.2]
      · have : False := by simpa using hsleft
        exact this.elim

/-- Star products preserve cubicity. -/
theorem starProduct_isCubic
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (hB : B.IsCubic) :
    (A.starProduct B r ell p q σ).IsCubic := by
  rw [(A.starProduct B r ell p q σ).isCubic_iff]
  constructor
  · intro x
    rcases x with x | x
    · change ((A.starProduct B r ell p q σ).leftIncident (.inl x)).card = 3
      rw [starProduct_leftIncident_a]
      exact ((A.isCubic_iff).1 hA).1 x
    · change ((A.starProduct B r ell p q σ).leftIncident (.inr x)).card = 3
      rw [starProduct_leftIncident_b]
      exact ((B.isCubic_iff).1 hB).1 x.1
  · intro y
    rcases y with y | y
    · change ((A.starProduct B r ell p q σ).rightIncident (.inl y)).card = 3
      rw [starProduct_rightIncident_a]
      exact ((A.isCubic_iff).1 hA).2 y.1
    · change ((A.starProduct B r ell p q σ).rightIncident (.inr y)).card = 3
      rw [starProduct_rightIncident_b]
      exact ((B.isCubic_iff).1 hB).2 y

end BipartiteMultigraph
end BachThesisLean
