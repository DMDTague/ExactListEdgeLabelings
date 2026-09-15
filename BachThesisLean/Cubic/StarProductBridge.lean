import BachThesisLean.Cubic.MatchingCardinality
import BachThesisLean.Cubic.StarProductMatching
import Mathlib.Data.Finset.Sum

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
# The star cut uses exactly one matching edge

For a perfect matching of a star product, `P.toLeft` records selected internal
`A` edges, `P.toRight.toLeft` records selected internal `B` edges, and
`P.toRight.toRight` records selected bridges. Counting the surviving shores
shows that the last finset has cardinality one.
-/

/-- Selected internal `A` edges are in bijection with the surviving `A`-right
vertices. -/
theorem starPerfectMatching_aInternal_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    P.toLeft.card = Fintype.card {y : YA // y ≠ r} := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_nbij
    (fun e : {e : EA // A.right e ≠ r} => ⟨A.right e.1, e.2⟩) ?_ ?_ ?_
  · intro e he
    simp
  · intro e he f hf hef
    have heP : (Sum.inl e : StarEdge A B r ell) ∈ P := by simpa using he
    have hfP : (Sum.inl f : StarEdge A B r ell) ∈ P := by simpa using hf
    have hincE : (A.starProduct B r ell p q σ).Incident
        (Sum.inl e) (.inr (.inl ⟨A.right e.1, e.2⟩)) := by
      rfl
    have hincF : (A.starProduct B r ell p q σ).Incident
        (Sum.inl f) (.inr (.inl ⟨A.right e.1, e.2⟩)) := by
      change (Sum.inl ⟨A.right f.1, f.2⟩ : StarRight YA YB r) =
        Sum.inl ⟨A.right e.1, e.2⟩
      exact congrArg Sum.inl hef.symm
    have hs := ((A.starProduct B r ell p q σ).isMatching_iff P).1
      hP.isMatching (Sum.inl e) heP (Sum.inl f) hfP
      (.inr (.inl ⟨A.right e.1, e.2⟩)) hincE hincF
    exact Sum.inl_injective hs
  · intro y hy
    obtain ⟨s, hs, _⟩ := hP.existsUnique_incident (.inr (.inl y))
    rcases s with ea | rest
    · refine ⟨ea, ?_, ?_⟩
      · simpa using hs.1
      · have hi : (Sum.inl ⟨A.right ea.1, ea.2⟩ : StarRight YA YB r) =
            Sum.inl y := by
          simpa [Incident] using hs.2
        exact Sum.inl_injective hi
    · rcases rest with eb | i
      · have : False := by simpa [Incident] using hs.2
        exact this.elim
      · have : False := by simpa [Incident] using hs.2
        exact this.elim

/-- Selected internal `B` edges are in bijection with the surviving `B`-left
vertices. -/
theorem starPerfectMatching_bInternal_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    P.toRight.toLeft.card = Fintype.card {x : XB // x ≠ ell} := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_nbij
    (fun e : {e : EB // B.left e ≠ ell} => ⟨B.left e.1, e.2⟩) ?_ ?_ ?_
  · intro e he
    simp
  · intro e he f hf hef
    have heP : (Sum.inr (Sum.inl e) : StarEdge A B r ell) ∈ P := by
      simpa using he
    have hfP : (Sum.inr (Sum.inl f) : StarEdge A B r ell) ∈ P := by
      simpa using hf
    have hincE : (A.starProduct B r ell p q σ).Incident
        (Sum.inr (Sum.inl e)) (.inl (.inr ⟨B.left e.1, e.2⟩)) := by
      rfl
    have hincF : (A.starProduct B r ell p q σ).Incident
        (Sum.inr (Sum.inl f)) (.inl (.inr ⟨B.left e.1, e.2⟩)) := by
      change (Sum.inr ⟨B.left f.1, f.2⟩ : StarLeft XA XB ell) =
        Sum.inr ⟨B.left e.1, e.2⟩
      exact congrArg Sum.inr hef.symm
    have hs := ((A.starProduct B r ell p q σ).isMatching_iff P).1
      hP.isMatching (Sum.inr (Sum.inl e)) heP (Sum.inr (Sum.inl f)) hfP
      (.inl (.inr ⟨B.left e.1, e.2⟩)) hincE hincF
    exact Sum.inl_injective (Sum.inr_injective hs)
  · intro x hx
    obtain ⟨s, hs, _⟩ := hP.existsUnique_incident (.inl (.inr x))
    rcases s with ea | rest
    · have : False := by simpa [Incident] using hs.2
      exact this.elim
    · rcases rest with eb | i
      · refine ⟨eb, ?_, ?_⟩
        · simpa using hs.1
        · have hi : (Sum.inr ⟨B.left eb.1, eb.2⟩ : StarLeft XA XB ell) =
              Sum.inr x := by
            simpa [Incident] using hs.2
          exact Sum.inr_injective hi
      · have : False := by simpa [Incident] using hs.2
        exact this.elim

/-- Every perfect matching of a cubic star product uses exactly one of the
three joining edge copies. Cubicity of the `A` factor supplies the shore
balance; no regularity assumption on `B` is needed for this counting step. -/
theorem starPerfectMatching_bridge_card_eq_one
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    P.toRight.toRight.card = 1 := by
  classical
  have hPcard : P.card =
      Fintype.card XA + Fintype.card {x : XB // x ≠ ell} := by
    simpa [StarLeft] using hP.card_eq_left
  have hsplit : P.toLeft.card + P.toRight.card = P.card :=
    Finset.card_toLeft_add_card_toRight
  have hsplitRight : P.toRight.toLeft.card + P.toRight.toRight.card =
      P.toRight.card :=
    Finset.card_toLeft_add_card_toRight
  have hAInternal :=
    A.starPerfectMatching_aInternal_card B r ell p q σ P hP
  have hBInternal :=
    A.starPerfectMatching_bInternal_card B r ell p q σ P hP
  have hshores : Fintype.card XA = Fintype.card YA :=
    A.card_left_eq_card_right_of_cubic hA
  have hsurvive : Fintype.card {y : YA // y ≠ r} = Fintype.card YA - 1 := by
    simpa using (Fintype.card_subtype_compl (fun y : YA => y = r))
  have hYpos : 0 < Fintype.card YA := Fintype.card_pos_iff.mpr ⟨r⟩
  have hbalance := hsplit
  rw [hAInternal, ← hsplitRight, hBInternal, hPcard] at hbalance
  rw [hsurvive, hshores] at hbalance
  omega

/-- Existential/unique form of the preceding bridge-count theorem. -/
theorem IsPerfectMatching.existsUnique_starBridge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) {P : Finset (StarEdge A B r ell)}
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    ∃! i : Fin 3, (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P := by
  classical
  have hcard := A.starPerfectMatching_bridge_card_eq_one B r ell p q σ hA P hP
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_, ?_⟩
  · have : i ∈ P.toRight.toRight := by simp [hi]
    simpa using this
  · intro j hj
    have hj' : j ∈ P.toRight.toRight := by simpa using hj
    simpa [hi] using hj'

end BipartiteMultigraph
end BachThesisLean
