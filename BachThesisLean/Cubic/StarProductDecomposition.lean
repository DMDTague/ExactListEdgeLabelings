import BachThesisLean.Cubic.StarProductRestriction

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
# Decomposing a star-product perfect matching

The pullback `starRestrictedA` is a perfect matching of the first factor once
the star matching is known to use one bridge.  This is the first half of the
converse to `starGluedMatching_isPerfectMatching`.
-/

/-- Pullback along `starAEdge` preserves selected incidence at an `A`-left
vertex. -/
theorem starRestrictedA_left_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell)) (x : XA) :
    (A.selectedIncident (A.starRestrictedA B r ell p P) (.inl x)).card =
      ((A.starProduct B r ell p q σ).selectedIncident P
        (.inl (.inl x))).card := by
  classical
  refine Finset.card_nbij (A.starAEdge B r ell p) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · exact (A.mem_starRestrictedA B r ell p P e).1 he.1
    · change (A.starProduct B r ell p q σ).left (A.starAEdge B r ell p e) =
        Sum.inl x
      rw [A.starAEdge_left B r ell p q σ e]
      exact congrArg Sum.inl he.2
  · intro e he f hf hef
    exact A.starAEdge_injective B r ell p hef
  · intro s hs
    have hs' : s ∈ (A.starProduct B r ell p q σ).selectedIncident P
        (.inl (.inl x)) := by
      simpa using hs
    rw [mem_selectedIncident] at hs'
    rcases s with ea | rest
    · have hleft : A.left ea.1 = x := by simpa [Incident] using hs'.2
      refine ⟨ea.1, (mem_selectedIncident A _ (.inl x) ea.1).2 ⟨?_, hleft⟩, ?_⟩
      · exact (A.mem_starRestrictedA_internal B r ell p P ea).2 hs'.1
      · simp [starAEdge, ea.2]
    · rcases rest with eb | i
      · have : False := by simpa [Incident] using hs'.2
        exact this.elim
      · have hleft : A.left (p i).1 = x := by simpa [Incident] using hs'.2
        refine ⟨(p i).1, (mem_selectedIncident A _ (.inl x) (p i).1).2 ⟨?_, hleft⟩, ?_⟩
        · exact (A.mem_starRestrictedA_port B r ell p P i).2 hs'.1
        · exact A.starAEdge_port B r ell p i

/-- Pullback along `starAEdge` preserves selected incidence at every surviving
`A`-right vertex. -/
theorem starRestrictedA_right_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell)) (y : {y : YA // y ≠ r}) :
    (A.selectedIncident (A.starRestrictedA B r ell p P) (.inr y.1)).card =
      ((A.starProduct B r ell p q σ).selectedIncident P
        (.inr (.inl y))).card := by
  classical
  refine Finset.card_nbij (A.starAEdge B r ell p) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    have hright : A.right e = y.1 := he.2
    have hne : A.right e ≠ r := by simpa [hright] using y.2
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · exact (A.mem_starRestrictedA B r ell p P e).1 he.1
    · have hedge : A.starAEdge B r ell p e =
          (Sum.inl ⟨e, hne⟩ : StarEdge A B r ell) := by
        simp [starAEdge, hne]
      rw [hedge]
      apply congrArg Sum.inl
      exact Subtype.ext hright
  · intro e he f hf hef
    exact A.starAEdge_injective B r ell p hef
  · intro s hs
    have hs' : s ∈ (A.starProduct B r ell p q σ).selectedIncident P
        (.inr (.inl y)) := by
      simpa using hs
    rw [mem_selectedIncident] at hs'
    rcases s with ea | rest
    · have hright : A.right ea.1 = y.1 := by
        simpa [Incident] using
          congrArg (fun z => Sum.elim Subtype.val (fun _ => r) z) hs'.2
      refine ⟨ea.1, (mem_selectedIncident A _ (.inr y.1) ea.1).2 ⟨?_, hright⟩, ?_⟩
      · exact (A.mem_starRestrictedA_internal B r ell p P ea).2 hs'.1
      · simp [starAEdge, ea.2]
    · rcases rest with eb | i
      · have : False := by simpa [Incident] using hs'.2
        exact this.elim
      · have : False := by simpa [Incident] using hs'.2
        exact this.elim

/-- At the deleted `A` root, the restricted matching consists exactly of the
source edge corresponding to the unique selected bridge. -/
theorem starRestrictedA_root_selectedIncident
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    ∃ i : Fin 3,
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P ∧
      A.selectedIncident (A.starRestrictedA B r ell p P) (.inr r) = {(p i).1} := by
  classical
  obtain ⟨i, hi, huniq⟩ := hP.existsUnique_starBridge A B r ell p q σ hA
  refine ⟨i, hi, ?_⟩
  ext e
  simp only [Finset.mem_singleton]
  constructor
  · intro he
    rw [mem_selectedIncident] at he
    have her : A.right e = r := he.2
    let er : {g : EA // g ∈ A.incidentEdges (.inr r)} :=
      ⟨e, (mem_incidentEdges A (.inr r) e).2 her⟩
    let j : Fin 3 := p.symm er
    have hpj : (p j).1 = e := by
      have hsub : p j = er := by simpa [j] using p.apply_symm_apply er
      exact congrArg Subtype.val hsub
    have hj : (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈ P := by
      rw [← A.starAEdge_port B r ell p j, hpj]
      exact (A.mem_starRestrictedA B r ell p P e).1 he.1
    have hji : j = i := huniq j hj
    rw [← hpj, hji]
  · intro hei
    subst e
    apply (mem_selectedIncident A _ (.inr r) (p i).1).2
    refine ⟨(A.mem_starRestrictedA_port B r ell p P i).2 hi, ?_⟩
    exact A.port_right_eq r p i

/-- Restricting a perfect matching of the star product restores a perfect
matching of the `A` factor. -/
theorem starRestrictedA_isPerfectMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    A.IsPerfectMatching (A.starRestrictedA B r ell p P) := by
  intro v
  rcases v with x | y
  · rw [A.starRestrictedA_left_card B r ell p q σ P x]
    exact hP (.inl (.inl x))
  · by_cases hyr : y = r
    · subst y
      obtain ⟨i, hi, hset⟩ :=
        A.starRestrictedA_root_selectedIncident B r ell p q σ hA P hP
      rw [hset]
      simp
    · let ys : {z : YA // z ≠ r} := ⟨y, hyr⟩
      rw [A.starRestrictedA_right_card B r ell p q σ P ys]
      exact hP (.inr (.inl ys))

end BipartiteMultigraph
end BachThesisLean
