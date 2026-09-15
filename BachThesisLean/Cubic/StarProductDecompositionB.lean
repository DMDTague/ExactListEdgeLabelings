import BachThesisLean.Cubic.StarProductDecomposition

namespace BachThesisLean
namespace BipartiteMultigraph

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-! The second-factor half of star-product matching decomposition. -/

/-- Pullback along `starBEdge` preserves selected incidence at each surviving
`B`-left vertex. -/
theorem starRestrictedB_left_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell)) (x : {x : XB // x ≠ ell}) :
    (B.selectedIncident (A.starRestrictedB B r ell q σ P) (.inl x.1)).card =
      ((A.starProduct B r ell p q σ).selectedIncident P
        (.inl (.inr x))).card := by
  classical
  refine Finset.card_nbij (A.starBEdge B r ell q σ) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    have hleft : B.left e = x.1 := he.2
    have hne : B.left e ≠ ell := by simpa [hleft] using x.2
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · exact (A.mem_starRestrictedB B r ell q σ P e).1 he.1
    · have hedge : A.starBEdge B r ell q σ e =
          (Sum.inr (Sum.inl ⟨e, hne⟩) : StarEdge A B r ell) := by
        simp [starBEdge, hne]
      rw [hedge]
      apply congrArg Sum.inr
      exact Subtype.ext hleft
  · intro e he f hf hef
    exact A.starBEdge_injective B r ell q σ hef
  · intro s hs
    have hs' : s ∈ (A.starProduct B r ell p q σ).selectedIncident P
        (.inl (.inr x)) := by
      simpa using hs
    rw [mem_selectedIncident] at hs'
    rcases s with ea | rest
    · have : False := by simpa [Incident] using hs'.2
      exact this.elim
    · rcases rest with eb | i
      · have hleft : B.left eb.1 = x.1 := by
          simpa [Incident] using
            congrArg (fun z => Sum.elim (fun _ => ell) Subtype.val z) hs'.2
        refine ⟨eb.1, (mem_selectedIncident B _ (.inl x.1) eb.1).2 ⟨?_, hleft⟩, ?_⟩
        · exact (A.mem_starRestrictedB_internal B r ell q σ P eb).2 hs'.1
        · simp [starBEdge, eb.2]
      · have : False := by simpa [Incident] using hs'.2
        exact this.elim

/-- Pullback along `starBEdge` preserves selected incidence at every `B`-right
vertex, including source edges that become bridges. -/
theorem starRestrictedB_right_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (P : Finset (StarEdge A B r ell)) (y : YB) :
    (B.selectedIncident (A.starRestrictedB B r ell q σ P) (.inr y)).card =
      ((A.starProduct B r ell p q σ).selectedIncident P
        (.inr (.inr y))).card := by
  classical
  refine Finset.card_nbij (A.starBEdge B r ell q σ) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · exact (A.mem_starRestrictedB B r ell q σ P e).1 he.1
    · change (A.starProduct B r ell p q σ).right (A.starBEdge B r ell q σ e) =
        Sum.inr y
      rw [A.starBEdge_right B r ell p q σ e]
      exact congrArg Sum.inr he.2
  · intro e he f hf hef
    exact A.starBEdge_injective B r ell q σ hef
  · intro s hs
    have hs' : s ∈ (A.starProduct B r ell p q σ).selectedIncident P
        (.inr (.inr y)) := by
      simpa using hs
    rw [mem_selectedIncident] at hs'
    rcases s with ea | rest
    · have : False := by simpa [Incident] using hs'.2
      exact this.elim
    · rcases rest with eb | i
      · have hright : B.right eb.1 = y := by simpa [Incident] using hs'.2
        refine ⟨eb.1, (mem_selectedIncident B _ (.inr y) eb.1).2 ⟨?_, hright⟩, ?_⟩
        · exact (A.mem_starRestrictedB_internal B r ell q σ P eb).2 hs'.1
        · simp [starBEdge, eb.2]
      · have hright : B.right (q (σ i)).1 = y := by simpa [Incident] using hs'.2
        refine ⟨(q (σ i)).1,
          (mem_selectedIncident B _ (.inr y) (q (σ i)).1).2 ⟨?_, hright⟩, ?_⟩
        · exact (A.mem_starRestrictedB_port B r ell q σ P i).2 hs'.1
        · exact A.starBEdge_port B r ell q σ i

/-- At the deleted `B` root, the restricted matching consists exactly of the
source edge corresponding to the unique selected bridge. -/
theorem starRestrictedB_root_selectedIncident
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    ∃ i : Fin 3,
      (Sum.inr (Sum.inr i) : StarEdge A B r ell) ∈ P ∧
      B.selectedIncident (A.starRestrictedB B r ell q σ P) (.inl ell) =
        {(q (σ i)).1} := by
  classical
  obtain ⟨i, hi, huniq⟩ := hP.existsUnique_starBridge A B r ell p q σ hA
  refine ⟨i, hi, ?_⟩
  ext e
  simp only [Finset.mem_singleton]
  constructor
  · intro he
    rw [mem_selectedIncident] at he
    have hel : B.left e = ell := he.2
    let er : {g : EB // g ∈ B.incidentEdges (.inl ell)} :=
      ⟨e, (mem_incidentEdges B (.inl ell) e).2 hel⟩
    let k : Fin 3 := q.symm er
    let j : Fin 3 := σ.symm k
    have hqk : (q k).1 = e := by
      have hsub : q k = er := by simpa [k] using q.apply_symm_apply er
      exact congrArg Subtype.val hsub
    have hsig : σ j = k := by simp [j]
    have hj : (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈ P := by
      rw [← A.starBEdge_port B r ell q σ j]
      rw [hsig, hqk]
      exact (A.mem_starRestrictedB B r ell q σ P e).1 he.1
    have hji : j = i := huniq j hj
    rw [← hqk, ← hsig, hji]
  · intro hei
    subst e
    apply (mem_selectedIncident B _ (.inl ell) (q (σ i)).1).2
    refine ⟨(A.mem_starRestrictedB_port B r ell q σ P i).2 hi, ?_⟩
    exact B.port_left_eq ell q (σ i)

/-- Restricting a perfect matching of the star product restores a perfect
matching of the `B` factor. -/
theorem starRestrictedB_isPerfectMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (hA : A.IsCubic) (P : Finset (StarEdge A B r ell))
    (hP : (A.starProduct B r ell p q σ).IsPerfectMatching P) :
    B.IsPerfectMatching (A.starRestrictedB B r ell q σ P) := by
  intro v
  rcases v with x | y
  · by_cases hxe : x = ell
    · subst x
      obtain ⟨i, hi, hset⟩ :=
        A.starRestrictedB_root_selectedIncident B r ell p q σ hA P hP
      rw [hset]
      simp
    · let xs : {z : XB // z ≠ ell} := ⟨x, hxe⟩
      rw [A.starRestrictedB_left_card B r ell p q σ P xs]
      exact hP (.inl (.inr xs))
  · rw [A.starRestrictedB_right_card B r ell p q σ P y]
    exact hP (.inr (.inr y))

end BipartiteMultigraph
end BachThesisLean
