import BachThesisLean.Cubic.StarProductDegrees

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
# Perfect-matchings in a star product

A perfect matching of each factor through corresponding ports glues to a
perfect matching of the star product. The definition below keeps the three
kinds of edge copies explicit: selected internal `A` edges, selected internal
`B` edges, and the single selected bridge.
-/

/-- Glue edge sets through bridge `i`. -/
noncomputable def starGluedMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB)
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3) :
    Finset (StarEdge A B r ell) := by
  classical
  exact Finset.univ.filter fun s =>
    match s with
    | .inl e => e.1 ∈ PA
    | .inr (.inl e) => e.1 ∈ PB
    | .inr (.inr j) => j = i

@[simp] theorem mem_starGluedMatching_aInternal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (e : {e : EA // A.right e ≠ r}) :
    (Sum.inl e : StarEdge A B r ell) ∈ A.starGluedMatching B r ell PA PB i ↔
      e.1 ∈ PA := by
  classical
  simp [starGluedMatching]

@[simp] theorem mem_starGluedMatching_bInternal
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (e : {e : EB // B.left e ≠ ell}) :
    (Sum.inr (Sum.inl e) : StarEdge A B r ell) ∈
        A.starGluedMatching B r ell PA PB i ↔ e.1 ∈ PB := by
  classical
  simp [starGluedMatching]

@[simp] theorem mem_starGluedMatching_bridge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (PA : Finset EA) (PB : Finset EB) (i j : Fin 3) :
    (Sum.inr (Sum.inr j) : StarEdge A B r ell) ∈
        A.starGluedMatching B r ell PA PB i ↔ j = i := by
  classical
  simp [starGluedMatching]

/-- At an `A`-left vertex, the glued selected incidence is in bijection with
selected incidence in `PA`. The root-port hypothesis is exactly what makes a
source root edge map to the chosen bridge. -/
theorem starGluedMatching_left_a_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA) (x : XA) :
    ((A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inl (.inl x))).card =
      (A.selectedIncident PA (.inl x)).card := by
  classical
  symm
  refine Finset.card_nbij (A.starAEdge B r ell p) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · by_cases hr : A.right e = r
      · have heq : e = (p i).1 :=
          (A.isMatching_iff PA).1 hPA.isMatching e he.1 (p i).1 hpi (.inr r)
            (by simpa [Incident] using hr) (by simp [Incident])
        subst e
        simp [starAEdge, A.port_right_eq]
      · simp [starAEdge, hr, he.1]
    · change (A.starProduct B r ell p q σ).left (A.starAEdge B r ell p e) = .inl x
      rw [starAEdge_left]
      exact congrArg Sum.inl he.2
  · intro e he f hf hef
    exact A.starAEdge_injective B r ell p hef
  · intro s hs
    change s ∈ (A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inl (.inl x)) at hs
    rw [mem_selectedIncident] at hs
    rcases s with ea | rest
    · have hleft : A.left ea.1 = x := by simpa [Incident] using hs.2
      refine ⟨ea.1, (mem_selectedIncident A PA (.inl x) ea.1).2 ⟨?_, hleft⟩, ?_⟩
      · simpa using hs.1
      · simp [starAEdge, ea.2]
    · rcases rest with eb | j
      · have : False := by simpa [Incident] using hs.2
        exact this.elim
      · have hji : j = i := by simpa using hs.1
        subst j
        have hleft : A.left (p i).1 = x := by simpa [Incident] using hs.2
        refine ⟨(p i).1,
          (mem_selectedIncident A PA (.inl x) (p i).1).2 ⟨hpi, hleft⟩, ?_⟩
        simp [starAEdge, A.port_right_eq]

/-- At a surviving `A`-right vertex only internal `A` edge copies can occur. -/
theorem starGluedMatching_right_a_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (y : {y : YA // y ≠ r}) :
    ((A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inr (.inl y))).card =
      (A.selectedIncident PA (.inr y.1)).card := by
  classical
  symm
  refine Finset.card_nbij (A.starAEdge B r ell p) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    have hright : A.right e = y.1 := he.2
    have hne : A.right e ≠ r := by simpa [hright] using y.2
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · simp [starAEdge, hne, he.1]
    · change (A.starProduct B r ell p q σ).right (A.starAEdge B r ell p e) = .inl y
      have hedge : A.starAEdge B r ell p e =
          (Sum.inl ⟨e, hne⟩ : StarEdge A B r ell) := by
        simp [starAEdge, hne]
      rw [hedge]
      apply congrArg Sum.inl
      exact Subtype.ext hright
  · intro e he f hf hef
    exact A.starAEdge_injective B r ell p hef
  · intro s hs
    change s ∈ (A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inr (.inl y)) at hs
    rw [mem_selectedIncident] at hs
    rcases s with ea | rest
    · have hright : A.right ea.1 = y.1 := by
        simpa [Incident] using congrArg (fun z => Sum.elim Subtype.val (fun _ => r) z) hs.2
      refine ⟨ea.1, (mem_selectedIncident A PA (.inr y.1) ea.1).2 ⟨?_, hright⟩, ?_⟩
      · simpa using hs.1
      · simp [starAEdge, ea.2]
    · rcases rest with eb | j
      · have : False := by simpa [Incident] using hs.2
        exact this.elim
      · have : False := by simpa [Incident] using hs.2
        exact this.elim

/-- At a surviving `B`-left vertex only internal `B` edge copies can occur. -/
theorem starGluedMatching_left_b_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (x : {x : XB // x ≠ ell}) :
    ((A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inl (.inr x))).card =
      (B.selectedIncident PB (.inl x.1)).card := by
  classical
  symm
  refine Finset.card_nbij (A.starBEdge B r ell q σ) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    have hleft : B.left e = x.1 := he.2
    have hne : B.left e ≠ ell := by simpa [hleft] using x.2
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · simp [starBEdge, hne, he.1]
    · change (A.starProduct B r ell p q σ).left (A.starBEdge B r ell q σ e) = .inr x
      have hedge : A.starBEdge B r ell q σ e =
          (Sum.inr (Sum.inl ⟨e, hne⟩) : StarEdge A B r ell) := by
        simp [starBEdge, hne]
      rw [hedge]
      apply congrArg Sum.inr
      exact Subtype.ext hleft
  · intro e he f hf hef
    exact A.starBEdge_injective B r ell q σ hef
  · intro s hs
    change s ∈ (A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inl (.inr x)) at hs
    rw [mem_selectedIncident] at hs
    rcases s with ea | rest
    · have : False := by simpa [Incident] using hs.2
      exact this.elim
    · rcases rest with eb | j
      · have hleft : B.left eb.1 = x.1 := by
          simpa [Incident] using congrArg (fun z => Sum.elim (fun _ => ell) Subtype.val z) hs.2
        refine ⟨eb.1, (mem_selectedIncident B PB (.inl x.1) eb.1).2 ⟨?_, hleft⟩, ?_⟩
        · simpa using hs.1
        · simp [starBEdge, eb.2]
      · have : False := by simpa [Incident] using hs.2
        exact this.elim

/-- At a `B`-right vertex the glued selected incidence is in bijection with
selected incidence in `PB`. -/
theorem starGluedMatching_right_b_card
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB) (y : YB) :
    ((A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inr (.inr y))).card =
      (B.selectedIncident PB (.inr y)).card := by
  classical
  symm
  refine Finset.card_nbij (A.starBEdge B r ell q σ) ?_ ?_ ?_
  · intro e he
    rw [mem_selectedIncident] at he
    refine (mem_selectedIncident _ _ _ _).2 ⟨?_, ?_⟩
    · by_cases hl : B.left e = ell
      · have heq : e = (q (σ i)).1 :=
          (B.isMatching_iff PB).1 hPB.isMatching e he.1 (q (σ i)).1 hqi (.inl ell)
            (by simpa [Incident] using hl) (by simp [Incident])
        subst e
        simp [starBEdge, B.port_left_eq]
      · simp [starBEdge, hl, he.1]
    · change (A.starProduct B r ell p q σ).right (A.starBEdge B r ell q σ e) = .inr y
      rw [starBEdge_right]
      exact congrArg Sum.inr he.2
  · intro e he f hf hef
    exact A.starBEdge_injective B r ell q σ hef
  · intro s hs
    change s ∈ (A.starProduct B r ell p q σ).selectedIncident
      (A.starGluedMatching B r ell PA PB i) (.inr (.inr y)) at hs
    rw [mem_selectedIncident] at hs
    rcases s with ea | rest
    · have : False := by simpa [Incident] using hs.2
      exact this.elim
    · rcases rest with eb | j
      · have hright : B.right eb.1 = y := by simpa [Incident] using hs.2
        refine ⟨eb.1, (mem_selectedIncident B PB (.inr y) eb.1).2 ⟨?_, hright⟩, ?_⟩
        · simpa using hs.1
        · simp [starBEdge, eb.2]
      · have hji : j = i := by simpa using hs.1
        subst j
        have hright : B.right (q (σ i)).1 = y := by simpa [Incident] using hs.2
        refine ⟨(q (σ i)).1,
          (mem_selectedIncident B PB (.inr y) (q (σ i)).1).2 ⟨hqi, hright⟩, ?_⟩
        simp [starBEdge, B.port_left_eq]

/-- Perfect matchings through corresponding ports glue to a perfect matching
of the star product. -/
theorem starGluedMatching_isPerfectMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hpi : (p i).1 ∈ PA) (hqi : (q (σ i)).1 ∈ PB) :
    (A.starProduct B r ell p q σ).IsPerfectMatching
      (A.starGluedMatching B r ell PA PB i) := by
  intro v
  rcases v with v | v
  · rcases v with x | x
    · rw [A.starGluedMatching_left_a_card B r ell p q σ PA PB i hPA hpi x]
      exact hPA (.inl x)
    · rw [A.starGluedMatching_left_b_card B r ell p q σ PA PB i x]
      exact hPB (.inl x.1)
  · rcases v with y | y
    · rw [A.starGluedMatching_right_a_card B r ell p q σ PA PB i y]
      exact hPA (.inr y.1)
    · rw [A.starGluedMatching_right_b_card B r ell p q σ PA PB i hPB hqi y]
      exact hPB (.inr y)

end BipartiteMultigraph
end BachThesisLean
