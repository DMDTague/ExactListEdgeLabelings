import BachThesisLean.Cubic.TightCutMatchingCommon
import BachThesisLean.Cubic.StarProductSourceMembership
import BachThesisLean.Cubic.PfaffianRelative

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
# Relative permutations for common-completion star matchings

When two `A`-factor perfect matchings use the same port and are glued against
one common `B`-factor perfect matching, their relative permutation on the star
product is block diagonal: the `A` relative permutation on the first left-shore
summand and the identity on the surviving `B`-left summand.  This is the
permutation-sign half of Pfaffian tight-cut cancellation.
-/

/-- Bundle the canonical glued edge set as a perfect matching. -/
noncomputable def starGluedPM
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hpi : (p i).1 ∈ PA) (hqi : (q (σ i)).1 ∈ PB) :
    (A.starProduct B r ell p q σ).PerfectMatching :=
  ⟨A.starGluedMatching B r ell PA PB i,
    A.starGluedMatching_isPerfectMatching B r ell p q σ
      PA PB i hPA hPB hpi hqi⟩

@[simp] theorem starGluedPM_val
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hpi : (p i).1 ∈ PA) (hqi : (q (σ i)).1 ∈ PB) :
    (starGluedPM A B r ell p q σ PA PB i hPA hPB hpi hqi).val =
      A.starGluedMatching B r ell PA PB i := rfl

/-- On the `A`-left summand, equal source matching-right vertices remain equal
after common-completion gluing. -/
theorem starGluedPM_matchingRight_inl_eq_of_source
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA QA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hQA : A.IsPerfectMatching QA)
    (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hQi : (p i).1 ∈ QA)
    (hBi : (q (σ i)).1 ∈ PB)
    (x y : XA)
    (hxy : hPA.matchingRight x = hQA.matchingRight y) :
    (starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingRight
        (Sum.inl x) =
      (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingRight
        (Sum.inl y) := by
  classical
  let Gs := A.starProduct B r ell p q σ
  let e := hPA.matchingEdge x
  let f := hQA.matchingEdge y
  have hePA : e ∈ PA := by simpa [e] using hPA.matchingEdge_mem x
  have hfQA : f ∈ QA := by simpa [f] using hQA.matchingEdge_mem y
  have heStar : A.starAEdge B r ell p e ∈
      A.starGluedMatching B r ell PA PB i :=
    (A.starAEdge_mem_starGluedMatching_iff B r ell p PA PB i hPA hPi e).2 hePA
  have hfStar : A.starAEdge B r ell p f ∈
      A.starGluedMatching B r ell QA PB i :=
    (A.starAEdge_mem_starGluedMatching_iff B r ell p QA PB i hQA hQi f).2 hfQA
  have heLeft : Gs.left (A.starAEdge B r ell p e) = Sum.inl x := by
    simpa [Gs, e] using A.starAEdge_left B r ell p q σ e
  have hfLeft : Gs.left (A.starAEdge B r ell p f) = Sum.inl y := by
    simpa [Gs, f] using A.starAEdge_left B r ell p q σ f
  have hPedge :
      (starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingEdge
          (Sum.inl x) = A.starAEdge B r ell p e := by
    exact (starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingEdge_eq_of_mem_left
      (Sum.inl x) heStar heLeft
  have hQedge :
      (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingEdge
          (Sum.inl y) = A.starAEdge B r ell p f := by
    exact (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingEdge_eq_of_mem_left
      (Sum.inl y) hfStar hfLeft
  change Gs.right
      ((starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingEdge
        (Sum.inl x)) =
    Gs.right
      ((starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingEdge
        (Sum.inl y))
  rw [hPedge, hQedge]
  have hright : A.right e = A.right f := by
    simpa [IsPerfectMatching.matchingRight, e, f] using hxy
  by_cases her : A.right e = r
  · have hfr : A.right f = r := hright.symm.trans her
    have heq : e = (p i).1 :=
      (A.isMatching_iff PA).1 hPA.isMatching e hePA (p i).1 hPi (.inr r)
        (by simpa [Incident] using her) (by simp [Incident])
    have hfeq : f = (p i).1 :=
      (A.isMatching_iff QA).1 hQA.isMatching f hfQA (p i).1 hQi (.inr r)
        (by simpa [Incident] using hfr) (by simp [Incident])
    rw [heq, hfeq]
  · have hfr : A.right f ≠ r := by
      intro hf
      exact her (hright.trans hf)
    simp [Gs, starAEdge, her, hfr, hright]

/-- On the surviving `B`-left summand, common completion makes the two glued
matching-right maps literally agree. -/
theorem starGluedPM_matchingRight_inr_eq
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA QA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hQA : A.IsPerfectMatching QA)
    (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hQi : (p i).1 ∈ QA)
    (hBi : (q (σ i)).1 ∈ PB)
    (x : {x : XB // x ≠ ell}) :
    (starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingRight
        (Sum.inr x) =
      (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingRight
        (Sum.inr x) := by
  classical
  let Gs := A.starProduct B r ell p q σ
  let e := hPB.matchingEdge x.1
  have hePB : e ∈ PB := by simpa [e] using hPB.matchingEdge_mem x.1
  have heLeft0 : B.left e = x.1 := by simpa [e] using hPB.matchingEdge_left x.1
  have heNe : B.left e ≠ ell := by
    intro h
    exact x.2 (heLeft0.symm.trans h)
  have heStarP : A.starBEdge B r ell q σ e ∈
      A.starGluedMatching B r ell PA PB i :=
    (A.starBEdge_mem_starGluedMatching_iff B r ell q σ PA PB i hPB hBi e).2 hePB
  have heStarQ : A.starBEdge B r ell q σ e ∈
      A.starGluedMatching B r ell QA PB i :=
    (A.starBEdge_mem_starGluedMatching_iff B r ell q σ QA PB i hPB hBi e).2 hePB
  have heLeft : Gs.left (A.starBEdge B r ell q σ e) = Sum.inr x := by
    have hedge : A.starBEdge B r ell q σ e =
        (Sum.inr (Sum.inl ⟨e, heNe⟩) : StarEdge A B r ell) := by
      simp [starBEdge, heNe]
    rw [hedge]
    simp [Gs, heLeft0]
  have hPedge :
      (starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingEdge
          (Sum.inr x) = A.starBEdge B r ell q σ e := by
    exact (starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingEdge_eq_of_mem_left
      (Sum.inr x) heStarP heLeft
  have hQedge :
      (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingEdge
          (Sum.inr x) = A.starBEdge B r ell q σ e := by
    exact (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingEdge_eq_of_mem_left
      (Sum.inr x) heStarQ heLeft
  change Gs.right
      ((starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).property.matchingEdge
        (Sum.inr x)) =
    Gs.right
      ((starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).property.matchingEdge
        (Sum.inr x))
  rw [hPedge, hQedge]

/-- The relative permutation of two same-port/common-completion star matchings
is block diagonal: the source `A` relative permutation and an identity block. -/
theorem starGluedPM_relativePerm_eq_sumCongr
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA QA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hQA : A.IsPerfectMatching QA)
    (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hQi : (p i).1 ∈ QA)
    (hBi : (q (σ i)).1 ∈ PB) :
    ((starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).shoreEquiv.trans
        (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).shoreEquiv.symm :
      Equiv.Perm (StarLeft XA XB ell)) =
      Equiv.sumCongr
        (hPA.shoreEquiv.trans hQA.shoreEquiv.symm : Equiv.Perm XA)
        (Equiv.refl {x : XB // x ≠ ell}) := by
  classical
  let Pstar := starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi
  let Qstar := starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi
  ext z
  rcases z with x | x
  · apply Qstar.shoreEquiv.injective
    have hsrc : hPA.matchingRight x =
        hQA.matchingRight ((hPA.shoreEquiv.trans hQA.shoreEquiv.symm) x) := by
      change hPA.shoreEquiv x =
        hQA.shoreEquiv ((hPA.shoreEquiv.trans hQA.shoreEquiv.symm) x)
      simp
    have hstar := starGluedPM_matchingRight_inl_eq_of_source
      A B r ell p q σ PA QA PB i hPA hQA hPB hPi hQi hBi
      x ((hPA.shoreEquiv.trans hQA.shoreEquiv.symm) x) hsrc
    simpa [Pstar, Qstar, PerfectMatching.shoreEquiv_apply] using hstar
  · apply Qstar.shoreEquiv.injective
    have hstar := starGluedPM_matchingRight_inr_eq
      A B r ell p q σ PA QA PB i hPA hQA hPB hPi hQi hBi x
    simpa [Pstar, Qstar, PerfectMatching.shoreEquiv_apply] using hstar

/-- Consequently the relative permutation sign of the two glued matchings is
exactly the relative permutation sign of the varying `A`-factor matchings. -/
theorem starGluedPM_relativeSign_eq_source
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA QA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hQA : A.IsPerfectMatching QA)
    (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hQi : (p i).1 ∈ QA)
    (hBi : (q (σ i)).1 ∈ PB) :
    Equiv.Perm.sign
        ((starGluedPM A B r ell p q σ PA PB i hPA hPB hPi hBi).shoreEquiv.trans
          (starGluedPM A B r ell p q σ QA PB i hQA hPB hQi hBi).shoreEquiv.symm :
          Equiv.Perm (StarLeft XA XB ell)) =
      Equiv.Perm.sign
        (hPA.shoreEquiv.trans hQA.shoreEquiv.symm : Equiv.Perm XA) := by
  rw [starGluedPM_relativePerm_eq_sumCongr A B r ell p q σ
    PA QA PB i hPA hQA hPB hPi hQi hBi,
    Equiv.Perm.sign_sumCongr]
  simp

end BipartiteMultigraph
end BachThesisLean
