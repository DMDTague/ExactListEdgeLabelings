import BachThesisLean.Cubic.StarProductPfaffianRelative

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w uA vA wA uB vB wB

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-!
# Relative permutations for common-completion B-factor matchings

For the complementary factor it is cleaner to work on the right shore.  The
usual Pfaffian relative sign is defined on the left shore, but the analogous
right-shore relative permutation has the same sign.  With a common `A`
completion, the right-shore relative permutation of two glued matchings is
block diagonal: identity on the surviving `A`-right vertices and the full
`B` right-relative permutation on `YB`.
-/

/-- The right-shore relative permutation has the same sign as the usual
left-shore relative permutation. -/
theorem PerfectMatching.relativeRightSign_eq_relativeSign
    (P Q : G.PerfectMatching) :
    Equiv.Perm.sign
        (P.shoreEquiv.symm.trans Q.shoreEquiv : Equiv.Perm Y) =
      Equiv.Perm.sign
        (P.shoreEquiv.trans Q.shoreEquiv.symm : Equiv.Perm X) := by
  let L : Equiv.Perm X := P.shoreEquiv.trans Q.shoreEquiv.symm
  let R : Equiv.Perm Y := P.shoreEquiv.symm.trans Q.shoreEquiv
  have hconj : R = Q.shoreEquiv.permCongr L.symm := by
    ext y
    simp [L, R, Equiv.permCongr_def]
  change Equiv.Perm.sign R = Equiv.Perm.sign L
  rw [hconj, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_symm]

/-- Embed a `B`-left vertex into the star left shore.  The deleted root is
represented by the `A` endpoint of the selected bridge; every other `B`-left
vertex survives literally. -/
def starBLeftLift
    (A : BipartiteMultigraph XA YA EA) (r : YA) (ell : XB)
    (p : A.PortEnumeration (.inr r)) (i : Fin 3) (x : XB) :
    StarLeft XA XB ell :=
  if h : x = ell then .inl (A.left (p i).1) else .inr ⟨x, h⟩

/-- A glued matching sends the lifted `B`-left vertex to exactly the right
vertex selected by its source `B` matching.  This includes the deleted-root
case, where the selected source port is represented by the bridge. -/
theorem starGluedPM_matchingRight_starBLeftLift
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hAi : (p i).1 ∈ PA) (hBi : (q (σ i)).1 ∈ PB) (x : XB) :
    (starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hBi).property.matchingRight
        (starBLeftLift A r ell p i x) =
      Sum.inr (hPB.matchingRight x) := by
  classical
  let Gs := A.starProduct B r ell p q σ
  let e := hPB.matchingEdge x
  have hePB : e ∈ PB := by simpa [e] using hPB.matchingEdge_mem x
  have heLeft : B.left e = x := by simpa [e] using hPB.matchingEdge_left x
  have heStar : A.starBEdge B r ell q σ e ∈
      A.starGluedMatching B r ell PA PB i :=
    (A.starBEdge_mem_starGluedMatching_iff B r ell q σ PA PB i hPB hBi e).2 hePB
  have hleftStar :
      Gs.left (A.starBEdge B r ell q σ e) = starBLeftLift A r ell p i x := by
    by_cases hx : x = ell
    · have heroot : B.left e = ell := heLeft.trans hx
      have heq : e = (q (σ i)).1 :=
        (B.isMatching_iff PB).1 hPB.isMatching e hePB (q (σ i)).1 hBi (.inl ell)
          (by simpa [Incident] using heroot) (by simp [Incident])
      rw [heq]
      simp [Gs, starBLeftLift, hx]
    · have hene : B.left e ≠ ell := by simpa [heLeft] using hx
      simp [Gs, starBEdge, starBLeftLift, hx, hene, heLeft]
  have hedge :
      (starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hBi).property.matchingEdge
          (starBLeftLift A r ell p i x) = A.starBEdge B r ell q σ e := by
    exact (starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hBi).property.matchingEdge_eq_of_mem_left
      (starBLeftLift A r ell p i x) heStar hleftStar
  change Gs.right
      ((starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hBi).property.matchingEdge
        (starBLeftLift A r ell p i x)) = Sum.inr (B.right e)
  rw [hedge]
  exact A.starBEdge_right B r ell p q σ e

/-- At a surviving `A`-right vertex, a common `A` completion makes the inverse
shore map of the glued matching independent of the `B` matching. -/
theorem starGluedPM_shoreEquiv_symm_inl_of_commonA
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hAi : (p i).1 ∈ PA) (hBi : (q (σ i)).1 ∈ PB)
    (y : {y : YA // y ≠ r}) :
    (starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hBi).shoreEquiv.symm
        (Sum.inl y) = Sum.inl (hPA.shoreEquiv.symm y.1) := by
  classical
  let Pstar := starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hBi
  let x : XA := hPA.shoreEquiv.symm y.1
  let e := hPA.matchingEdge x
  have hePA : e ∈ PA := by simpa [e] using hPA.matchingEdge_mem x
  have heLeft0 : A.left e = x := by simpa [e] using hPA.matchingEdge_left x
  have heRight : A.right e = y.1 := by
    change hPA.matchingRight x = y.1
    change hPA.shoreEquiv x = y.1
    exact hPA.shoreEquiv.apply_symm_apply y.1
  have hene : A.right e ≠ r := by simpa [heRight] using y.2
  have heStar : A.starAEdge B r ell p e ∈
      A.starGluedMatching B r ell PA PB i :=
    (A.starAEdge_mem_starGluedMatching_iff B r ell p PA PB i hPA hAi e).2 hePA
  have heLeft :
      (A.starProduct B r ell p q σ).left (A.starAEdge B r ell p e) = Sum.inl x := by
    calc
      (A.starProduct B r ell p q σ).left (A.starAEdge B r ell p e) =
          Sum.inl (A.left e) := A.starAEdge_left B r ell p q σ e
      _ = Sum.inl x := congrArg Sum.inl heLeft0
  have hedge :
      Pstar.property.matchingEdge (Sum.inl x) = A.starAEdge B r ell p e := by
    exact Pstar.property.matchingEdge_eq_of_mem_left (Sum.inl x) heStar heLeft
  apply Pstar.shoreEquiv.injective
  rw [Pstar.shoreEquiv.apply_symm_apply]
  symm
  change Pstar.property.matchingRight (Sum.inl x) = Sum.inl y
  change (A.starProduct B r ell p q σ).right
      (Pstar.property.matchingEdge (Sum.inl x)) = Sum.inl y
  rw [hedge]
  simp [starAEdge, hene, heRight, y.2]

/-- The right-shore relative permutation of two same-port `B` matchings with a
common `A` completion is block diagonal. -/
theorem starGluedPM_relativeRightPerm_eq_sumCongr_sourceB
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB QB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hQB : B.IsPerfectMatching QB)
    (hAi : (p i).1 ∈ PA)
    (hPi : (q (σ i)).1 ∈ PB) (hQi : (q (σ i)).1 ∈ QB) :
    ((starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hPi).shoreEquiv.symm.trans
        (starGluedPM A B r ell p q σ PA QB i hPA hQB hAi hQi).shoreEquiv :
      Equiv.Perm (StarRight YA YB r)) =
      Equiv.sumCongr
        (Equiv.refl {y : YA // y ≠ r})
        (hPB.shoreEquiv.symm.trans hQB.shoreEquiv : Equiv.Perm YB) := by
  classical
  let Pstar := starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hPi
  let Qstar := starGluedPM A B r ell p q σ PA QB i hPA hQB hAi hQi
  ext z
  rcases z with y | y
  · have hpre := starGluedPM_shoreEquiv_symm_inl_of_commonA
      A B r ell p q σ PA PB i hPA hPB hAi hPi y
    have hQpre := starGluedPM_shoreEquiv_symm_inl_of_commonA
      A B r ell p q σ PA QB i hPA hQB hAi hQi y
    change Qstar.shoreEquiv (Pstar.shoreEquiv.symm (Sum.inl y)) = Sum.inl y
    rw [hpre]
    have h := congrArg Qstar.shoreEquiv hQpre
    simpa [Qstar] using h.symm
  · let x : XB := hPB.shoreEquiv.symm y
    have hPmap := starGluedPM_matchingRight_starBLeftLift
      A B r ell p q σ PA PB i hPA hPB hAi hPi x
    have hQmap := starGluedPM_matchingRight_starBLeftLift
      A B r ell p q σ PA QB i hPA hQB hAi hQi x
    have hPx : hPB.matchingRight x = y := by
      change hPB.shoreEquiv x = y
      exact hPB.shoreEquiv.apply_symm_apply y
    have hPpre : Pstar.shoreEquiv.symm (Sum.inr y) =
        starBLeftLift A r ell p i x := by
      apply Pstar.shoreEquiv.injective
      rw [Pstar.shoreEquiv.apply_symm_apply]
      change Sum.inr y =
        Pstar.property.matchingRight (starBLeftLift A r ell p i x)
      rw [← hPx]
      simpa [Pstar] using hPmap.symm
    change Qstar.shoreEquiv (Pstar.shoreEquiv.symm (Sum.inr y)) =
      Sum.inr ((hPB.shoreEquiv.symm.trans hQB.shoreEquiv) y)
    rw [hPpre]
    simpa [Qstar, PerfectMatching.shoreEquiv_apply, x] using hQmap

/-- Consequently the usual left-shore relative sign of the two glued matchings
is exactly the usual relative sign of the varying `B`-factor matchings. -/
theorem starGluedPM_relativeSign_eq_sourceB
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB QB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hQB : B.IsPerfectMatching QB)
    (hAi : (p i).1 ∈ PA)
    (hPi : (q (σ i)).1 ∈ PB) (hQi : (q (σ i)).1 ∈ QB) :
    Equiv.Perm.sign
        ((starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hPi).shoreEquiv.trans
          (starGluedPM A B r ell p q σ PA QB i hPA hQB hAi hQi).shoreEquiv.symm :
          Equiv.Perm (StarLeft XA XB ell)) =
      Equiv.Perm.sign
        (hPB.shoreEquiv.trans hQB.shoreEquiv.symm : Equiv.Perm XB) := by
  let Pstar := starGluedPM A B r ell p q σ PA PB i hPA hPB hAi hPi
  let Qstar := starGluedPM A B r ell p q σ PA QB i hPA hQB hAi hQi
  rw [← PerfectMatching.relativeRightSign_eq_relativeSign Pstar Qstar,
    starGluedPM_relativeRightPerm_eq_sumCongr_sourceB
      A B r ell p q σ PA PB QB i hPA hPB hQB hAi hPi hQi,
    Equiv.Perm.sign_sumCongr]
  simp only [Equiv.Perm.sign_refl, one_mul]
  let PBpm : B.PerfectMatching := ⟨PB, hPB⟩
  let QBpm : B.PerfectMatching := ⟨QB, hQB⟩
  simpa [PBpm, QBpm] using
    PerfectMatching.relativeRightSign_eq_relativeSign PBpm QBpm

end BipartiteMultigraph
end BachThesisLean
