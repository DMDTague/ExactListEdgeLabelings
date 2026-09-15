import BachThesisLean.Cubic.OddPathSmoothingMatchingDegrees
import BachThesisLean.Cubic.OddPathSmoothingReference

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Shore maps through odd-path smoothing

The Pfaffian smoothing calculation needs the exact permutation represented by
the lifted matching.  Rather than hiding this in a determinant-sign proof, we
record the edge-copy statement first.  At a surviving left vertex, the lifted
matching edge is exactly `recoverLeft` applied to the smooth matching edge.  At
the deleted left vertex `w`, the selected copy is `wv` when the fresh edge is
selected and `wz` otherwise.
-/

/-- At every surviving left vertex, the chosen edge of the lifted perfect
matching is the left-recovery of the chosen smooth matching edge. -/
theorem PerfectMatching.lift_oddPath_matchingEdge_reduced
    (P : Q.smooth.PerfectMatching) (x : Q.ReducedLeft) :
    (PerfectMatching.lift_oddPath Q P).property.matchingEdge x.val =
      Q.recoverLeft (P.property.matchingEdge x) := by
  let a : Q.SmoothEdge := P.property.matchingEdge x
  have haP : a ∈ P.val := by
    simpa [a] using P.property.matchingEdge_mem x
  have haLift : Q.recoverLeft a ∈ Q.liftMatchingSet P.val :=
    (Q.recoverLeft_mem_liftMatchingSet_iff P.val a).2 haP
  have haLeftSmooth : Q.smooth.left a = x := by
    simpa [a] using P.property.matchingEdge_left x
  have haLeft : G.left (Q.recoverLeft a) = x.val := by
    exact (Q.recoverLeft_left a).trans (congrArg Subtype.val haLeftSmooth)
  exact (PerfectMatching.lift_oddPath Q P).property.matchingEdge_eq_of_mem_left
    x.val haLift haLeft

/-- Consequently the lifted right partner of a surviving left vertex is read
from the recovered actual edge copy.  This deliberately keeps the fresh-edge
case explicit: when the fresh copy is selected at `u`, its left recovery is
`uz`, whose old right endpoint is the deleted vertex `z`. -/
theorem PerfectMatching.lift_oddPath_matchingRight_reduced
    (P : Q.smooth.PerfectMatching) (x : Q.ReducedLeft) :
    (PerfectMatching.lift_oddPath Q P).property.matchingRight x.val =
      G.right (Q.recoverLeft (P.property.matchingEdge x)) := by
  change G.right ((PerfectMatching.lift_oddPath Q P).property.matchingEdge x.val) = _
  rw [PerfectMatching.lift_oddPath_matchingEdge_reduced Q P x]

/-- If the fresh smoothing edge is selected, the deleted left vertex `w` is
matched along the last path copy `wv`. -/
theorem PerfectMatching.lift_oddPath_matchingEdge_w_of_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).property.matchingEdge Q.w = Q.wv := by
  have hwvP : Q.wv ∈ Q.liftMatchingSet P.val :=
    (Q.mem_liftMatchingSet_wv P.val).2 hfresh
  exact (PerfectMatching.lift_oddPath Q P).property.matchingEdge_eq_of_mem_left
    Q.w hwvP Q.wv_left

/-- If the fresh smoothing edge is not selected, the deleted left vertex `w`
is matched along the middle path copy `wz`. -/
theorem PerfectMatching.lift_oddPath_matchingEdge_w_of_not_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : ¬ Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).property.matchingEdge Q.w = Q.wz := by
  have hwzP : Q.wz ∈ Q.liftMatchingSet P.val :=
    (Q.mem_liftMatchingSet_wz P.val).2 hfresh
  exact (PerfectMatching.lift_oddPath Q P).property.matchingEdge_eq_of_mem_left
    Q.w hwzP Q.wz_left

/-- Fresh state: the lifted matching sends the deleted left vertex to `v`. -/
theorem PerfectMatching.lift_oddPath_matchingRight_w_of_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).property.matchingRight Q.w = Q.v := by
  change G.right ((PerfectMatching.lift_oddPath Q P).property.matchingEdge Q.w) = Q.v
  rw [PerfectMatching.lift_oddPath_matchingEdge_w_of_fresh Q P hfresh]
  exact Q.wv_right

/-- Non-fresh state: the lifted matching sends the deleted left vertex to `z`. -/
theorem PerfectMatching.lift_oddPath_matchingRight_w_of_not_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : ¬ Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).property.matchingRight Q.w = Q.z := by
  change G.right ((PerfectMatching.lift_oddPath Q P).property.matchingEdge Q.w) = Q.z
  rw [PerfectMatching.lift_oddPath_matchingEdge_w_of_not_fresh Q P hfresh]
  exact Q.wz_right

/-- Away from the fresh local state, left recovery preserves the matched right
partner of every surviving left vertex. -/
theorem PerfectMatching.lift_oddPath_matchingRight_reduced_of_not_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : ¬ Q.freshSelected P.val)
    (x : Q.ReducedLeft) :
    (PerfectMatching.lift_oddPath Q P).property.matchingRight x.val =
      (P.property.matchingRight x).val := by
  rw [PerfectMatching.lift_oddPath_matchingRight_reduced Q P x]
  let a : Q.SmoothEdge := P.property.matchingEdge x
  have haP : a ∈ P.val := by
    simpa [a] using P.property.matchingEdge_mem x
  change G.right (Q.recoverLeft a) = (Q.smooth.right a).val
  rcases a with a | unit
  · rfl
  · cases unit
    exact False.elim (hfresh (by simpa [freshSelected, freshEdge] using haP))

/-- In the non-fresh state the ambient matching equivalence is exactly the
canonical extension of the smooth matching equivalence by `w ↦ z`. -/
theorem PerfectMatching.lift_oddPath_shoreEquiv_of_not_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : ¬ Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).shoreEquiv = Q.extendReducedEquiv P.shoreEquiv := by
  ext x
  by_cases hx : x = Q.w
  · subst x
    change (PerfectMatching.lift_oddPath Q P).property.matchingRight Q.w =
      Q.extendReducedEquiv P.shoreEquiv Q.w
    rw [PerfectMatching.lift_oddPath_matchingRight_w_of_not_fresh Q P hfresh]
    simp
  · let xr : Q.ReducedLeft := ⟨x, hx⟩
    change (PerfectMatching.lift_oddPath Q P).property.matchingRight x =
      Q.extendReducedEquiv P.shoreEquiv x
    rw [show x = xr.val by rfl,
      PerfectMatching.lift_oddPath_matchingRight_reduced_of_not_fresh Q P hfresh xr]
    simpa [xr] using
      (Q.extendReducedEquiv_apply_reduced P.shoreEquiv xr).symm

/-- In the fresh state the smooth matching edge at the surviving vertex `u`
is exactly the tagged fresh copy. -/
theorem PerfectMatching.matchingEdge_u_of_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val) :
    P.property.matchingEdge (⟨Q.u, Q.u_ne_w⟩ : Q.ReducedLeft) = Q.freshEdge := by
  exact P.property.matchingEdge_eq_of_mem_left
    (⟨Q.u, Q.u_ne_w⟩ : Q.ReducedLeft) hfresh rfl

/-- Hence in the fresh state the lifted matching sends the surviving old
vertex `u` to the deleted right vertex `z`. -/
theorem PerfectMatching.lift_oddPath_matchingRight_u_of_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).property.matchingRight Q.u = Q.z := by
  let ur : Q.ReducedLeft := ⟨Q.u, Q.u_ne_w⟩
  rw [show Q.u = ur.val by rfl,
    PerfectMatching.lift_oddPath_matchingRight_reduced Q P ur]
  have huEdge : P.property.matchingEdge ur = Q.freshEdge := by
    simpa [ur] using PerfectMatching.matchingEdge_u_of_fresh Q P hfresh
  rw [huEdge]
  exact Q.uz_right

/-- In the fresh state, every surviving left vertex other than `u` retains its
smooth matched right partner. -/
theorem PerfectMatching.lift_oddPath_matchingRight_reduced_of_fresh_of_ne_u
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val)
    (x : Q.ReducedLeft) (hxu : x.val ≠ Q.u) :
    (PerfectMatching.lift_oddPath Q P).property.matchingRight x.val =
      (P.property.matchingRight x).val := by
  rw [PerfectMatching.lift_oddPath_matchingRight_reduced Q P x]
  let a : Q.SmoothEdge := P.property.matchingEdge x
  have haLeft : Q.smooth.left a = x := by
    simpa [a] using P.property.matchingEdge_left x
  change G.right (Q.recoverLeft a) = (Q.smooth.right a).val
  rcases a with a | unit
  · rfl
  · cases unit
    exfalso
    apply hxu
    have hsub := congrArg Subtype.val haLeft
    simpa using hsub.symm

/-- In the fresh state the ambient matching equivalence differs from the
canonical extension by exactly the transposition exchanging the two left
vertices `u` and `w`. -/
theorem PerfectMatching.lift_oddPath_shoreEquiv_of_fresh
    (P : Q.smooth.PerfectMatching) (hfresh : Q.freshSelected P.val) :
    (PerfectMatching.lift_oddPath Q P).shoreEquiv =
      (Equiv.swap Q.u Q.w).trans (Q.extendReducedEquiv P.shoreEquiv) := by
  ext x
  by_cases hxw : x = Q.w
  · subst x
    change (PerfectMatching.lift_oddPath Q P).property.matchingRight Q.w =
      ((Equiv.swap Q.u Q.w).trans (Q.extendReducedEquiv P.shoreEquiv)) Q.w
    rw [PerfectMatching.lift_oddPath_matchingRight_w_of_fresh Q P hfresh]
    let ur : Q.ReducedLeft := ⟨Q.u, Q.u_ne_w⟩
    have huRight :
        P.property.matchingRight ur =
          (⟨Q.v, Q.v_ne_z⟩ : Q.ReducedRight) := by
      change Q.smooth.right (P.property.matchingEdge ur) = _
      rw [PerfectMatching.matchingEdge_u_of_fresh Q P hfresh]
      rfl
    have hswap : Equiv.swap Q.u Q.w Q.w = Q.u := by
      rw [Equiv.swap_apply_def]
      simp [Q.u_ne_w]
    rw [Equiv.trans_apply, hswap]
    have hext :
        Q.extendReducedEquiv P.shoreEquiv Q.u =
          (P.shoreEquiv ur).val := by
      simpa [ur] using Q.extendReducedEquiv_apply_reduced P.shoreEquiv ur
    rw [hext]
    change Q.v = (P.property.matchingRight ur).val
    exact (congrArg Subtype.val huRight).symm
  · by_cases hxu : x = Q.u
    · subst x
      change (PerfectMatching.lift_oddPath Q P).property.matchingRight Q.u =
        ((Equiv.swap Q.u Q.w).trans (Q.extendReducedEquiv P.shoreEquiv)) Q.u
      rw [PerfectMatching.lift_oddPath_matchingRight_u_of_fresh Q P hfresh]
      simp [Q.u_ne_w]
    · let xr : Q.ReducedLeft := ⟨x, hxw⟩
      change (PerfectMatching.lift_oddPath Q P).property.matchingRight x =
        ((Equiv.swap Q.u Q.w).trans (Q.extendReducedEquiv P.shoreEquiv)) x
      rw [show x = xr.val by rfl,
        PerfectMatching.lift_oddPath_matchingRight_reduced_of_fresh_of_ne_u
          Q P hfresh xr hxu]
      have hswap : Equiv.swap Q.u Q.w x = x := by
        rw [Equiv.swap_apply_def]
        simp [hxu, hxw]
      rw [Equiv.trans_apply, hswap]
      simpa [xr] using
        (Q.extendReducedEquiv_apply_reduced P.shoreEquiv xr).symm

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
