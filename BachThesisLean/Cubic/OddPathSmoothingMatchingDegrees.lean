import BachThesisLean.Cubic.OddPathSmoothingMatching

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Matching degrees through odd-path smoothing

At surviving vertices the left/right recovery maps identify selected
incidences bijectively.  At the two deleted internal vertices the lift selects
exactly one local path copy in either fresh-edge state.  Together these facts
show that every perfect matching of the smoothing lifts to a perfect matching
of the original graph.
-/

/-- Selected incidences at a surviving left vertex are transported exactly by
`recoverLeft`. -/
theorem recoverLeft_selectedIncident_image
    (S : Finset Q.SmoothEdge) (x : Q.ReducedLeft) :
    ((Q.smooth.selectedIncident S (.inl x)).image Q.recoverLeft) =
      G.selectedIncident (Q.liftMatchingSet S) (.inl x.val) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
    have ha' := (Q.smooth.mem_selectedIncident S (.inl x) a).1 ha
    have hmem : Q.recoverLeft a ∈ Q.liftMatchingSet S :=
      (Q.recoverLeft_mem_liftMatchingSet_iff S a).2 ha'.1
    have hax : Q.smooth.left a = x := by
      simpa [Incident] using ha'.2
    have hinc : G.Incident (Q.recoverLeft a) (.inl x.val) := by
      change G.left (Q.recoverLeft a) = x.val
      exact (Q.recoverLeft_left a).trans (congrArg Subtype.val hax)
    have hsel :=
      (G.mem_selectedIncident (Q.liftMatchingSet S) (.inl x.val)
        (Q.recoverLeft a)).2 ⟨hmem, hinc⟩
    simpa [hae] using hsel
  · intro he
    have he' :=
      (G.mem_selectedIncident (Q.liftMatchingSet S) (.inl x.val) e).1 he
    have hleft : G.left e = x.val := by simpa [Incident] using he'.2
    rw [Q.mem_liftMatchingSet S e] at he'
    rcases he'.1 with hold | huz | hwv | hwz
    · obtain ⟨hsurv, heS⟩ := hold
      let a : Q.Survivor := ⟨e, hsurv⟩
      refine Finset.mem_image.mpr ⟨Q.oldEdge a, ?_, rfl⟩
      apply (Q.smooth.mem_selectedIncident S (.inl x) (Q.oldEdge a)).2
      refine ⟨heS, ?_⟩
      change Q.smooth.left (Q.oldEdge a) = x
      apply Subtype.ext
      exact hleft
    · rcases huz with ⟨rfl, hfresh⟩
      refine Finset.mem_image.mpr ⟨Q.freshEdge, ?_, rfl⟩
      apply (Q.smooth.mem_selectedIncident S (.inl x) Q.freshEdge).2
      refine ⟨hfresh, ?_⟩
      change Q.smooth.left Q.freshEdge = x
      apply Subtype.ext
      exact Q.uz_left.symm.trans hleft
    · rcases hwv with ⟨rfl, _⟩
      exact False.elim (x.property (Q.wv_left.symm.trans hleft).symm)
    · rcases hwz with ⟨rfl, _⟩
      exact False.elim (x.property (Q.wz_left.symm.trans hleft).symm)

/-- Selected incidences at a surviving right vertex are transported exactly by
`recoverRight`. -/
theorem recoverRight_selectedIncident_image
    (S : Finset Q.SmoothEdge) (y : Q.ReducedRight) :
    ((Q.smooth.selectedIncident S (.inr y)).image Q.recoverRight) =
      G.selectedIncident (Q.liftMatchingSet S) (.inr y.val) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
    have ha' := (Q.smooth.mem_selectedIncident S (.inr y) a).1 ha
    have hmem : Q.recoverRight a ∈ Q.liftMatchingSet S :=
      (Q.recoverRight_mem_liftMatchingSet_iff S a).2 ha'.1
    have hay : Q.smooth.right a = y := by
      simpa [Incident] using ha'.2
    have hinc : G.Incident (Q.recoverRight a) (.inr y.val) := by
      change G.right (Q.recoverRight a) = y.val
      exact (Q.recoverRight_right a).trans (congrArg Subtype.val hay)
    have hsel :=
      (G.mem_selectedIncident (Q.liftMatchingSet S) (.inr y.val)
        (Q.recoverRight a)).2 ⟨hmem, hinc⟩
    simpa [hae] using hsel
  · intro he
    have he' :=
      (G.mem_selectedIncident (Q.liftMatchingSet S) (.inr y.val) e).1 he
    have hright : G.right e = y.val := by simpa [Incident] using he'.2
    rw [Q.mem_liftMatchingSet S e] at he'
    rcases he'.1 with hold | huz | hwv | hwz
    · obtain ⟨hsurv, heS⟩ := hold
      let a : Q.Survivor := ⟨e, hsurv⟩
      refine Finset.mem_image.mpr ⟨Q.oldEdge a, ?_, rfl⟩
      apply (Q.smooth.mem_selectedIncident S (.inr y) (Q.oldEdge a)).2
      refine ⟨heS, ?_⟩
      change Q.smooth.right (Q.oldEdge a) = y
      apply Subtype.ext
      exact hright
    · rcases huz with ⟨rfl, _⟩
      exact False.elim (y.property (Q.uz_right.symm.trans hright).symm)
    · rcases hwv with ⟨rfl, hfresh⟩
      refine Finset.mem_image.mpr ⟨Q.freshEdge, ?_, rfl⟩
      apply (Q.smooth.mem_selectedIncident S (.inr y) Q.freshEdge).2
      refine ⟨hfresh, ?_⟩
      change Q.smooth.right Q.freshEdge = y
      apply Subtype.ext
      exact Q.wv_right.symm.trans hright
    · rcases hwz with ⟨rfl, _⟩
      exact False.elim (y.property (Q.wz_right.symm.trans hright).symm)

/-- Selected degree is preserved at every surviving left vertex. -/
theorem liftMatchingSet_selectedIncident_left_card
    (S : Finset Q.SmoothEdge) (x : Q.ReducedLeft) :
    (G.selectedIncident (Q.liftMatchingSet S) (.inl x.val)).card =
      (Q.smooth.selectedIncident S (.inl x)).card := by
  have h := congrArg Finset.card (Q.recoverLeft_selectedIncident_image S x)
  rw [Finset.card_image_of_injective _ Q.recoverLeft_injective] at h
  exact h.symm

/-- Selected degree is preserved at every surviving right vertex. -/
theorem liftMatchingSet_selectedIncident_right_card
    (S : Finset Q.SmoothEdge) (y : Q.ReducedRight) :
    (G.selectedIncident (Q.liftMatchingSet S) (.inr y.val)).card =
      (Q.smooth.selectedIncident S (.inr y)).card := by
  have h := congrArg Finset.card (Q.recoverRight_selectedIncident_image S y)
  rw [Finset.card_image_of_injective _ Q.recoverRight_injective] at h
  exact h.symm

/-- At the deleted left internal vertex `w`, the lifted set always selects
exactly one path copy. -/
theorem liftMatchingSet_selectedIncident_w_card
    (S : Finset Q.SmoothEdge) :
    (G.selectedIncident (Q.liftMatchingSet S) (.inl Q.w)).card = 1 := by
  classical
  by_cases hfresh : Q.freshSelected S
  · have hset :
        G.selectedIncident (Q.liftMatchingSet S) (.inl Q.w) = {Q.wv} := by
      ext e
      constructor
      · intro he
        have he' := (G.mem_selectedIncident (Q.liftMatchingSet S) (.inl Q.w) e).1 he
        have hleft : G.left e = Q.w := by simpa [Incident] using he'.2
        rw [Q.mem_liftMatchingSet S e] at he'
        rcases he'.1 with hold | huz | hwv | hwz
        · obtain ⟨hsurv, _⟩ := hold
          exact False.elim (hsurv.1 hleft)
        · rcases huz with ⟨rfl, _⟩
          exact False.elim (Q.u_ne_w (Q.uz_left.symm.trans hleft))
        · simpa [hwv.1]
        · exact False.elim (hwz.2 hfresh)
      · intro he
        have heq : e = Q.wv := by simpa using he
        subst e
        apply (G.mem_selectedIncident (Q.liftMatchingSet S) (.inl Q.w) Q.wv).2
        exact ⟨(Q.mem_liftMatchingSet_wv S).2 hfresh, by simpa [Incident] using Q.wv_left⟩
    rw [hset]
    simp
  · have hset :
        G.selectedIncident (Q.liftMatchingSet S) (.inl Q.w) = {Q.wz} := by
      ext e
      constructor
      · intro he
        have he' := (G.mem_selectedIncident (Q.liftMatchingSet S) (.inl Q.w) e).1 he
        have hleft : G.left e = Q.w := by simpa [Incident] using he'.2
        rw [Q.mem_liftMatchingSet S e] at he'
        rcases he'.1 with hold | huz | hwv | hwz
        · obtain ⟨hsurv, _⟩ := hold
          exact False.elim (hsurv.1 hleft)
        · rcases huz with ⟨rfl, _⟩
          exact False.elim (Q.u_ne_w (Q.uz_left.symm.trans hleft))
        · exact False.elim (hfresh hwv.2)
        · simpa [hwz.1]
      · intro he
        have heq : e = Q.wz := by simpa using he
        subst e
        apply (G.mem_selectedIncident (Q.liftMatchingSet S) (.inl Q.w) Q.wz).2
        exact ⟨(Q.mem_liftMatchingSet_wz S).2 hfresh, by simpa [Incident] using Q.wz_left⟩
    rw [hset]
    simp

/-- At the deleted right internal vertex `z`, the lifted set likewise selects
exactly one path copy. -/
theorem liftMatchingSet_selectedIncident_z_card
    (S : Finset Q.SmoothEdge) :
    (G.selectedIncident (Q.liftMatchingSet S) (.inr Q.z)).card = 1 := by
  classical
  by_cases hfresh : Q.freshSelected S
  · have hset :
        G.selectedIncident (Q.liftMatchingSet S) (.inr Q.z) = {Q.uz} := by
      ext e
      constructor
      · intro he
        have he' := (G.mem_selectedIncident (Q.liftMatchingSet S) (.inr Q.z) e).1 he
        have hright : G.right e = Q.z := by simpa [Incident] using he'.2
        rw [Q.mem_liftMatchingSet S e] at he'
        rcases he'.1 with hold | huz | hwv | hwz
        · obtain ⟨hsurv, _⟩ := hold
          exact False.elim (hsurv.2 hright)
        · simpa [huz.1]
        · rcases hwv with ⟨rfl, _⟩
          exact False.elim (Q.v_ne_z (Q.wv_right.symm.trans hright))
        · exact False.elim (hwz.2 hfresh)
      · intro he
        have heq : e = Q.uz := by simpa using he
        subst e
        apply (G.mem_selectedIncident (Q.liftMatchingSet S) (.inr Q.z) Q.uz).2
        exact ⟨(Q.mem_liftMatchingSet_uz S).2 hfresh, by simpa [Incident] using Q.uz_right⟩
    rw [hset]
    simp
  · have hset :
        G.selectedIncident (Q.liftMatchingSet S) (.inr Q.z) = {Q.wz} := by
      ext e
      constructor
      · intro he
        have he' := (G.mem_selectedIncident (Q.liftMatchingSet S) (.inr Q.z) e).1 he
        have hright : G.right e = Q.z := by simpa [Incident] using he'.2
        rw [Q.mem_liftMatchingSet S e] at he'
        rcases he'.1 with hold | huz | hwv | hwz
        · obtain ⟨hsurv, _⟩ := hold
          exact False.elim (hsurv.2 hright)
        · exact False.elim (hfresh huz.2)
        · rcases hwv with ⟨rfl, _⟩
          exact False.elim (Q.v_ne_z (Q.wv_right.symm.trans hright))
        · simpa [hwz.1]
      · intro he
        have heq : e = Q.wz := by simpa using he
        subst e
        apply (G.mem_selectedIncident (Q.liftMatchingSet S) (.inr Q.z) Q.wz).2
        exact ⟨(Q.mem_liftMatchingSet_wz S).2 hfresh, by simpa [Incident] using Q.wz_right⟩
    rw [hset]
    simp

/-- Every perfect matching of the smoothed graph lifts to a perfect matching of
the original graph. -/
theorem IsPerfectMatching.lift_oddPath
    (S : Finset Q.SmoothEdge) (hS : Q.smooth.IsPerfectMatching S) :
    G.IsPerfectMatching (Q.liftMatchingSet S) := by
  intro p
  rcases p with x | y
  · by_cases hx : x = Q.w
    · subst x
      exact Q.liftMatchingSet_selectedIncident_w_card S
    · let xr : Q.ReducedLeft := ⟨x, hx⟩
      calc
        (G.selectedIncident (Q.liftMatchingSet S) (.inl x)).card =
            (Q.smooth.selectedIncident S (.inl xr)).card := by
              simpa [xr] using Q.liftMatchingSet_selectedIncident_left_card S xr
        _ = 1 := hS (.inl xr)
  · by_cases hy : y = Q.z
    · subst y
      exact Q.liftMatchingSet_selectedIncident_z_card S
    · let yr : Q.ReducedRight := ⟨y, hy⟩
      calc
        (G.selectedIncident (Q.liftMatchingSet S) (.inr y)).card =
            (Q.smooth.selectedIncident S (.inr yr)).card := by
              simpa [yr] using Q.liftMatchingSet_selectedIncident_right_card S yr
        _ = 1 := hS (.inr yr)

/-- Subtype-facing perfect-matching lift used by the Pfaffian term comparison. -/
noncomputable def PerfectMatching.lift_oddPath
    (P : Q.smooth.PerfectMatching) : G.PerfectMatching :=
  ⟨Q.liftMatchingSet P.val,
    BachThesisLean.BipartiteMultigraph.OddPathFrame.IsPerfectMatching.lift_oddPath
      Q P.val P.property⟩

@[simp] theorem PerfectMatching.lift_oddPath_val
    (P : Q.smooth.PerfectMatching) :
    (PerfectMatching.lift_oddPath Q P).val = Q.liftMatchingSet P.val := rfl

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
