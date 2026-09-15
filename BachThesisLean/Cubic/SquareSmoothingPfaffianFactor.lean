import BachThesisLean.Cubic.SquareSmoothing
import BachThesisLean.Cubic.OddPathSmoothing
import BachThesisLean.Cubic.EdgeRestriction

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : SquareFrame G)

/-!
# Factoring a square smoothing through odd-path smoothing

For either terminal pairing, delete the two square copies not used by that
pairing and keep every other old copy.  The resulting spanning restriction
contains two vertex-disjoint saturated odd three-edge paths.  Smoothing those
paths successively is the graph-theoretic factorization behind Pfaffian closure
of square smoothing.

This file establishes the spanning restriction and both odd-path frames.  It
deliberately makes no Pfaffian claim yet.
-/

/-- The spanning restriction used for one square pairing.  All non-square
copies survive, and in each square column `j` only the copy in row
`squarePair swap j` is retained. -/
noncomputable def pairingRestrictionEdges (swap : Bool) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    Q.OutsideSquare e ∨ ∃ j : Bool, e = Q.square (squarePair swap j) j

@[simp] theorem mem_pairingRestrictionEdges (swap : Bool) (e : E) :
    e ∈ Q.pairingRestrictionEdges swap ↔
      Q.OutsideSquare e ∨ ∃ j : Bool, e = Q.square (squarePair swap j) j := by
  classical
  simp [pairingRestrictionEdges]

/-- A square copy is retained exactly when its row is the row selected by the
pairing for its column. -/
theorem square_mem_pairingRestrictionEdges_iff
    (swap i j : Bool) :
    Q.square i j ∈ Q.pairingRestrictionEdges swap ↔
      i = squarePair swap j := by
  classical
  constructor
  · intro h
    rcases (Q.mem_pairingRestrictionEdges swap (Q.square i j)).1 h with
      hout | ⟨k, hk⟩
    · exact False.elim (hout i j rfl)
    · have hpairs : (i, j) = (squarePair swap k, k) :=
        Q.square_injective hk
      have hj : j = k := congrArg Prod.snd hpairs
      have hi : i = squarePair swap k := congrArg Prod.fst hpairs
      simpa [hj] using hi
  · intro hi
    apply (Q.mem_pairingRestrictionEdges swap (Q.square i j)).2
    right
    refine ⟨j, ?_⟩
    rw [hi]

/-- Every left spoke belongs to every pairing restriction. -/
theorem leftSpoke_mem_pairingRestrictionEdges (swap i : Bool) :
    Q.leftSpoke i ∈ Q.pairingRestrictionEdges swap := by
  apply (Q.mem_pairingRestrictionEdges swap (Q.leftSpoke i)).2
  left
  intro a b h
  exact Q.square_ne_leftSpoke a b i h.symm

/-- Every right spoke belongs to every pairing restriction. -/
theorem rightSpoke_mem_pairingRestrictionEdges (swap i : Bool) :
    Q.rightSpoke i ∈ Q.pairingRestrictionEdges swap := by
  apply (Q.mem_pairingRestrictionEdges swap (Q.rightSpoke i)).2
  left
  intro a b h
  exact Q.square_ne_rightSpoke a b i h.symm

/-- The two displayed left square vertices are indexed injectively by `Bool`. -/
theorem leftVertex_injective : Function.Injective Q.leftVertex := by
  intro i j h
  cases i <;> cases j
  · rfl
  · exact False.elim (Q.leftVertex_ne h)
  · exact False.elim (Q.leftVertex_ne h.symm)
  · rfl

/-- The two displayed right square vertices are indexed injectively by `Bool`. -/
theorem rightVertex_injective : Function.Injective Q.rightVertex := by
  intro i j h
  cases i <;> cases j
  · rfl
  · exact False.elim (Q.rightVertex_ne h)
  · exact False.elim (Q.rightVertex_ne h.symm)
  · rfl

/-- The pairing sends the two columns to distinct rows. -/
theorem squarePair_false_ne_true (swap : Bool) :
    squarePair swap false ≠ squarePair swap true := by
  intro h
  exact Bool.false_ne_true (squarePair_injective swap h)

/-- The first retained square path, indexed by column `false`, as a saturated
odd path in the spanning restriction.  Its endpoints are
`externalLeft false` and `externalRight (squarePair swap false)`. -/
noncomputable def firstPairingOddPathFrame (swap : Bool) :
    OddPathFrame (G.restrictEdges (Q.pairingRestrictionEdges swap)) := by
  classical
  let j : Bool := squarePair swap false
  let uz : {e : E // e ∈ Q.pairingRestrictionEdges swap} :=
    ⟨Q.rightSpoke false, Q.rightSpoke_mem_pairingRestrictionEdges swap false⟩
  let wz : {e : E // e ∈ Q.pairingRestrictionEdges swap} :=
    ⟨Q.square j false,
      (Q.square_mem_pairingRestrictionEdges_iff swap j false).2 rfl⟩
  let wv : {e : E // e ∈ Q.pairingRestrictionEdges swap} :=
    ⟨Q.leftSpoke j, Q.leftSpoke_mem_pairingRestrictionEdges swap j⟩
  refine
    { u := Q.externalLeft false
      z := Q.rightVertex false
      w := Q.leftVertex j
      v := Q.externalRight j
      uz := uz
      wz := wz
      wv := wv
      u_ne_w := Q.externalLeft_ne false j
      v_ne_z := Q.externalRight_ne j false
      uz_left := by
        change G.left (Q.rightSpoke false) = Q.externalLeft false
        exact Q.rightSpoke_left false
      uz_right := by
        change G.right (Q.rightSpoke false) = Q.rightVertex false
        exact Q.rightSpoke_right false
      wz_left := by
        change G.left (Q.square j false) = Q.leftVertex j
        exact Q.square_left j false
      wz_right := by
        change G.right (Q.square j false) = Q.rightVertex false
        exact Q.square_right j false
      wv_left := by
        change G.left (Q.leftSpoke j) = Q.leftVertex j
        exact Q.leftSpoke_left j
      wv_right := by
        change G.right (Q.leftSpoke j) = Q.externalRight j
        exact Q.leftSpoke_right j
      uz_ne_wz := by
        intro h
        have hval := congrArg Subtype.val h
        exact Q.square_ne_rightSpoke j false false hval.symm
      wz_ne_wv := by
        intro h
        have hval := congrArg Subtype.val h
        exact Q.square_ne_leftSpoke j false j hval
      uz_ne_wv := by
        intro h
        have hval := congrArg Subtype.val h
        exact Q.leftSpoke_ne_rightSpoke j false hval.symm
      z_saturated := by
        intro a ha
        change G.right a.val = Q.rightVertex false at ha
        rcases Q.right_saturated a.val false ha with h0 | h1 | hr
        · have hmem : Q.square false false ∈ Q.pairingRestrictionEdges swap := by
            simpa [h0] using a.property
          have hrow : false = squarePair swap false :=
            (Q.square_mem_pairingRestrictionEdges_iff swap false false).1 hmem
          right
          apply Subtype.ext
          change a.val = Q.square j false
          calc
            a.val = Q.square false false := h0
            _ = Q.square (squarePair swap false) false :=
              congrArg (fun r => Q.square r false) hrow
            _ = Q.square j false := rfl
        · have hmem : Q.square true false ∈ Q.pairingRestrictionEdges swap := by
            simpa [h1] using a.property
          have hrow : true = squarePair swap false :=
            (Q.square_mem_pairingRestrictionEdges_iff swap true false).1 hmem
          right
          apply Subtype.ext
          change a.val = Q.square j false
          calc
            a.val = Q.square true false := h1
            _ = Q.square (squarePair swap false) false :=
              congrArg (fun r => Q.square r false) hrow
            _ = Q.square j false := rfl
        · left
          apply Subtype.ext
          exact hr
      w_saturated := by
        intro a ha
        change G.left a.val = Q.leftVertex j at ha
        rcases Q.left_saturated a.val j ha with h0 | h1 | hl
        · left
          apply Subtype.ext
          exact h0
        · have hmem : Q.square j true ∈ Q.pairingRestrictionEdges swap := by
            simpa [h1] using a.property
          have hrow : j = squarePair swap true :=
            (Q.square_mem_pairingRestrictionEdges_iff swap j true).1 hmem
          have hp : squarePair swap false = squarePair swap true := by
            simpa [j] using hrow
          exact False.elim (Bool.false_ne_true (squarePair_injective swap hp))
        · right
          apply Subtype.ext
          exact hl }

/-- After smoothing the first retained square path, the path through the other
column remains a saturated odd path.  The first fresh smoothing edge cannot
meet either of its internal vertices because those vertices are still genuine
square vertices while the fresh endpoints are external square neighbours. -/
noncomputable def secondPairingOddPathFrame (swap : Bool) :
    OddPathFrame (Q.firstPairingOddPathFrame swap).smooth := by
  classical
  let F := Q.firstPairingOddPathFrame swap
  let j0 : Bool := squarePair swap false
  let j1 : Bool := squarePair swap true
  have hj01 : j0 ≠ j1 := by
    simpa [j0, j1] using squarePair_false_ne_true swap
  have hleft10 : Q.leftVertex j1 ≠ Q.leftVertex j0 := by
    intro h
    exact hj01 ((Q.leftVertex_injective) h).symm
  have hright10 : Q.rightVertex true ≠ Q.rightVertex false :=
    Q.rightVertex_ne.symm
  let uz0 : {e : E // e ∈ Q.pairingRestrictionEdges swap} :=
    ⟨Q.rightSpoke true, Q.rightSpoke_mem_pairingRestrictionEdges swap true⟩
  let wz0 : {e : E // e ∈ Q.pairingRestrictionEdges swap} :=
    ⟨Q.square j1 true,
      (Q.square_mem_pairingRestrictionEdges_iff swap j1 true).2 rfl⟩
  let wv0 : {e : E // e ∈ Q.pairingRestrictionEdges swap} :=
    ⟨Q.leftSpoke j1, Q.leftSpoke_mem_pairingRestrictionEdges swap j1⟩
  let uzS : F.Survivor := ⟨uz0, by
    constructor
    · change G.left (Q.rightSpoke true) ≠ Q.leftVertex j0
      simpa only [Q.rightSpoke_left] using Q.externalLeft_ne true j0
    · change G.right (Q.rightSpoke true) ≠ Q.rightVertex false
      simpa only [Q.rightSpoke_right] using hright10⟩
  let wzS : F.Survivor := ⟨wz0, by
    constructor
    · change G.left (Q.square j1 true) ≠ Q.leftVertex j0
      simpa only [Q.square_left] using hleft10
    · change G.right (Q.square j1 true) ≠ Q.rightVertex false
      simpa only [Q.square_right] using hright10⟩
  let wvS : F.Survivor := ⟨wv0, by
    constructor
    · change G.left (Q.leftSpoke j1) ≠ Q.leftVertex j0
      simpa only [Q.leftSpoke_left] using hleft10
    · change G.right (Q.leftSpoke j1) ≠ Q.rightVertex false
      simpa only [Q.leftSpoke_right] using Q.externalRight_ne j1 false⟩
  let uz : F.SmoothEdge := F.oldEdge uzS
  let wz : F.SmoothEdge := F.oldEdge wzS
  let wv : F.SmoothEdge := F.oldEdge wvS
  refine
    { u := ⟨Q.externalLeft true, Q.externalLeft_ne true j0⟩
      z := ⟨Q.rightVertex true, hright10⟩
      w := ⟨Q.leftVertex j1, hleft10⟩
      v := ⟨Q.externalRight j1, Q.externalRight_ne j1 false⟩
      uz := uz
      wz := wz
      wv := wv
      u_ne_w := by
        intro h
        exact Q.externalLeft_ne true j1 (congrArg Subtype.val h)
      v_ne_z := by
        intro h
        exact Q.externalRight_ne j1 true (congrArg Subtype.val h)
      uz_left := by
        apply Subtype.ext
        change G.left (Q.rightSpoke true) = Q.externalLeft true
        exact Q.rightSpoke_left true
      uz_right := by
        apply Subtype.ext
        change G.right (Q.rightSpoke true) = Q.rightVertex true
        exact Q.rightSpoke_right true
      wz_left := by
        apply Subtype.ext
        change G.left (Q.square j1 true) = Q.leftVertex j1
        exact Q.square_left j1 true
      wz_right := by
        apply Subtype.ext
        change G.right (Q.square j1 true) = Q.rightVertex true
        exact Q.square_right j1 true
      wv_left := by
        apply Subtype.ext
        change G.left (Q.leftSpoke j1) = Q.leftVertex j1
        exact Q.leftSpoke_left j1
      wv_right := by
        apply Subtype.ext
        change G.right (Q.leftSpoke j1) = Q.externalRight j1
        exact Q.leftSpoke_right j1
      uz_ne_wz := by
        intro h
        have hs : uzS = wzS := F.oldEdge_injective h
        have h0 : uz0 = wz0 := congrArg Subtype.val hs
        have hv := congrArg Subtype.val h0
        exact Q.square_ne_rightSpoke j1 true true hv.symm
      wz_ne_wv := by
        intro h
        have hs : wzS = wvS := F.oldEdge_injective h
        have h0 : wz0 = wv0 := congrArg Subtype.val hs
        have hv := congrArg Subtype.val h0
        exact Q.square_ne_leftSpoke j1 true j1 hv
      uz_ne_wv := by
        intro h
        have hs : uzS = wvS := F.oldEdge_injective h
        have h0 : uz0 = wv0 := congrArg Subtype.val hs
        have hv := congrArg Subtype.val h0
        exact Q.leftSpoke_ne_rightSpoke j1 true hv.symm
      z_saturated := by
        intro a ha
        cases a with
        | inr t =>
            have hv := congrArg Subtype.val ha
            change Q.externalRight j0 = Q.rightVertex true at hv
            exact False.elim (Q.externalRight_ne j0 true hv)
        | inl s =>
            have hg : G.right s.val.val = Q.rightVertex true := by
              have hv := congrArg Subtype.val ha
              change G.right s.val.val = Q.rightVertex true at hv
              exact hv
            rcases Q.right_saturated s.val.val true hg with h0 | h1 | hr
            · have hmem : Q.square false true ∈ Q.pairingRestrictionEdges swap := by
                simpa [h0] using s.val.property
              have hrow : false = j1 := by
                simpa [j1] using
                  (Q.square_mem_pairingRestrictionEdges_iff swap false true).1 hmem
              right
              change F.oldEdge s = F.oldEdge wzS
              apply congrArg F.oldEdge
              apply Subtype.ext
              apply Subtype.ext
              calc
                s.val.val = Q.square false true := h0
                _ = Q.square j1 true :=
                  congrArg (fun r => Q.square r true) hrow
            · have hmem : Q.square true true ∈ Q.pairingRestrictionEdges swap := by
                simpa [h1] using s.val.property
              have hrow : true = j1 := by
                simpa [j1] using
                  (Q.square_mem_pairingRestrictionEdges_iff swap true true).1 hmem
              right
              change F.oldEdge s = F.oldEdge wzS
              apply congrArg F.oldEdge
              apply Subtype.ext
              apply Subtype.ext
              calc
                s.val.val = Q.square true true := h1
                _ = Q.square j1 true :=
                  congrArg (fun r => Q.square r true) hrow
            · left
              change F.oldEdge s = F.oldEdge uzS
              apply congrArg F.oldEdge
              apply Subtype.ext
              apply Subtype.ext
              exact hr
      w_saturated := by
        intro a ha
        cases a with
        | inr t =>
            have hv := congrArg Subtype.val ha
            change Q.externalLeft false = Q.leftVertex j1 at hv
            exact False.elim (Q.externalLeft_ne false j1 hv)
        | inl s =>
            have hg : G.left s.val.val = Q.leftVertex j1 := by
              have hv := congrArg Subtype.val ha
              change G.left s.val.val = Q.leftVertex j1 at hv
              exact hv
            rcases Q.left_saturated s.val.val j1 hg with h0 | h1 | hl
            · have hmem : Q.square j1 false ∈ Q.pairingRestrictionEdges swap := by
                simpa [h0] using s.val.property
              have hrow : j1 = j0 := by
                have :=
                  (Q.square_mem_pairingRestrictionEdges_iff swap j1 false).1 hmem
                simpa [j0] using this
              exact False.elim (hj01 hrow.symm)
            · left
              change F.oldEdge s = F.oldEdge wzS
              apply congrArg F.oldEdge
              apply Subtype.ext
              apply Subtype.ext
              exact h1
            · right
              change F.oldEdge s = F.oldEdge wvS
              apply congrArg F.oldEdge
              apply Subtype.ext
              apply Subtype.ext
              exact hl }

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
