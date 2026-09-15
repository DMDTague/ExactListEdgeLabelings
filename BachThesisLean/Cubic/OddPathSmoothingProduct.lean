import BachThesisLean.Cubic.OddPathSmoothingPermutation
import Mathlib.Data.Int.Order.Units

namespace BachThesisLean
namespace BipartiteMultigraph
namespace OddPathFrame

open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E} (Q : OddPathFrame G)

/-!
# Edge products through odd-path smoothing

The lifted matching consists of the left-recovered selected smooth copies plus
one additional old path copy.  In the fresh state that additional copy is
`wv`; in the non-fresh state it is `wz`.  These exact finite-set identities are
the bookkeeping input for the Pfaffian signing product calculation.
-/

/-- Left recovery as an embedding of actual edge copies. -/
def recoverLeftEmbedding : Q.SmoothEdge ↪ E :=
  ⟨Q.recoverLeft, Q.recoverLeft_injective⟩

@[simp] theorem recoverLeftEmbedding_apply (a : Q.SmoothEdge) :
    Q.recoverLeftEmbedding a = Q.recoverLeft a := rfl

/-- `wv` never occurs in the image of left recovery. -/
theorem wv_not_mem_map_recoverLeft (S : Finset Q.SmoothEdge) :
    Q.wv ∉ S.map Q.recoverLeftEmbedding := by
  intro h
  obtain ⟨a, haS, ha⟩ := Finset.mem_map.mp h
  change Q.recoverLeft a = Q.wv at ha
  rcases a with a | unit
  · have hs := a.property
    change a.val = Q.wv at ha
    rw [ha] at hs
    exact Q.wv_not_survives hs
  · cases unit
    exact Q.uz_ne_wv ha

/-- `wz` likewise never occurs in the image of left recovery. -/
theorem wz_not_mem_map_recoverLeft (S : Finset Q.SmoothEdge) :
    Q.wz ∉ S.map Q.recoverLeftEmbedding := by
  intro h
  obtain ⟨a, haS, ha⟩ := Finset.mem_map.mp h
  change Q.recoverLeft a = Q.wz at ha
  rcases a with a | unit
  · have hs := a.property
    change a.val = Q.wz at ha
    rw [ha] at hs
    exact Q.wz_not_survives hs
  · cases unit
    exact Q.uz_ne_wz ha

/-- Fresh state: lift the selected copies by left recovery and add `wv`. -/
theorem liftMatchingSet_eq_map_recoverLeft_insert_wv
    (S : Finset Q.SmoothEdge) (hfresh : Q.freshSelected S) :
    Q.liftMatchingSet S = insert Q.wv (S.map Q.recoverLeftEmbedding) := by
  classical
  ext e
  constructor
  · intro he
    rw [Q.mem_liftMatchingSet S e] at he
    rcases he with hold | huz | hwv | hwz
    · obtain ⟨hsurv, heS⟩ := hold
      apply Finset.mem_insert_of_mem
      apply Finset.mem_map.mpr
      refine ⟨Q.oldEdge ⟨e, hsurv⟩, heS, ?_⟩
      rfl
    · rcases huz with ⟨rfl, -⟩
      apply Finset.mem_insert_of_mem
      apply Finset.mem_map.mpr
      refine ⟨Q.freshEdge, hfresh, ?_⟩
      rfl
    · exact Finset.mem_insert.mpr (Or.inl hwv.1)
    · exact False.elim (hwz.2 hfresh)
  · intro he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · exact (Q.mem_liftMatchingSet_wv S).2 hfresh
    · obtain ⟨a, haS, hae⟩ := Finset.mem_map.mp he
      change Q.recoverLeft a = e at hae
      rw [← hae]
      exact (Q.recoverLeft_mem_liftMatchingSet_iff S a).2 haS

/-- Non-fresh state: lift the selected copies by left recovery and add `wz`. -/
theorem liftMatchingSet_eq_map_recoverLeft_insert_wz
    (S : Finset Q.SmoothEdge) (hfresh : ¬ Q.freshSelected S) :
    Q.liftMatchingSet S = insert Q.wz (S.map Q.recoverLeftEmbedding) := by
  classical
  ext e
  constructor
  · intro he
    rw [Q.mem_liftMatchingSet S e] at he
    rcases he with hold | huz | hwv | hwz
    · obtain ⟨hsurv, heS⟩ := hold
      apply Finset.mem_insert_of_mem
      apply Finset.mem_map.mpr
      refine ⟨Q.oldEdge ⟨e, hsurv⟩, heS, ?_⟩
      rfl
    · exact False.elim (hfresh huz.2)
    · exact False.elim (hfresh hwv.2)
    · exact Finset.mem_insert.mpr (Or.inl hwz.1)
  · intro he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · exact (Q.mem_liftMatchingSet_wz S).2 hfresh
    · obtain ⟨a, haS, hae⟩ := Finset.mem_map.mp he
      change Q.recoverLeft a = e at hae
      rw [← hae]
      exact (Q.recoverLeft_mem_liftMatchingSet_iff S a).2 haS

/-- The signing on the smoothed graph used by the Pfaffian closure argument.
Surviving copies keep their signs; the fresh copy receives the manuscript's
`-s(uz)s(wz)s(wv)` sign. -/
def smoothEdgeSign (edgeSign : E → ℤˣ) : Q.SmoothEdge → ℤˣ
  | .inl e => edgeSign e.val
  | .inr _ => -(edgeSign Q.uz * edgeSign Q.wz * edgeSign Q.wv)

@[simp] theorem smoothEdgeSign_old (edgeSign : E → ℤˣ) (e : Q.Survivor) :
    Q.smoothEdgeSign edgeSign (Q.oldEdge e) = edgeSign e.val := rfl

@[simp] theorem smoothEdgeSign_fresh (edgeSign : E → ℤˣ) :
    Q.smoothEdgeSign edgeSign Q.freshEdge =
      -(edgeSign Q.uz * edgeSign Q.wz * edgeSign Q.wv) := rfl

/-- Product transport through the recovery embedding. -/
theorem prod_map_recoverLeft (S : Finset Q.SmoothEdge)
    (edgeSign : E → ℤˣ) :
    (∏ e ∈ S.map Q.recoverLeftEmbedding, edgeSign e) =
      ∏ a ∈ S, edgeSign (Q.recoverLeft a) := by
  simpa [recoverLeftEmbedding] using
    (Finset.prod_map S Q.recoverLeftEmbedding edgeSign)

/-- In the non-fresh state the lifted old-edge product is the smooth product
multiplied by the middle-path sign. -/
theorem prod_liftMatchingSet_of_not_fresh
    (S : Finset Q.SmoothEdge) (edgeSign : E → ℤˣ)
    (hfresh : ¬ Q.freshSelected S) :
    (∏ e ∈ Q.liftMatchingSet S, edgeSign e) =
      edgeSign Q.wz * ∏ a ∈ S, Q.smoothEdgeSign edgeSign a := by
  classical
  have hpoint :
      (∏ a ∈ S, edgeSign (Q.recoverLeft a)) =
        ∏ a ∈ S, Q.smoothEdgeSign edgeSign a := by
    apply Finset.prod_congr rfl
    intro a ha
    rcases a with a | unit
    · rfl
    · cases unit
      exact False.elim (hfresh (by simpa [freshSelected, freshEdge] using ha))
  rw [Q.liftMatchingSet_eq_map_recoverLeft_insert_wz S hfresh,
    Finset.prod_insert (Q.wz_not_mem_map_recoverLeft S),
    Q.prod_map_recoverLeft S edgeSign, hpoint]

/-- In the fresh state the lifted old-edge product is `-s(wz)` times the
smooth product.  The square of every integer unit is one, which cancels the
middle-path sign introduced in the fresh-edge definition. -/
theorem prod_liftMatchingSet_of_fresh
    (S : Finset Q.SmoothEdge) (edgeSign : E → ℤˣ)
    (hfresh : Q.freshSelected S) :
    (∏ e ∈ Q.liftMatchingSet S, edgeSign e) =
      (- edgeSign Q.wz) * ∏ a ∈ S, Q.smoothEdgeSign edgeSign a := by
  classical
  let T : Finset Q.SmoothEdge := S.erase Q.freshEdge
  have hfreshT : Q.freshEdge ∉ T := by simp [T]
  have hrecoverRest :
      (∏ a ∈ T, edgeSign (Q.recoverLeft a)) =
        ∏ a ∈ T, Q.smoothEdgeSign edgeSign a := by
    apply Finset.prod_congr rfl
    intro a ha
    have hne : a ≠ Q.freshEdge := (Finset.mem_erase.mp (by simpa [T] using ha)).1
    rcases a with a | unit
    · rfl
    · cases unit
      exact False.elim (hne rfl)
  have hrecoverS :
      (∏ a ∈ S, edgeSign (Q.recoverLeft a)) =
        edgeSign Q.uz * ∏ a ∈ T, edgeSign (Q.recoverLeft a) := by
    rw [← Finset.prod_erase_mul S (fun a => edgeSign (Q.recoverLeft a)) hfresh]
    simp [T, mul_comm]
  have hsmoothS :
      (∏ a ∈ S, Q.smoothEdgeSign edgeSign a) =
        (-(edgeSign Q.uz * edgeSign Q.wz * edgeSign Q.wv)) *
          ∏ a ∈ T, Q.smoothEdgeSign edgeSign a := by
    rw [← Finset.prod_erase_mul S (Q.smoothEdgeSign edgeSign) hfresh]
    simp [T, mul_comm]
  rw [Q.liftMatchingSet_eq_map_recoverLeft_insert_wv S hfresh,
    Finset.prod_insert (Q.wv_not_mem_map_recoverLeft S),
    Q.prod_map_recoverLeft S edgeSign, hrecoverS, hrecoverRest, hsmoothS]
  have hsq : edgeSign Q.wz * edgeSign Q.wz = 1 := by
    simpa only [pow_two] using Int.units_sq (edgeSign Q.wz)
  simp only [neg_mul, mul_neg, neg_neg]
  calc
    edgeSign Q.wv *
          (edgeSign Q.uz * ∏ a ∈ T, Q.smoothEdgeSign edgeSign a) =
        (edgeSign Q.wz * edgeSign Q.wz) *
          (edgeSign Q.wv *
            (edgeSign Q.uz * ∏ a ∈ T, Q.smoothEdgeSign edgeSign a)) := by
              rw [hsq, one_mul]
    _ = edgeSign Q.wz *
          ((edgeSign Q.uz * edgeSign Q.wz * edgeSign Q.wv) *
            ∏ a ∈ T, Q.smoothEdgeSign edgeSign a) := by
              ac_rfl

end OddPathFrame
end BipartiteMultigraph
end BachThesisLean
