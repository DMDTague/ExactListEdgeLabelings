import BachThesisLean.Cubic.TightCutBalance
import BachThesisLean.Cubic.RegularMatching

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Simplicity of nontrivial cubic braces

The manuscript reduces the universal prescribed-pair problem further from all
cubic braces to simple cubic braces.  Rather than importing the standard brace
expansion theorem, this file proves the needed statement directly in the
edge-copy model.  Parallel copies at a cubic left vertex force fewer than three
distinct right neighbours.  Connectedness and matching-coveredness rule out a
single neighbour, while two neighbours make the closed neighbourhood shore a
nontrivial tight cut, contradicting the brace condition.
-/

/-- Simplicity for the edge-copy model: an ordered endpoint pair determines at
most one edge copy. -/
def IsSimple (G : BipartiteMultigraph X Y E) : Prop :=
  Function.Injective (fun e => (G.left e, G.right e))

/-- A connected finite graph has a boundary edge across every vertex bipartition
with both shores nonempty. -/
theorem IsConnected.edgeCut_nonempty_of_nonempty_shores
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hconn : G.IsConnected) (hW : W.Nonempty) (hWc : Wᶜ.Nonempty) :
    (G.edgeCut W).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hW
  obtain ⟨b, hbWc⟩ := hWc
  have hb : b ∉ W := Finset.mem_compl.mp hbWc
  by_contra hcut
  have hsides : ∀ e : E,
      ((Sum.inl (G.left e) : X ⊕ Y) ∈ W ↔
        (Sum.inr (G.right e) : X ⊕ Y) ∈ W) := by
    intro e
    constructor
    · intro hl
      by_contra hr
      exact hcut ⟨e, by simp [edgeCut, hl, hr]⟩
    · intro hr
      by_contra hl
      exact hcut ⟨e, by simp [edgeCut, hl, hr]⟩
  have heq := (hconn.2 a b).map_eq (fun z => decide (z ∈ W)) (by
    rintro p q ⟨e, _, hpq | hpq⟩
    · rcases hpq with ⟨rfl, rfl⟩
      by_cases hl : (Sum.inl (G.left e) : X ⊕ Y) ∈ W
      · have hr := (hsides e).1 hl
        simp [hl, hr]
      · have hr : (Sum.inr (G.right e) : X ⊕ Y) ∉ W := by
          intro hr
          exact hl ((hsides e).2 hr)
        simp [hl, hr]
    · rcases hpq with ⟨rfl, rfl⟩
      by_cases hl : (Sum.inl (G.left e) : X ⊕ Y) ∈ W
      · have hr := (hsides e).1 hl
        simp [hl, hr]
      · have hr : (Sum.inr (G.right e) : X ⊕ Y) ∉ W := by
          intro hr
          exact hl ((hsides e).2 hr)
        simp [hl, hr])
  simpa [ha, hb] using heq

/-- Two parallel edge copies at a cubic left vertex force strictly fewer than
three distinct right neighbours. -/
theorem rightNeighborSet_card_lt_three_of_parallel
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic)
    {e f : E} (hef : e ≠ f)
    (hleft : G.left e = G.left f) (hright : G.right e = G.right f) :
    (G.rightNeighborSet (G.left e)).card < 3 := by
  classical
  have heI : e ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) e).2 rfl
  have hfI : f ∈ G.leftIncident (G.left e) :=
    (G.mem_leftIncident (G.left e) f).2 hleft.symm
  have hdegree : (G.leftIncident (G.left e)).card = 3 := by
    simpa using hG (.inl (G.left e))
  have hle :
      (G.rightNeighborSet (G.left e)).card ≤
        (G.leftIncident (G.left e)).card := by
    simpa [rightNeighborSet] using
      (Finset.card_image_le :
        ((G.leftIncident (G.left e)).image G.right).card ≤
          (G.leftIncident (G.left e)).card)
  have hne :
      (G.rightNeighborSet (G.left e)).card ≠
        (G.leftIncident (G.left e)).card := by
    intro hcard
    have hinj : Set.InjOn G.right (G.leftIncident (G.left e)) :=
      (Finset.card_image_iff.mp (by simpa [rightNeighborSet] using hcard))
    exact hef (hinj heI hfI hright)
  omega

/-- The canonical shore around a left vertex consists of that vertex together
with every distinct right neighbour of it. -/
noncomputable def closedLeftShore (G : BipartiteMultigraph X Y E) (x : X) :
    Finset (X ⊕ Y) := by
  classical
  exact Finset.univ.filter fun v =>
    match v with
    | .inl x' => x' = x
    | .inr y => y ∈ G.rightNeighborSet x

@[simp] theorem mem_closedLeftShore_inl
    (G : BipartiteMultigraph X Y E) (x x' : X) :
    (Sum.inl x' : X ⊕ Y) ∈ G.closedLeftShore x ↔ x' = x := by
  classical
  simp [closedLeftShore]

@[simp] theorem mem_closedLeftShore_inr
    (G : BipartiteMultigraph X Y E) (x : X) (y : Y) :
    (Sum.inr y : X ⊕ Y) ∈ G.closedLeftShore x ↔
      y ∈ G.rightNeighborSet x := by
  classical
  simp [closedLeftShore]

@[simp] theorem cutLeftVertices_closedLeftShore
    (G : BipartiteMultigraph X Y E) (x : X) :
    cutLeftVertices (G.closedLeftShore x) = {x} := by
  classical
  ext x'
  simp

@[simp] theorem cutRightVertices_closedLeftShore
    (G : BipartiteMultigraph X Y E) (x : X) :
    cutRightVertices (G.closedLeftShore x) = G.rightNeighborSet x := by
  classical
  ext y
  simp

/-- By construction, no edge copy leaves the closed shore from its unique left
vertex: every right endpoint of an edge at `x` was included. -/
@[simp] theorem cutFromLeft_closedLeftShore
    (G : BipartiteMultigraph X Y E) (x : X) :
    G.cutFromLeft (G.closedLeftShore x) = ∅ := by
  classical
  ext e
  constructor
  · intro he
    have hcut := (G.mem_cutFromLeft (G.closedLeftShore x) e).1 he
    have hx : G.left e = x := by
      simpa using hcut.1
    have hy : G.right e ∈ G.rightNeighborSet x :=
      (mem_rightNeighborSet G x (G.right e)).2
        ⟨e, (G.mem_leftIncident x e).2 hx, rfl⟩
    exact False.elim (hcut.2 (by simpa using hy))
  · intro he
    simp at he

@[simp] theorem closedLeftShore_nonempty
    (G : BipartiteMultigraph X Y E) (x : X) :
    (G.closedLeftShore x).Nonempty :=
  ⟨.inl x, by simp⟩

/-- With at least three left vertices, the closed shore around the left endpoint
of any edge is nontrivial on both sides of the cut. -/
theorem closedLeftShore_isNontrivial_of_three_le_card_left
    (G : BipartiteMultigraph X Y E) (e : E)
    (hX : 3 ≤ Fintype.card X) :
    IsNontrivialCutShore (G.closedLeftShore (G.left e)) := by
  classical
  constructor
  · apply Finset.one_lt_card_iff_nontrivial.mpr
    refine ⟨.inl (G.left e), by simp, .inr (G.right e), ?_, by simp⟩
    apply (G.mem_closedLeftShore_inr (G.left e) (G.right e)).2
    exact (mem_rightNeighborSet G (G.left e) (G.right e)).2
      ⟨e, (G.mem_leftIncident (G.left e) e).2 rfl, rfl⟩
  · let ι : X ↪ X ⊕ Y := ⟨Sum.inl, Sum.inl_injective⟩
    let S : Finset (X ⊕ Y) := (Finset.univ.erase (G.left e)).map ι
    have hSsub : S ⊆ (G.closedLeftShore (G.left e))ᶜ := by
      intro z hz
      obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hz
      have hxne : x' ≠ G.left e := (Finset.mem_erase.mp hx').1
      apply Finset.mem_compl.mpr
      intro hxmem
      exact hxne ((G.mem_closedLeftShore_inl (G.left e) x').1 hxmem)
    have hScard : S.card = Fintype.card X - 1 := by
      simp [S]
    have hSgt : 1 < S.card := by
      omega
    exact lt_of_lt_of_le hSgt (Finset.card_le_card hSsub)

/-- In a connected cubic graph with at least three left vertices, a left vertex
incident with an edge cannot have exactly one distinct right neighbour. -/
theorem rightNeighborSet_card_ne_one_of_three_le_card_left
    (G : BipartiteMultigraph X Y E) (hconn : G.IsConnected) (hG : G.IsCubic)
    (e : E) (hX : 3 ≤ Fintype.card X) :
    (G.rightNeighborSet (G.left e)).card ≠ 1 := by
  classical
  intro hN
  let W := G.closedLeftShore (G.left e)
  have hnontriv : IsNontrivialCutShore W := by
    simpa [W] using G.closedLeftShore_isNontrivial_of_three_le_card_left e hX
  have hW : W.Nonempty := by
    simpa [W] using G.closedLeftShore_nonempty (G.left e)
  have hWcCard : 0 < Wᶜ.card := lt_trans Nat.zero_lt_one hnontriv.2
  have hWc : Wᶜ.Nonempty := Finset.card_pos.mp hWcCard
  obtain ⟨g, hgcut⟩ := hconn.edgeCut_nonempty_of_nonempty_shores hW hWc
  have hgRight : g ∈ G.cutFromRight W := by
    have h := hgcut
    rw [G.edgeCut_eq_oriented_union, show G.cutFromLeft W = ∅ by simp [W]] at h
    simpa using h
  obtain ⟨P, hP, hgP⟩ := G.exists_perfectMatching_containing_edge_of_cubic hG g
  have hbal := hP.cut_orientation_balance W
  have hleftVertices : cutLeftVertices W = {G.left e} := by simp [W]
  have hrightVertices : cutRightVertices W = G.rightNeighborSet (G.left e) := by
    simp [W]
  have hleftCut : G.cutFromLeft W = ∅ := by simp [W]
  rw [hleftVertices, hrightVertices, hleftCut] at hbal
  simp only [Finset.card_singleton, Finset.inter_empty, Finset.card_empty,
    Nat.add_zero] at hbal
  rw [hN] at hbal
  have hzero : (P ∩ G.cutFromRight W).card = 0 := by omega
  have hgInter : g ∈ P ∩ G.cutFromRight W := Finset.mem_inter.mpr ⟨hgP, hgRight⟩
  have hpos : 0 < (P ∩ G.cutFromRight W).card :=
    Finset.card_pos.mpr ⟨g, hgInter⟩
  omega

/-- Hence two parallel copies at a left vertex of a connected cubic graph with
at least three left vertices force exactly two distinct right neighbours. -/
theorem rightNeighborSet_card_eq_two_of_parallel
    (G : BipartiteMultigraph X Y E) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hX : 3 ≤ Fintype.card X)
    {e f : E} (hef : e ≠ f)
    (hleft : G.left e = G.left f) (hright : G.right e = G.right f) :
    (G.rightNeighborSet (G.left e)).card = 2 := by
  classical
  have hlt := G.rightNeighborSet_card_lt_three_of_parallel hG hef hleft hright
  have hne1 := G.rightNeighborSet_card_ne_one_of_three_le_card_left hconn hG e hX
  have hmem : G.right e ∈ G.rightNeighborSet (G.left e) :=
    (mem_rightNeighborSet G (G.left e) (G.right e)).2
      ⟨e, (G.mem_leftIncident (G.left e) e).2 rfl, rfl⟩
  have hpos : 0 < (G.rightNeighborSet (G.left e)).card :=
    Finset.card_pos.mpr ⟨G.right e, hmem⟩
  omega

/-- If a left vertex has exactly two distinct neighbours, its closed shore is a
tight cut: the matching balance equation forces every perfect matching to use
exactly one right-to-left boundary edge. -/
theorem closedLeftShore_isTightCut_of_two_neighbors
    (G : BipartiteMultigraph X Y E) (x : X)
    (hN : (G.rightNeighborSet x).card = 2) :
    G.IsTightCut (G.closedLeftShore x) := by
  classical
  intro P hP
  have hbal := hP.cut_orientation_balance (G.closedLeftShore x)
  rw [G.cutLeftVertices_closedLeftShore, G.cutRightVertices_closedLeftShore,
    G.cutFromLeft_closedLeftShore] at hbal
  simp only [Finset.card_singleton, Finset.inter_empty, Finset.card_empty,
    Nat.add_zero] at hbal
  rw [hN] at hbal
  have hright : (P ∩ G.cutFromRight (G.closedLeftShore x)).card = 1 := by
    omega
  have hcut : G.edgeCut (G.closedLeftShore x) =
      G.cutFromRight (G.closedLeftShore x) := by
    rw [G.edgeCut_eq_oriented_union, G.cutFromLeft_closedLeftShore]
    simp
  rw [hcut]
  exact hright

/-- Relevant cubic braces are simple: once a brace has at least three vertices
on the left shore, parallel edge copies would create the forbidden nontrivial
tight cut above. -/
theorem IsBrace.isSimple_of_three_le_card_left
    {G : BipartiteMultigraph X Y E} (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : 3 ≤ Fintype.card X) : G.IsSimple := by
  rw [IsSimple]
  intro e f hpair
  by_contra hef
  have hleft : G.left e = G.left f := congrArg Prod.fst hpair
  have hright : G.right e = G.right f := congrArg Prod.snd hpair
  have hN : (G.rightNeighborSet (G.left e)).card = 2 :=
    G.rightNeighborSet_card_eq_two_of_parallel hbrace.1.1 hG hX hef hleft hright
  have hnontriv := G.closedLeftShore_isNontrivial_of_three_le_card_left e hX
  have hT := G.closedLeftShore_isTightCut_of_two_neighbors (G.left e) hN
  exact hbrace.2 (G.closedLeftShore (G.left e)) hnontriv hT

end BipartiteMultigraph
end BachThesisLean
