import BachThesisLean.Cubic.FourVertexCube
import BachThesisLean.Cubic.Isomorphism

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# The four-vertex-per-shore brace case

A simple cubic bipartite graph with four vertices on each shore is uniquely the
cube `K₄,₄` minus a perfect matching.  We prove this without enumerating graph
presentations.  Every left vertex has exactly three distinct right neighbours,
so it has a unique missing right vertex.  The missing-vertex map is injective:
if two left vertices missed the same right vertex, that right vertex could have
at most two distinct left neighbours, contradicting simplicity and cubicity.
After labeling each right vertex by the left vertex that misses it, every edge
is exactly one off-diagonal copy of the canonical cube.
-/

/-- Left neighbours of one right vertex, forgetting only edge multiplicity. -/
noncomputable def leftNeighborSet (G : BipartiteMultigraph X Y E) (y : Y) :
    Finset X :=
  (G.rightIncident y).image G.left

@[simp] theorem mem_leftNeighborSet (G : BipartiteMultigraph X Y E)
    (y : Y) (x : X) :
    x ∈ G.leftNeighborSet y ↔
      ∃ e ∈ G.rightIncident y, G.left e = x := by
  classical
  simp [leftNeighborSet]

/-- The left/right neighbour-set predicates describe the same endpoint cell. -/
theorem mem_leftNeighborSet_iff_mem_rightNeighborSet
    (G : BipartiteMultigraph X Y E) (x : X) (y : Y) :
    x ∈ G.leftNeighborSet y ↔ y ∈ G.rightNeighborSet x := by
  constructor
  · intro hx
    obtain ⟨e, heR, heL⟩ := (G.mem_leftNeighborSet y x).1 hx
    apply (mem_rightNeighborSet G x y).2
    refine ⟨e, ?_, ?_⟩
    · exact (G.mem_leftIncident x e).2 heL
    · exact (G.mem_rightIncident y e).1 heR
  · intro h
    obtain ⟨e, heL, heR⟩ := (mem_rightNeighborSet G x y).1 h
    exact (G.mem_leftNeighborSet y x).2
      ⟨e, (G.mem_rightIncident y e).2 heR, (G.mem_leftIncident x e).1 heL⟩

/-- At a fixed right vertex of a simple cubic graph, the three incident edge
copies have three distinct left endpoints. -/
theorem leftNeighborSet_card_eq_three_of_simple_cubic
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (y : Y) : (G.leftNeighborSet y).card = 3 := by
  classical
  have hinj : Set.InjOn G.left (G.rightIncident y) := by
    intro e he f hf hleft
    apply hsimple
    apply Prod.ext
    · exact hleft
    · exact ((G.mem_rightIncident y e).1 he).trans
        ((G.mem_rightIncident y f).1 hf).symm
  have hcardImage :
      ((G.rightIncident y).image G.left).card = (G.rightIncident y).card :=
    Finset.card_image_iff.mpr hinj
  rw [leftNeighborSet, hcardImage]
  simpa using hG (.inr y)

/-- With four right vertices, a simple cubic left vertex has exactly one
missing right neighbour. -/
theorem existsUnique_missingRight_of_simple_cubic_card_right_eq_four
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (hY : Fintype.card Y = 4) (x : X) :
    ∃! y : Y, y ∉ G.rightNeighborSet x := by
  classical
  let M : Finset Y := (Finset.univ : Finset Y) \ G.rightNeighborSet x
  have hN : (G.rightNeighborSet x).card = 3 :=
    G.rightNeighborSet_card_eq_three_of_simple_cubic hsimple hG x
  have hMcard : M.card = 1 := by
    dsimp [M]
    rw [Finset.card_sdiff (Finset.subset_univ (G.rightNeighborSet x))]
    simp [hY, hN]
  have hMpos : 0 < M.card := by omega
  obtain ⟨y, hyM⟩ := Finset.card_pos.mp hMpos
  have hy : y ∉ G.rightNeighborSet x := (Finset.mem_sdiff.mp hyM).2
  refine ⟨y, hy, ?_⟩
  intro z hz
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
  by_contra hzy
  have hyz : y ≠ z := by
    intro hyz
    exact hzy hyz.symm
  have hgt : 1 < M.card :=
    Finset.one_lt_card_iff_nontrivial.mpr ⟨y, hyM, z, hzM, hyz⟩
  rw [hMcard] at hgt
  omega

/-- In a simple cubic `4 × 4` graph, the map sending a left vertex to its
unique missing right neighbour is injective. -/
theorem missingRight_injective_of_simple_cubic_card_four
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (hX : Fintype.card X = 4) (hY : Fintype.card Y = 4)
    (miss : X → Y)
    (hmiss : ∀ x, miss x ∉ G.rightNeighborSet x) :
    Function.Injective miss := by
  classical
  intro x x' hmx
  by_contra hxx
  let y := miss x
  have hxNot : x ∉ G.leftNeighborSet y := by
    intro hxN
    have hyN : y ∈ G.rightNeighborSet x :=
      (G.mem_leftNeighborSet_iff_mem_rightNeighborSet x y).1 hxN
    exact hmiss x hyN
  have hx'Not : x' ∉ G.leftNeighborSet y := by
    intro hxN
    have hyN : y ∈ G.rightNeighborSet x' :=
      (G.mem_leftNeighborSet_iff_mem_rightNeighborSet x' y).1 hxN
    have hmy : miss x' = y := hmx.symm
    exact hmiss x' (by simpa [hmy] using hyN)
  have hsub :
      G.leftNeighborSet y ⊆ ((Finset.univ : Finset X).erase x).erase x' := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro hzx'
      subst z
      exact hx'Not hz
    · apply Finset.mem_erase.mpr
      exact ⟨by
        intro hzx
        subst z
        exact hxNot hz, Finset.mem_univ z⟩
  have hNcard : (G.leftNeighborSet y).card = 3 :=
    G.leftNeighborSet_card_eq_three_of_simple_cubic hsimple hG y
  have hx'ne : x' ≠ x := by
    intro hx'eq
    exact hxx hx'eq.symm
  have hx'mem : x' ∈ (Finset.univ : Finset X).erase x :=
    Finset.mem_erase.mpr ⟨hx'ne, Finset.mem_univ x'⟩
  have hfirst : ((Finset.univ : Finset X).erase x).card = 3 := by
    simp [hX]
  have hsecondAdd := Finset.card_erase_add_one hx'mem
  have hsecond : (((Finset.univ : Finset X).erase x).erase x').card = 2 := by
    omega
  have hle := Finset.card_le_card hsub
  rw [hNcard, hsecond] at hle
  omega

/-- Inverse slot lookup for the canonical cube.  Diagonal inputs are assigned
an arbitrary slot; the theorem below is used only off the diagonal. -/
def fourCubeSlot : Fin 4 → Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2],
    ![0, 0, 1, 2],
    ![0, 1, 0, 2],
    ![0, 1, 2, 0]]

/-- Off the diagonal, `fourCubeSlot` inverts `fourCubeRight`. -/
theorem fourCubeRight_slot_of_ne (i j : Fin 4) (h : j ≠ i) :
    fourCubeRight i (fourCubeSlot i j) = j := by
  fin_cases i <;> fin_cases j <;> simp_all [fourCubeRight, fourCubeSlot]

/-- The three canonical slots in one row have distinct right endpoints. -/
theorem fourCubeRight_injective (i : Fin 4) :
    Function.Injective (fourCubeRight i) := by
  intro a b h
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp_all [fourCubeRight]

/-- Every simple cubic bipartite graph with four vertices on each shore is
explicitly isomorphic, with individual edge copies preserved, to the canonical
cube. -/
noncomputable def graphIsoFourCube_of_simple_cubic_card_four
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (hX : Fintype.card X = 4) : GraphIso G fourCube := by
  classical
  have hY : Fintype.card Y = 4 := by
    calc
      Fintype.card Y = Fintype.card X :=
        (G.card_left_eq_card_right_of_cubic hG).symm
      _ = 4 := hX
  have hmissing : ∀ x : X, ∃! y : Y, y ∉ G.rightNeighborSet x :=
    fun x => G.existsUnique_missingRight_of_simple_cubic_card_right_eq_four
      hsimple hG hY x
  choose miss hmiss using fun x => (hmissing x).exists
  have hmissUnique : ∀ x y, y ∉ G.rightNeighborSet x → y = miss x := by
    intro x y hy
    exact (hmissing x).unique hy (hmiss x)
  have hmissInj : Function.Injective miss :=
    G.missingRight_injective_of_simple_cubic_card_four
      hsimple hG hX hY miss hmiss
  have hmissBij : Function.Bijective miss :=
    (Fintype.bijective_iff_injective_and_card miss).2
      ⟨hmissInj, G.card_left_eq_card_right_of_cubic hG⟩
  let missEquiv : X ≃ Y := Equiv.ofBijective miss hmissBij
  let leftLabel : X ≃ Fin 4 := Fintype.equivFinOfCardEq hX
  let rightLabel : Y ≃ Fin 4 := missEquiv.symm.trans leftLabel
  have hdiag (x : X) : rightLabel (miss x) = leftLabel x := by
    change leftLabel (missEquiv.symm (miss x)) = leftLabel x
    have hm : missEquiv x = miss x := rfl
    rw [← hm]
    simp
  have hrightNe (e : E) : G.right e ≠ miss (G.left e) := by
    intro hEq
    apply hmiss (G.left e)
    rw [← hEq]
    exact (mem_rightNeighborSet G (G.left e) (G.right e)).2
      ⟨e, (G.mem_leftIncident (G.left e) e).2 rfl, rfl⟩
  have hlabelNe (e : E) :
      rightLabel (G.right e) ≠ leftLabel (G.left e) := by
    intro hEq
    have hEq' : rightLabel (G.right e) = rightLabel (miss (G.left e)) :=
      hEq.trans (hdiag (G.left e)).symm
    exact hrightNe e (rightLabel.injective hEq')
  let edgeMap : E → FourCubeEdge := fun e =>
    (leftLabel (G.left e),
      fourCubeSlot (leftLabel (G.left e)) (rightLabel (G.right e)))
  have hmapLeft (e : E) : fourCube.left (edgeMap e) = leftLabel (G.left e) := rfl
  have hmapRight (e : E) : fourCube.right (edgeMap e) = rightLabel (G.right e) := by
    change fourCubeRight (leftLabel (G.left e))
      (fourCubeSlot (leftLabel (G.left e)) (rightLabel (G.right e))) =
        rightLabel (G.right e)
    exact fourCubeRight_slot_of_ne _ _ (hlabelNe e)
  have hedgeInj : Function.Injective edgeMap := by
    intro e f hef
    have hlab : leftLabel (G.left e) = leftLabel (G.left f) := by
      simpa [edgeMap] using congrArg Prod.fst hef
    have hleft : G.left e = G.left f := leftLabel.injective hlab
    have hrLab : rightLabel (G.right e) = rightLabel (G.right f) := by
      rw [← hmapRight e, ← hmapRight f]
      exact congrArg fourCube.right hef
    have hright : G.right e = G.right f := rightLabel.injective hrLab
    exact hsimple (Prod.ext hleft hright)
  have hedgeSurj : Function.Surjective edgeMap := by
    intro q
    let x : X := leftLabel.symm q.1
    let y : Y := rightLabel.symm (fourCube.right q)
    have hxLabel : leftLabel x = q.1 := by simp [x]
    have hyLabel : rightLabel y = fourCube.right q := by simp [y]
    have hyNe : y ≠ miss x := by
      intro hEq
      have hcanon : fourCube.right q = fourCube.left q := by
        rw [← hyLabel, hEq, hdiag x, hxLabel]
        rfl
      exact fourCube_right_ne_left q hcanon
    have hyN : y ∈ G.rightNeighborSet x := by
      by_contra hyNot
      exact hyNe (hmissUnique x y hyNot)
    obtain ⟨e, heI, heR⟩ := (mem_rightNeighborSet G x y).1 hyN
    have heL : G.left e = x := (G.mem_leftIncident x e).1 heI
    refine ⟨e, ?_⟩
    apply Prod.ext
    · change leftLabel (G.left e) = q.1
      rw [heL, hxLabel]
    · apply fourCubeRight_injective q.1
      have hfirst : (edgeMap e).1 = q.1 := by
        change leftLabel (G.left e) = q.1
        rw [heL, hxLabel]
      have hrightEq : fourCube.right (edgeMap e) = fourCube.right q := by
        rw [hmapRight e, heR, hyLabel]
      change fourCubeRight (edgeMap e).1 (edgeMap e).2 =
        fourCubeRight q.1 q.2 at hrightEq
      rw [hfirst] at hrightEq
      exact hrightEq
  let edgeEquiv : E ≃ FourCubeEdge :=
    Equiv.ofBijective edgeMap ⟨hedgeInj, hedgeSurj⟩
  exact
    { leftEquiv := leftLabel
      rightEquiv := rightLabel
      edgeEquiv := edgeEquiv
      map_left := by
        intro e
        change fourCube.left (edgeMap e) = leftLabel (G.left e)
        exact hmapLeft e
      map_right := by
        intro e
        change fourCube.right (edgeMap e) = rightLabel (G.right e)
        exact hmapRight e }

/-- Every simple cubic bipartite graph with four vertices on each shore has
EEP, by transport from the canonical cube. -/
theorem hasEEP_of_simple_cubic_card_left_eq_four
    (G : BipartiteMultigraph X Y E) (hsimple : G.IsSimple) (hG : G.IsCubic)
    (hX : Fintype.card X = 4) : G.HasEEP := by
  let φ := G.graphIsoFourCube_of_simple_cubic_card_four hsimple hG hX
  exact φ.hasEEP_iff.mp fourCube_hasEEP

/-- In particular every cubic brace with four vertices on its left shore has
EEP. -/
theorem IsBrace.hasEEP_of_card_left_eq_four
    (hbrace : G.IsBrace) (hG : G.IsCubic)
    (hX : Fintype.card X = 4) : G.HasEEP := by
  have hthree : 3 ≤ Fintype.card X := by omega
  exact G.hasEEP_of_simple_cubic_card_left_eq_four
    (hbrace.isSimple_of_three_le_card_left hG hthree) hG hX

namespace IsMinimalEEPCounterexample

/-- The four-vertex-per-shore cube case is not a minimal counterexample. -/
theorem five_le_card_left (hmin : G.IsMinimalEEPCounterexample) :
    5 ≤ Fintype.card X := by
  by_contra hfive
  have hlt : Fintype.card X < 5 := Nat.lt_of_not_ge hfive
  have hX : Fintype.card X = 4 := by
    have hfour := hmin.four_le_card_left
    omega
  exact hmin.failsEEP
    (hmin.isBrace.hasEEP_of_card_left_eq_four hmin.cubic hX)

/-- The same five-vertex lower bound holds on the right shore. -/
theorem five_le_card_right (hmin : G.IsMinimalEEPCounterexample) :
    5 ≤ Fintype.card Y := by
  rw [← G.card_left_eq_card_right_of_cubic hmin.cubic]
  exact hmin.five_le_card_left

/-- Thus a minimal EEP counterexample has at least ten vertices. -/
theorem ten_le_vertexCard (hmin : G.IsMinimalEEPCounterexample) :
    10 ≤ G.vertexCard := by
  rw [vertexCard, ← G.card_left_eq_card_right_of_cubic hmin.cubic]
  have hleft := hmin.five_le_card_left
  omega

/-- Thus a minimal EEP counterexample has at least fifteen actual edge copies. -/
theorem fifteen_le_edgeCard (hmin : G.IsMinimalEEPCounterexample) :
    15 ≤ Fintype.card E := by
  rw [G.edgeCard_eq_three_mul_leftCard_of_cubic hmin.cubic]
  have hleft := hmin.five_le_card_left
  omega

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
