import BachThesisLean.Cubic.Foundations
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Hall infrastructure for cubic bipartite multigraphs

The manuscript repeatedly uses the standard fact that finite regular
bipartite graphs have perfect matchings.  These lemmas prove that fact directly
for the edge-copy model.  Parallel edges remain distinct throughout the degree
counts; Hall's representatives are chosen among right-neighbour vertices and
then lifted back to actual edge copies.
-/

/-- Right neighbours of one left vertex, forgetting only multiplicity. -/
noncomputable def rightNeighborSet (G : BipartiteMultigraph X Y E) (x : X) :
    Finset Y :=
  (G.leftIncident x).image G.right

@[simp] theorem mem_rightNeighborSet (G : BipartiteMultigraph X Y E)
    (x : X) (y : Y) :
    y ∈ G.rightNeighborSet x ↔
      ∃ e ∈ G.leftIncident x, G.right e = y := by
  classical
  simp [rightNeighborSet]

/-- Incidence fibres at distinct left vertices are disjoint sets of edge
copies. -/
theorem leftIncident_pairwiseDisjoint (G : BipartiteMultigraph X Y E)
    (S : Finset X) :
    (S : Set X).PairwiseDisjoint G.leftIncident := by
  intro x _ x' _ hxx'
  change Disjoint (G.leftIncident x) (G.leftIncident x')
  rw [Finset.disjoint_left]
  intro e hex hex'
  have hx : G.left e = x := (G.mem_leftIncident x e).1 hex
  have hx' : G.left e = x' := (G.mem_leftIncident x' e).1 hex'
  exact hxx' (hx.symm.trans hx')

/-- Incidence fibres at distinct right vertices are disjoint sets of edge
copies. -/
theorem rightIncident_pairwiseDisjoint (G : BipartiteMultigraph X Y E)
    (S : Finset Y) :
    (S : Set Y).PairwiseDisjoint G.rightIncident := by
  intro y _ y' _ hyy'
  change Disjoint (G.rightIncident y) (G.rightIncident y')
  rw [Finset.disjoint_left]
  intro e hey hey'
  have hy : G.right e = y := (G.mem_rightIncident y e).1 hey
  have hy' : G.right e = y' := (G.mem_rightIncident y' e).1 hey'
  exact hyy' (hy.symm.trans hy')

/-- In a left-regular multigraph, the edge copies incident with a set of left
vertices are counted with their full multiplicities. -/
theorem card_biUnion_leftIncident_of_regular
    (G : BipartiteMultigraph X Y E) {k : ℕ} (hG : G.IsLeftRegular k)
    (S : Finset X) :
    (S.biUnion G.leftIncident).card = k * S.card := by
  classical
  rw [Finset.card_biUnion (G.leftIncident_pairwiseDisjoint S)]
  calc
    ∑ x ∈ S, (G.leftIncident x).card = ∑ _x ∈ S, k := by
      apply Finset.sum_congr rfl
      intro x _
      simpa [leftDegree] using hG x
    _ = S.card * k := by simp
    _ = k * S.card := Nat.mul_comm _ _

/-- Right-side version of the preceding edge-copy count. -/
theorem card_biUnion_rightIncident_of_regular
    (G : BipartiteMultigraph X Y E) {k : ℕ} (hG : G.IsRightRegular k)
    (S : Finset Y) :
    (S.biUnion G.rightIncident).card = k * S.card := by
  classical
  rw [Finset.card_biUnion (G.rightIncident_pairwiseDisjoint S)]
  calc
    ∑ y ∈ S, (G.rightIncident y).card = ∑ _y ∈ S, k := by
      apply Finset.sum_congr rfl
      intro y _
      simpa [rightDegree] using hG y
    _ = S.card * k := by simp
    _ = k * S.card := Nat.mul_comm _ _

@[simp] theorem biUnion_leftIncident_univ (G : BipartiteMultigraph X Y E) :
    (Finset.univ : Finset X).biUnion G.leftIncident = Finset.univ := by
  classical
  ext e
  simp

@[simp] theorem biUnion_rightIncident_univ (G : BipartiteMultigraph X Y E) :
    (Finset.univ : Finset Y).biUnion G.rightIncident = Finset.univ := by
  classical
  ext e
  simp

/-- Cubic regularity forces the two shores to have the same finite cardinality. -/
theorem card_left_eq_card_right_of_cubic
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) :
    Fintype.card X = Fintype.card Y := by
  have hreg := (G.isCubic_iff).1 hG
  have hx := G.card_biUnion_leftIncident_of_regular hreg.1 (Finset.univ : Finset X)
  have hy := G.card_biUnion_rightIncident_of_regular hreg.2 (Finset.univ : Finset Y)
  simp only [biUnion_leftIncident_univ, biUnion_rightIncident_univ,
    Finset.card_univ] at hx hy
  omega

/-- Hall's cardinal inequality for the right-neighbour family of a cubic
bipartite multigraph. -/
theorem cubic_hall_condition
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (S : Finset X) :
    S.card ≤ (S.biUnion G.rightNeighborSet).card := by
  classical
  let F : Finset E := S.biUnion G.leftIncident
  let N : Finset Y := S.biUnion G.rightNeighborSet
  have hsub : F ⊆ N.biUnion G.rightIncident := by
    intro e he
    have he' : e ∈ S.biUnion G.leftIncident := by simpa [F] using he
    rw [Finset.mem_biUnion] at he'
    obtain ⟨x, hxS, hex⟩ := he'
    rw [Finset.mem_biUnion]
    refine ⟨G.right e, ?_, (G.mem_rightIncident (G.right e) e).2 rfl⟩
    dsimp [N]
    rw [Finset.mem_biUnion]
    refine ⟨x, hxS, ?_⟩
    exact (mem_rightNeighborSet G x (G.right e)).2 ⟨e, hex, rfl⟩
  have hreg := (G.isCubic_iff).1 hG
  have hF : F.card = 3 * S.card := by
    simpa [F] using G.card_biUnion_leftIncident_of_regular hreg.1 S
  have hN : (N.biUnion G.rightIncident).card = 3 * N.card :=
    G.card_biUnion_rightIncident_of_regular hreg.2 N
  have hc := Finset.card_le_card hsub
  rw [hF, hN] at hc
  change S.card ≤ N.card
  omega

/-- A finite cubic bipartite multigraph has a perfect matching.  No simplicity
or connectedness hypothesis is required. -/
theorem exists_perfectMatching_of_cubic
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) :
    Nonempty G.PerfectMatching := by
  classical
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x : X => G.rightNeighborSet x)).1 (G.cubic_hall_condition hG)
  have hedge : ∀ x : X, ∃ e : E, e ∈ G.leftIncident x ∧ G.right e = f x := by
    intro x
    exact (mem_rightNeighborSet G x (f x)).1 (hf_mem x)
  choose g hgLeft hgRight using hedge
  have hgLeftEq : ∀ x : X, G.left (g x) = x := by
    intro x
    exact (G.mem_leftIncident x (g x)).1 (hgLeft x)
  have hg_inj : Function.Injective g := by
    intro x x' hxx'
    have hleft := congrArg G.left hxx'
    exact (hgLeftEq x).symm.trans (hleft.trans (hgLeftEq x'))
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf_inj, G.card_left_eq_card_right_of_cubic hG⟩
  let P : Finset E := Finset.univ.image g
  refine ⟨⟨P, ?_⟩⟩
  intro v
  cases v with
  | inl x =>
      have hset : G.selectedIncident P (.inl x) = {g x} := by
        ext e
        simp only [mem_selectedIncident, Finset.mem_singleton]
        constructor
        · rintro ⟨heP, heInc⟩
          have heImage : e ∈ Finset.univ.image g := by simpa [P] using heP
          obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp heImage
          change G.left (g z) = x at heInc
          have hz : z = x := (hgLeftEq z).symm.trans heInc
          simpa [hz]
        · intro he
          subst e
          refine ⟨?_, ?_⟩
          · simp [P]
          · exact hgLeftEq x
      rw [hset]
      simp
  | inr y =>
      obtain ⟨x, hfx⟩ := hf_bij.2 y
      have hset : G.selectedIncident P (.inr y) = {g x} := by
        ext e
        simp only [mem_selectedIncident, Finset.mem_singleton]
        constructor
        · rintro ⟨heP, heInc⟩
          have heImage : e ∈ Finset.univ.image g := by simpa [P] using heP
          obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp heImage
          change G.right (g z) = y at heInc
          have hfzy : f z = y := (hgRight z).symm.trans heInc
          have hfz : f z = f x := hfzy.trans hfx.symm
          have hz : z = x := hf_inj hfz
          simpa [hz]
        · intro he
          subst e
          refine ⟨?_, ?_⟩
          · simp [P]
          · change G.right (g x) = y
            exact (hgRight x).trans hfx
      rw [hset]
      simp

end BipartiteMultigraph
end BachThesisLean
