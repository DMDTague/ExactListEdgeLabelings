import BachThesisLean.Cubic.TightCutContractionCubic

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Connectivity of explicit tight-cut contractions

The contraction maps send an original edge either to its surviving edge copy
or to a constant path at the contraction root.  Consequently every original
path descends.  Surjectivity of the vertex maps then transfers connectedness
as soon as the shore being collapsed is nonempty.
-/

/-- Collapse `W` to the right root, retaining all vertices outside `W`. -/
def contractSetVertexMap (W : Finset (X ⊕ Y)) :
    X ⊕ Y → ContractSetLeft X Y W ⊕ ContractSetRight X Y W
  | .inl x => if h : (Sum.inl x : X ⊕ Y) ∈ W then
      .inr (contractSetRoot W) else .inl ⟨x, h⟩
  | .inr y => if h : (Sum.inr y : X ⊕ Y) ∈ W then
      .inr (contractSetRoot W) else .inr (.inl ⟨y, h⟩)

/-- Collapse `Wᶜ` to the left root, retaining all vertices in `W`. -/
def contractComplementVertexMap (W : Finset (X ⊕ Y)) :
    X ⊕ Y → ContractComplementLeft X Y W ⊕ ContractComplementRight X Y W
  | .inl x => if h : (Sum.inl x : X ⊕ Y) ∈ W then
      .inl (.inl ⟨x, h⟩) else .inl (contractComplementRoot W)
  | .inr y => if h : (Sum.inr y : X ⊕ Y) ∈ W then
      .inr ⟨y, h⟩ else .inl (contractComplementRoot W)

@[simp] theorem contractSetVertexMap_of_mem (W : Finset (X ⊕ Y))
    {a : X ⊕ Y} (ha : a ∈ W) :
    contractSetVertexMap W a = .inr (contractSetRoot W) := by
  cases a <;> simp [contractSetVertexMap, ha]

@[simp] theorem contractComplementVertexMap_of_not_mem (W : Finset (X ⊕ Y))
    {a : X ⊕ Y} (ha : a ∉ W) :
    contractComplementVertexMap W a = .inl (contractComplementRoot W) := by
  cases a <;> simp [contractComplementVertexMap, ha]

/-- Nonemptiness of the collapsed shore makes the quotient map onto. -/
theorem contractSetVertexMap_surjective (W : Finset (X ⊕ Y))
    (hW : W.Nonempty) : Function.Surjective (contractSetVertexMap W) := by
  rintro (x | (y | r))
  · exact ⟨.inl x.1, by simp [contractSetVertexMap, x.2]⟩
  · exact ⟨.inr y.1, by simp [contractSetVertexMap, y.2]⟩
  · obtain ⟨a, ha⟩ := hW
    cases r
    exact ⟨a, contractSetVertexMap_of_mem W ha⟩

theorem contractComplementVertexMap_surjective (W : Finset (X ⊕ Y))
    (hW : Wᶜ.Nonempty) : Function.Surjective (contractComplementVertexMap W) := by
  rintro ((x | r) | y)
  · exact ⟨.inl x.1, by simp [contractComplementVertexMap, x.2]⟩
  · obtain ⟨a, ha⟩ := hW
    cases r
    exact ⟨a, contractComplementVertexMap_of_not_mem W (Finset.mem_compl.mp ha)⟩
  · exact ⟨.inr y.1, by simp [contractComplementVertexMap, y.2]⟩

/-- Each original edge descends to an edge or a constant path in `G / W`. -/
theorem factorReachable_contractSet_endpoints
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) (e : E) :
    (G.contractSet W).FactorReachable Finset.univ
      (contractSetVertexMap W (.inl (G.left e)))
      (contractSetVertexMap W (.inr (G.right e))) := by
  by_cases hl : (Sum.inl (G.left e) : X ⊕ Y) ∈ W
  · have hr := G.right_mem_of_left_mem_of_cutFromLeft_eq_empty W hW hl
    simp only [contractSetVertexMap, dif_pos hl, dif_pos hr]
    exact (G.contractSet W).factorReachable_refl _ _
  · have he := (G.contractSet W).factorReachable_endpoints
      (Finset.mem_univ (⟨e, hl⟩ : ContractSetEdge G W))
    by_cases hr : (Sum.inr (G.right e) : X ⊕ Y) ∈ W
    · simpa [contractSetVertexMap, contractSet, hl, hr, contractSetRoot] using he
    · simpa [contractSetVertexMap, contractSet, hl, hr] using he

/-- Each original edge descends to an edge or a constant path in `G / Wᶜ`. -/
theorem factorReachable_contractComplement_endpoints
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) (e : E) :
    (G.contractComplement W).FactorReachable Finset.univ
      (contractComplementVertexMap W (.inl (G.left e)))
      (contractComplementVertexMap W (.inr (G.right e))) := by
  by_cases hr : (Sum.inr (G.right e) : X ⊕ Y) ∈ W
  · have he := (G.contractComplement W).factorReachable_endpoints
      (Finset.mem_univ (⟨e, hr⟩ : ContractComplementEdge G W))
    by_cases hl : (Sum.inl (G.left e) : X ⊕ Y) ∈ W
    · simpa [contractComplementVertexMap, contractComplement, hl, hr] using he
    · simpa [contractComplementVertexMap, contractComplement, hl, hr,
        contractComplementRoot] using he
  · have hl : (Sum.inl (G.left e) : X ⊕ Y) ∉ W :=
      G.left_not_mem_of_right_not_mem_of_cutFromLeft_eq_empty W hW hr
    simp only [contractComplementVertexMap, dif_neg hl, dif_neg hr]
    exact (G.contractComplement W).factorReachable_refl _ _

/-- Every original path descends through the `W` contraction map. -/
theorem factorReachable_contractSet_of_factorReachable
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) {a b : X ⊕ Y}
    (h : G.FactorReachable Finset.univ a b) :
    (G.contractSet W).FactorReachable Finset.univ
      (contractSetVertexMap W a) (contractSetVertexMap W b) := by
  induction h with
  | refl => exact (G.contractSet W).factorReachable_refl _ _
  | tail _ hab ih =>
      rcases hab with ⟨e, _, hdir | hdir⟩
      · rcases hdir with ⟨rfl, rfl⟩
        exact ih.trans (G.factorReachable_contractSet_endpoints W hW e)
      · rcases hdir with ⟨rfl, rfl⟩
        exact ih.trans (G.factorReachable_contractSet_endpoints W hW e).symm

/-- Every original path descends through the complementary contraction map. -/
theorem factorReachable_contractComplement_of_factorReachable
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hW : G.cutFromLeft W = ∅) {a b : X ⊕ Y}
    (h : G.FactorReachable Finset.univ a b) :
    (G.contractComplement W).FactorReachable Finset.univ
      (contractComplementVertexMap W a) (contractComplementVertexMap W b) := by
  induction h with
  | refl => exact (G.contractComplement W).factorReachable_refl _ _
  | tail _ hab ih =>
      rcases hab with ⟨e, _, hdir | hdir⟩
      · rcases hdir with ⟨rfl, rfl⟩
        exact ih.trans (G.factorReachable_contractComplement_endpoints W hW e)
      · rcases hdir with ⟨rfl, rfl⟩
        exact ih.trans (G.factorReachable_contractComplement_endpoints W hW e).symm

/-- A connected graph remains connected after contracting a nonempty `W`. -/
theorem contractSet_isConnected
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hG : G.IsConnected) (hW : G.cutFromLeft W = ∅)
    (hne : W.Nonempty) : (G.contractSet W).IsConnected := by
  constructor
  · obtain ⟨a⟩ := hG.1
    exact ⟨contractSetVertexMap W a⟩
  · intro u v
    obtain ⟨a, rfl⟩ := contractSetVertexMap_surjective W hne u
    obtain ⟨b, rfl⟩ := contractSetVertexMap_surjective W hne v
    exact G.factorReachable_contractSet_of_factorReachable W hW (hG.2 a b)

/-- A connected graph remains connected after contracting a nonempty `Wᶜ`. -/
theorem contractComplement_isConnected
    (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y))
    (hG : G.IsConnected) (hW : G.cutFromLeft W = ∅)
    (hne : Wᶜ.Nonempty) : (G.contractComplement W).IsConnected := by
  constructor
  · obtain ⟨a⟩ := hG.1
    exact ⟨contractComplementVertexMap W a⟩
  · intro u v
    obtain ⟨a, rfl⟩ := contractComplementVertexMap_surjective W hne u
    obtain ⟨b, rfl⟩ := contractComplementVertexMap_surjective W hne v
    exact G.factorReachable_contractComplement_of_factorReachable W hW (hG.2 a b)

/-- Nontrivial right-oriented tight-cut shores therefore have connected
contractions on both sides. -/
theorem IsTightCut.right_oriented_contractions_connected
    {G : BipartiteMultigraph X Y E} {W : Finset (X ⊕ Y)}
    (hT : G.IsTightCut W) (hconn : G.IsConnected)
    (hnontriv : IsNontrivialCutShore W)
    (hOrient : G.cutFromLeft W = ∅) :
    (G.contractComplement W).IsConnected ∧ (G.contractSet W).IsConnected := by
  change 1 < W.card ∧ 1 < Wᶜ.card at hnontriv
  have hW : W.Nonempty := Finset.card_pos.mp (by omega)
  have hWc : Wᶜ.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨G.contractComplement_isConnected W hconn hOrient hWc,
    G.contractSet_isConnected W hconn hOrient hW⟩

end BipartiteMultigraph
end BachThesisLean
