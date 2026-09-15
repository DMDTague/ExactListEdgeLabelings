import BachThesisLean.Basic.Multigraph
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation

/-!
# Edge-copy foundations for the cubic theory

The vertex type is the disjoint sum of the two shores. Matchings and factors
are finite sets of actual edge copies, so parallel edges are never identified.
In particular, the complement of a perfect matching in a cubic multigraph
may contain a two-edge cycle. This file does not assert any general
prescribed-pair conjecture or a tight-cut decomposition theorem.
-/

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-- Incidence at a vertex of either shore, retaining the edge copy. -/
def Incident (G : BipartiteMultigraph X Y E) (e : E) : X ⊕ Y → Prop
  | .inl x => G.left e = x
  | .inr y => G.right e = y

instance (G : BipartiteMultigraph X Y E) (e : E) (v : X ⊕ Y) :
    Decidable (G.Incident e v) := by
  cases v <;> unfold Incident <;> infer_instance

/-- The selected incident edge copies at a vertex. -/
def selectedIncident (G : BipartiteMultigraph X Y E) (S : Finset E)
    (v : X ⊕ Y) : Finset E :=
  S.filter (fun e => G.Incident e v)

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_selectedIncident (G : BipartiteMultigraph X Y E)
    (S : Finset E) (v : X ⊕ Y) (e : E) :
    e ∈ G.selectedIncident S v ↔ e ∈ S ∧ G.Incident e v := by
  simp [selectedIncident]

/-- All incident edge copies at a vertex. -/
def incidentEdges (G : BipartiteMultigraph X Y E) (v : X ⊕ Y) : Finset E :=
  G.selectedIncident Finset.univ v

@[simp] theorem mem_incidentEdges (G : BipartiteMultigraph X Y E)
    (v : X ⊕ Y) (e : E) :
    e ∈ G.incidentEdges v ↔ G.Incident e v := by
  simp [incidentEdges]

@[simp] theorem incidentEdges_inl (G : BipartiteMultigraph X Y E) (x : X) :
    G.incidentEdges (.inl x) = G.leftIncident x := by
  ext e
  simp [Incident]

@[simp] theorem incidentEdges_inr (G : BipartiteMultigraph X Y E) (y : Y) :
    G.incidentEdges (.inr y) = G.rightIncident y := by
  ext e
  simp [Incident]

/-- A spanning edge subset with degree `d` at every vertex. -/
def IsSpanningFactor (G : BipartiteMultigraph X Y E) (d : ℕ) (S : Finset E) : Prop :=
  ∀ v : X ⊕ Y, (G.selectedIncident S v).card = d

/-- A matching contains at most one incident edge at every vertex. -/
def IsMatching (G : BipartiteMultigraph X Y E) (S : Finset E) : Prop :=
  ∀ v : X ⊕ Y, (G.selectedIncident S v).card ≤ 1

/-- A perfect matching covers every vertex exactly once. -/
def IsPerfectMatching (G : BipartiteMultigraph X Y E) (S : Finset E) : Prop :=
  G.IsSpanningFactor 1 S

/-- A spanning two-factor; parallel two-edge cycles are permitted. -/
def IsTwoFactor (G : BipartiteMultigraph X Y E) (S : Finset E) : Prop :=
  G.IsSpanningFactor 2 S

instance (G : BipartiteMultigraph X Y E) (d : ℕ) (S : Finset E) :
    Decidable (G.IsSpanningFactor d S) :=
  inferInstanceAs (Decidable (∀ v : X ⊕ Y, (G.selectedIncident S v).card = d))

instance (G : BipartiteMultigraph X Y E) (S : Finset E) :
    Decidable (G.IsMatching S) :=
  inferInstanceAs (Decidable (∀ v : X ⊕ Y, (G.selectedIncident S v).card ≤ 1))

instance (G : BipartiteMultigraph X Y E) (S : Finset E) :
    Decidable (G.IsPerfectMatching S) :=
  inferInstanceAs (Decidable (G.IsSpanningFactor 1 S))

instance (G : BipartiteMultigraph X Y E) (S : Finset E) :
    Decidable (G.IsTwoFactor S) :=
  inferInstanceAs (Decidable (G.IsSpanningFactor 2 S))

def PerfectMatching (G : BipartiteMultigraph X Y E) :=
  {S : Finset E // G.IsPerfectMatching S}

def TwoFactor (G : BipartiteMultigraph X Y E) :=
  {S : Finset E // G.IsTwoFactor S}

instance (G : BipartiteMultigraph X Y E) : Fintype G.PerfectMatching :=
  inferInstanceAs (Fintype {S : Finset E // G.IsPerfectMatching S})

instance (G : BipartiteMultigraph X Y E) : Fintype G.TwoFactor :=
  inferInstanceAs (Fintype {S : Finset E // G.IsTwoFactor S})

/-- Cubicity imposes degree three on both shores. -/
def IsCubic (G : BipartiteMultigraph X Y E) : Prop :=
  ∀ v : X ⊕ Y, (G.incidentEdges v).card = 3

instance (G : BipartiteMultigraph X Y E) : Decidable G.IsCubic :=
  inferInstanceAs (Decidable (∀ v : X ⊕ Y, (G.incidentEdges v).card = 3))

theorem isCubic_iff (G : BipartiteMultigraph X Y E) :
    G.IsCubic ↔ G.IsLeftRegular 3 ∧ G.IsRightRegular 3 := by
  simp only [IsCubic, Sum.forall, incidentEdges_inl, incidentEdges_inr,
    IsLeftRegular, IsRightRegular, leftDegree, rightDegree]

theorem selectedIncident_subset (G : BipartiteMultigraph X Y E)
    (S : Finset E) (v : X ⊕ Y) :
    G.selectedIncident S v ⊆ G.incidentEdges v := by
  intro e he
  exact (mem_incidentEdges G v e).2 ((mem_selectedIncident G S v e).1 he).2

theorem selectedIncident_compl (G : BipartiteMultigraph X Y E)
    (S : Finset E) (v : X ⊕ Y) :
    G.selectedIncident Sᶜ v = G.incidentEdges v \ G.selectedIncident S v := by
  ext e
  simp only [mem_selectedIncident, Finset.mem_compl, Finset.mem_sdiff,
    mem_incidentEdges]
  tauto

/-- The selected and unselected incidence counts partition the full degree. -/
theorem selectedIncident_compl_card_add (G : BipartiteMultigraph X Y E)
    (S : Finset E) (v : X ⊕ Y) :
    (G.selectedIncident Sᶜ v).card + (G.selectedIncident S v).card =
      (G.incidentEdges v).card := by
  rw [selectedIncident_compl]
  exact Finset.card_sdiff_add_card_eq_card (G.selectedIncident_subset S v)

theorem selectedIncident_compl_card (G : BipartiteMultigraph X Y E)
    (S : Finset E) (v : X ⊕ Y) :
    (G.selectedIncident Sᶜ v).card =
      (G.incidentEdges v).card - (G.selectedIncident S v).card := by
  have h := G.selectedIncident_compl_card_add S v
  omega

/-- Cardinal matching semantics agree with pairwise nonincidence. -/
theorem isMatching_iff (G : BipartiteMultigraph X Y E) (S : Finset E) :
    G.IsMatching S ↔
      ∀ e ∈ S, ∀ f ∈ S, ∀ v, G.Incident e v → G.Incident f v → e = f := by
  constructor
  · intro h e he f hf v hev hfv
    exact (Finset.card_le_one.mp (h v)) e (by simp [he, hev]) f (by simp [hf, hfv])
  · intro h v
    apply Finset.card_le_one.mpr
    intro e he f hf
    rw [mem_selectedIncident] at he hf
    exact h e he.1 f hf.1 v he.2 hf.2

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] in
theorem IsPerfectMatching.isMatching {G : BipartiteMultigraph X Y E}
    {S : Finset E} (h : G.IsPerfectMatching S) : G.IsMatching S := by
  intro v
  exact (h v).le

/-- A perfect matching really selects a unique edge copy at each vertex. -/
theorem IsPerfectMatching.existsUnique_incident {G : BipartiteMultigraph X Y E}
    {S : Finset E} (h : G.IsPerfectMatching S) (v : X ⊕ Y) :
    ∃! e, e ∈ S ∧ G.Incident e v := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (h v)
  refine ⟨e, ?_, ?_⟩
  · exact (mem_selectedIncident G S v e).1 (by rw [he]; simp)
  · intro f hf
    have : f ∈ G.selectedIncident S v := (mem_selectedIncident G S v f).2 hf
    simpa [he] using this

theorem perfectMatching_compl_iff_twoFactor (G : BipartiteMultigraph X Y E)
    (hG : G.IsCubic) (S : Finset E) :
    G.IsPerfectMatching S ↔ G.IsTwoFactor Sᶜ := by
  constructor
  · intro h v
    have hc := G.selectedIncident_compl_card_add S v
    have hd := hG v
    have hm := h v
    omega
  · intro h v
    have hc := G.selectedIncident_compl_card_add S v
    have hd := hG v
    have hm := h v
    omega

/-- Complementation is an explicit involutive bijection in a cubic graph. -/
def perfectMatchingEquivTwoFactor (G : BipartiteMultigraph X Y E)
    (hG : G.IsCubic) : G.PerfectMatching ≃ G.TwoFactor where
  toFun P := ⟨P.valᶜ, (G.perfectMatching_compl_iff_twoFactor hG P.val).1 P.property⟩
  invFun H := ⟨H.valᶜ, (G.perfectMatching_compl_iff_twoFactor hG H.valᶜ).2 (by
    simpa using H.property)⟩
  left_inv P := by apply Subtype.ext; simp
  right_inv H := by apply Subtype.ext; simp

@[simp] theorem perfectMatchingEquivTwoFactor_apply_val
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (P : G.PerfectMatching) :
    (G.perfectMatchingEquivTwoFactor hG P).val = P.valᶜ := rfl

@[simp] theorem perfectMatchingEquivTwoFactor_symm_apply_val
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) (H : G.TwoFactor) :
    ((G.perfectMatchingEquivTwoFactor hG).symm H).val = H.valᶜ := rfl

theorem card_perfectMatching_eq_card_twoFactor (G : BipartiteMultigraph X Y E)
    (hG : G.IsCubic) : Fintype.card G.PerfectMatching = Fintype.card G.TwoFactor :=
  Fintype.card_congr (G.perfectMatchingEquivTwoFactor hG)

/-- Adjacent vertices are joined by an actual selected edge copy. -/
def SelectedAdjacent (G : BipartiteMultigraph X Y E) (S : Finset E)
    (u v : X ⊕ Y) : Prop :=
  ∃ e ∈ S, (u = .inl (G.left e) ∧ v = .inr (G.right e)) ∨
    (u = .inr (G.right e) ∧ v = .inl (G.left e))

/-- Reachability in the edge subset, including the zero-length path. -/
def FactorReachable (G : BipartiteMultigraph X Y E) (S : Finset E)
    (u v : X ⊕ Y) : Prop :=
  Relation.ReflTransGen (G.SelectedAdjacent S) u v

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] [DecidableEq E] in
theorem selectedAdjacent_symm (G : BipartiteMultigraph X Y E) (S : Finset E) :
    Symmetric (G.SelectedAdjacent S) := by
  rintro u v ⟨e, he, h | h⟩
  · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨e, he, Or.inl ⟨h.2, h.1⟩⟩

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] [DecidableEq E] in
theorem factorReachable_refl (G : BipartiteMultigraph X Y E)
    (S : Finset E) (v : X ⊕ Y) : G.FactorReachable S v v :=
  Relation.ReflTransGen.refl

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] [DecidableEq E] in
theorem FactorReachable.symm {G : BipartiteMultigraph X Y E}
    {S : Finset E} {u v : X ⊕ Y} (h : G.FactorReachable S u v) :
    G.FactorReachable S v u :=
  Relation.ReflTransGen.symmetric (G.selectedAdjacent_symm S) h

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] [DecidableEq E] in
theorem FactorReachable.trans {G : BipartiteMultigraph X Y E}
    {S : Finset E} {u v w : X ⊕ Y} (h : G.FactorReachable S u v)
    (h' : G.FactorReachable S v w) : G.FactorReachable S u w :=
  Relation.ReflTransGen.trans h h'

/- Any vertex invariant preserved by selected edges is preserved along a component. -/
omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] [DecidableEq E] in
theorem FactorReachable.map_eq {G : BipartiteMultigraph X Y E}
    {S : Finset E} {u v : X ⊕ Y} {Z : Type*} (h : G.FactorReachable S u v)
    (f : X ⊕ Y → Z)
    (hf : ∀ a b, G.SelectedAdjacent S a b → f a = f b) : f u = f v := by
  induction h with
  | refl => rfl
  | tail _ hab ih => exact ih.trans (hf _ _ hab)

omit [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] [DecidableEq E] in
theorem factorReachable_endpoints (G : BipartiteMultigraph X Y E)
    {S : Finset E} {e : E} (he : e ∈ S) :
    G.FactorReachable S (.inl (G.left e)) (.inr (G.right e)) :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- An edge on a component is selected; endpoint connectivity alone is insufficient. -/
def ComponentCarries (G : BipartiteMultigraph X Y E) (S : Finset E)
    (root : X ⊕ Y) (e : E) : Prop :=
  e ∈ S ∧ G.FactorReachable S root (.inl (G.left e))

theorem ComponentCarries.reachable_incident {G : BipartiteMultigraph X Y E}
    {S : Finset E} {root v : X ⊕ Y} {e : E}
    (h : G.ComponentCarries S root e) (hv : G.Incident e v) :
    G.FactorReachable S root v := by
  cases v with
  | inl x =>
    change G.left e = x at hv
    simpa [← hv] using h.2
  | inr y =>
    change G.right e = y at hv
    simpa [← hv] using h.2.trans (G.factorReachable_endpoints h.1)

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem not_componentCarries_of_mem_matching (G : BipartiteMultigraph X Y E)
    (P : Finset E) (root : X ⊕ Y) {e : E} (he : e ∈ P) :
    ¬ G.ComponentCarries Pᶜ root e := by
  intro h
  exact (Finset.mem_compl.mp h.1) he

/-- Connected means nonempty and all vertices are mutually reachable. -/
def IsConnected (G : BipartiteMultigraph X Y E) : Prop :=
  Nonempty (X ⊕ Y) ∧ ∀ u v, G.FactorReachable Finset.univ u v

/-- The edge boundary of a set of vertices; each parallel copy is retained. -/
def edgeCut (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) : Finset E :=
  Finset.univ.filter (fun e =>
    (Sum.inl (G.left e) ∈ W ∧ Sum.inr (G.right e) ∉ W) ∨
    (Sum.inl (G.left e) ∉ W ∧ Sum.inr (G.right e) ∈ W))

omit [DecidableEq E] in
@[simp] theorem edgeCut_compl (G : BipartiteMultigraph X Y E)
    (W : Finset (X ⊕ Y)) : G.edgeCut Wᶜ = G.edgeCut W := by
  ext e
  simp only [edgeCut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  tauto

/-- Every perfect matching uses exactly one cut edge. -/
def IsTightCut (G : BipartiteMultigraph X Y E) (W : Finset (X ⊕ Y)) : Prop :=
  ∀ P : Finset E, G.IsPerfectMatching P → (P ∩ G.edgeCut W).card = 1

/-- Both shores of a nontrivial cut contain at least two vertices. -/
def IsNontrivialCutShore (W : Finset (X ⊕ Y)) : Prop :=
  1 < W.card ∧ 1 < Wᶜ.card

def IsMatchingCovered (G : BipartiteMultigraph X Y E) : Prop :=
  G.IsConnected ∧ Nonempty G.PerfectMatching ∧
    ∀ e, ∃ P : Finset E, G.IsPerfectMatching P ∧ e ∈ P

/-- The matching-covered, no-nontrivial-tight-cut convention for a brace. -/
def IsBrace (G : BipartiteMultigraph X Y E) : Prop :=
  G.IsMatchingCovered ∧
    ∀ W, IsNontrivialCutShore W → ¬ G.IsTightCut W

/-- Ports enumerate incident edge copies, not distinct neighbouring vertices. -/
abbrev PortEnumeration (G : BipartiteMultigraph X Y E) (r : X ⊕ Y) :=
  Fin 3 ≃ {e : E // e ∈ G.incidentEdges r}

/-- Cubicity supplies an enumeration, with a classical choice of its order. -/
noncomputable def portsOfCubic (G : BipartiteMultigraph X Y E)
    (hG : G.IsCubic) (r : X ⊕ Y) : G.PortEnumeration r :=
  (Finset.equivFinOfCardEq (hG r)).symm

/-- Exactly one of the three named edge copies is selected by a perfect matching. -/
theorem IsPerfectMatching.existsUnique_port {G : BipartiteMultigraph X Y E}
    {P : Finset E} (hP : G.IsPerfectMatching P) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) : ∃! i : Fin 3, (ports i).val ∈ P := by
  obtain ⟨e, he, hunique⟩ := hP.existsUnique_incident r
  let er : {e : E // e ∈ G.incidentEdges r} := ⟨e, (mem_incidentEdges G r e).2 he.2⟩
  refine ⟨ports.symm er, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using he.1
  · intro i hi
    apply ports.injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    exact hunique (ports i).val ⟨hi, (mem_incidentEdges G r _).1 (ports i).property⟩

/-- The edge-root mask; the manuscript uses it for edges nonincident with `r`. -/
noncomputable def edgeRootMask (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun i => ∃ P : Finset E,
    G.IsPerfectMatching P ∧ (ports i).val ∈ P ∧ G.ComponentCarries Pᶜ r e)

/-- Vertex-root masks are separate from edge-root masks. -/
noncomputable def vertexRootMask (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (v : X ⊕ Y) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun i => ∃ P : Finset E,
    G.IsPerfectMatching P ∧ (ports i).val ∈ P ∧ G.FactorReachable Pᶜ r v)

@[simp] theorem mem_edgeRootMask (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) (i : Fin 3) :
    i ∈ G.edgeRootMask r ports e ↔ ∃ P : Finset E,
      G.IsPerfectMatching P ∧ (ports i).val ∈ P ∧ G.ComponentCarries Pᶜ r e := by
  classical
  simp [edgeRootMask]

@[simp] theorem mem_vertexRootMask (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (v : X ⊕ Y) (i : Fin 3) :
    i ∈ G.vertexRootMask r ports v ↔ ∃ P : Finset E,
      G.IsPerfectMatching P ∧ (ports i).val ∈ P ∧ G.FactorReachable Pᶜ r v := by
  classical
  simp [vertexRootMask]

/-- The prescribed two-edge property of v13.23. -/
def HasEEP (G : BipartiteMultigraph X Y E) : Prop :=
  ∀ e f : E, e ≠ f → ∃ P : Finset E, ∃ root : X ⊕ Y,
    G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
      G.ComponentCarries Pᶜ root f

/-- The prescribed edge-vertex property of v13.23. -/
def HasEVP (G : BipartiteMultigraph X Y E) : Prop :=
  ∀ (e : E) (v : X ⊕ Y), ∃ P : Finset E, ∃ root : X ⊕ Y,
    G.IsPerfectMatching P ∧ G.ComponentCarries Pᶜ root e ∧
      G.FactorReachable Pᶜ root v

/-- Vertex and edge elements are tagged, even when their underlying types coincide. -/
def ComponentContains (G : BipartiteMultigraph X Y E) (S : Finset E)
    (root : X ⊕ Y) : (X ⊕ Y) ⊕ E → Prop
  | .inl v => G.FactorReachable S root v
  | .inr e => G.ComponentCarries S root e

def HasTwoEP (G : BipartiteMultigraph X Y E) : Prop :=
  ∀ a b : (X ⊕ Y) ⊕ E, a ≠ b → ∃ P : Finset E, ∃ root : X ⊕ Y,
    G.IsPerfectMatching P ∧ G.ComponentContains Pᶜ root a ∧
      G.ComponentContains Pᶜ root b

theorem IsCubic.exists_incident_ne {G : BipartiteMultigraph X Y E}
    (hG : G.IsCubic) (v : X ⊕ Y) (e : E) :
    ∃ f, G.Incident f v ∧ f ≠ e := by
  have hcard : 1 < (G.incidentEdges v).card := by rw [hG v]; decide
  obtain ⟨f, hf, hne⟩ := Finset.exists_mem_ne hcard e
  exact ⟨f, (mem_incidentEdges G v f).1 hf, hne⟩

/-- The EEP-to-EVP implication uses actual incidence, including parallel copies. -/
theorem HasEEP.hasEVP {G : BipartiteMultigraph X Y E}
    (hEEP : G.HasEEP) (hG : G.IsCubic) : G.HasEVP := by
  intro e v
  obtain ⟨f, hf, hfe⟩ := hG.exists_incident_ne v e
  obtain ⟨P, root, hP, he, hcarry⟩ := hEEP e f hfe.symm
  exact ⟨P, root, hP, he, hcarry.reachable_incident hf⟩

omit [Fintype X] [Fintype Y] in
theorem HasTwoEP.hasEEP {G : BipartiteMultigraph X Y E}
    (h : G.HasTwoEP) : G.HasEEP := by
  intro e f hef
  exact h (.inr e) (.inr f) (by simpa using hef)

/-- The full equivalence in Lemma `lem:eep-2ep`, with an explicit cubic premise. -/
theorem hasEEP_iff_hasTwoEP (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) :
    G.HasEEP ↔ G.HasTwoEP := by
  refine ⟨?_, HasTwoEP.hasEEP⟩
  intro h a b hab
  have hev := h.hasEVP hG
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      have hcard : 0 < (G.incidentEdges u).card := by rw [hG u]; decide
      obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
      obtain ⟨P, root, hP, heP, hv⟩ := hev e v
      exact ⟨P, root, hP, heP.reachable_incident ((mem_incidentEdges G u e).1 he), hv⟩
    | inr f =>
      obtain ⟨P, root, hP, hf, hu⟩ := hev f u
      exact ⟨P, root, hP, hu, hf⟩
  | inr e =>
    cases b with
    | inl v => exact hev e v
    | inr f => exact h e f (by simpa using hab)

end BipartiteMultigraph
end BachThesisLean
