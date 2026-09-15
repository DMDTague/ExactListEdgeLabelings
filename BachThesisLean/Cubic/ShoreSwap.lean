import BachThesisLean.Cubic.PortMasks

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Exchanging the bipartition shores

The manuscript's amplifier argument is symmetric in the two shores.  This file
makes that symmetry explicit in the edge-copy model.  Edge copies and edge
subsets are unchanged; only the left/right endpoint maps and vertex tags are
exchanged.
-/

/-- Exchange the two shores of a bipartite edge-copy multigraph. -/
def shoreSwap (G : BipartiteMultigraph X Y E) : BipartiteMultigraph Y X E where
  left := G.right
  right := G.left

@[simp] theorem shoreSwap_left (G : BipartiteMultigraph X Y E) (e : E) :
    G.shoreSwap.left e = G.right e := rfl

@[simp] theorem shoreSwap_right (G : BipartiteMultigraph X Y E) (e : E) :
    G.shoreSwap.right e = G.left e := rfl

/-- Exchange the tags of a bipartite vertex. -/
def shoreSwapVertex : X ⊕ Y → Y ⊕ X
  | .inl x => .inr x
  | .inr y => .inl y

@[simp] theorem shoreSwapVertex_inl (x : X) :
    shoreSwapVertex (Sum.inl x : X ⊕ Y) = (Sum.inr x : Y ⊕ X) := rfl

@[simp] theorem shoreSwapVertex_inr (y : Y) :
    shoreSwapVertex (Sum.inr y : X ⊕ Y) = (Sum.inl y : Y ⊕ X) := rfl

@[simp] theorem shoreSwapVertex_involutive (z : X ⊕ Y) :
    shoreSwapVertex (shoreSwapVertex z) = z := by
  cases z <;> rfl

@[simp] theorem shoreSwap_incident_iff
    (G : BipartiteMultigraph X Y E) (e : E) (z : X ⊕ Y) :
    G.shoreSwap.Incident e (shoreSwapVertex z) ↔ G.Incident e z := by
  cases z <;> rfl

@[simp] theorem shoreSwap_selectedIncident
    (G : BipartiteMultigraph X Y E) (S : Finset E) (z : X ⊕ Y) :
    G.shoreSwap.selectedIncident S (shoreSwapVertex z) =
      G.selectedIncident S z := by
  ext e
  simp

/-- Perfect-matching status is unchanged by exchanging shores. -/
theorem shoreSwap_isPerfectMatching_iff
    (G : BipartiteMultigraph X Y E) (S : Finset E) :
    G.shoreSwap.IsPerfectMatching S ↔ G.IsPerfectMatching S := by
  constructor
  · intro h z
    have hz := h (shoreSwapVertex z)
    simpa using hz
  · intro h z
    cases z with
    | inl y => simpa using h (.inr y)
    | inr x => simpa using h (.inl x)

/-- Two-factor status is unchanged by exchanging shores. -/
theorem shoreSwap_isTwoFactor_iff
    (G : BipartiteMultigraph X Y E) (S : Finset E) :
    G.shoreSwap.IsTwoFactor S ↔ G.IsTwoFactor S := by
  constructor
  · intro h z
    have hz := h (shoreSwapVertex z)
    simpa using hz
  · intro h z
    cases z with
    | inl y => simpa using h (.inr y)
    | inr x => simpa using h (.inl x)

/-- Cubicity is shore-symmetric. -/
theorem shoreSwap_isCubic_iff (G : BipartiteMultigraph X Y E) :
    G.shoreSwap.IsCubic ↔ G.IsCubic := by
  constructor
  · intro h z
    have hz := h (shoreSwapVertex z)
    simpa [incidentEdges] using hz
  · intro h z
    cases z with
    | inl y => simpa [incidentEdges] using h (.inr y)
    | inr x => simpa [incidentEdges] using h (.inl x)

/-- Selected adjacency transports through the vertex shore swap. -/
theorem shoreSwap_selectedAdjacent_iff
    (G : BipartiteMultigraph X Y E) (S : Finset E) (a b : Y ⊕ X) :
    G.shoreSwap.SelectedAdjacent S a b ↔
      G.SelectedAdjacent S (shoreSwapVertex a) (shoreSwapVertex b) := by
  cases a <;> cases b <;>
    simp [SelectedAdjacent, shoreSwap, shoreSwapVertex]

/-- Factor reachability is exactly preserved by shore exchange. -/
theorem shoreSwap_factorReachable_iff
    (G : BipartiteMultigraph X Y E) (S : Finset E) (a b : X ⊕ Y) :
    G.shoreSwap.FactorReachable S (shoreSwapVertex a) (shoreSwapVertex b) ↔
      G.FactorReachable S a b := by
  constructor
  · intro h
    have h' := Relation.ReflTransGen.lift
      (fun z : Y ⊕ X => shoreSwapVertex z)
      (fun u v huv => (G.shoreSwap_selectedAdjacent_iff S u v).1 huv) h
    simpa using h'
  · intro h
    have h' := Relation.ReflTransGen.lift
      (fun z : X ⊕ Y => shoreSwapVertex z)
      (fun u v huv => by
        apply (G.shoreSwap_selectedAdjacent_iff S
          (shoreSwapVertex u) (shoreSwapVertex v)).2
        simpa using huv) h
    exact h'

/-- Edge-component membership is preserved, even though `ComponentCarries`
chooses the left endpoint as its canonical representative. -/
theorem shoreSwap_componentCarries_iff
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (root : X ⊕ Y) (e : E) :
    G.shoreSwap.ComponentCarries S (shoreSwapVertex root) e ↔
      G.ComponentCarries S root e := by
  constructor
  · rintro ⟨he, hr⟩
    have hright : G.FactorReachable S root (.inr (G.right e)) := by
      exact (G.shoreSwap_factorReachable_iff S root (.inr (G.right e))).1 hr
    exact ⟨he, hright.trans (G.factorReachable_endpoints he).symm⟩
  · rintro ⟨he, hl⟩
    have hright : G.FactorReachable S root (.inr (G.right e)) :=
      hl.trans (G.factorReachable_endpoints he)
    exact ⟨he,
      (G.shoreSwap_factorReachable_iff S root (.inr (G.right e))).2 hright⟩

/-- Connectedness is shore-symmetric. -/
theorem shoreSwap_isConnected_iff (G : BipartiteMultigraph X Y E) :
    G.shoreSwap.IsConnected ↔ G.IsConnected := by
  constructor
  · rintro ⟨⟨z⟩, hconn⟩
    refine ⟨⟨shoreSwapVertex z⟩, ?_⟩
    intro a b
    exact (G.shoreSwap_factorReachable_iff Finset.univ a b).1
      (hconn (shoreSwapVertex a) (shoreSwapVertex b))
  · rintro ⟨⟨z⟩, hconn⟩
    refine ⟨⟨shoreSwapVertex z⟩, ?_⟩
    intro a b
    cases a with
    | inl y =>
      cases b with
      | inl y' =>
        exact (G.shoreSwap_factorReachable_iff Finset.univ (.inr y) (.inr y')).2
          (hconn (.inr y) (.inr y'))
      | inr x' =>
        exact (G.shoreSwap_factorReachable_iff Finset.univ (.inr y) (.inl x')).2
          (hconn (.inr y) (.inl x'))
    | inr x =>
      cases b with
      | inl y' =>
        exact (G.shoreSwap_factorReachable_iff Finset.univ (.inl x) (.inr y')).2
          (hconn (.inl x) (.inr y'))
      | inr x' =>
        exact (G.shoreSwap_factorReachable_iff Finset.univ (.inl x) (.inl x')).2
          (hconn (.inl x) (.inl x'))

/-- EEP is invariant under exchanging the shores. -/
theorem shoreSwap_hasEEP_iff (G : BipartiteMultigraph X Y E) :
    G.shoreSwap.HasEEP ↔ G.HasEEP := by
  constructor
  · intro h e f hef
    obtain ⟨P, root, hP, he, hf⟩ := h e f hef
    refine ⟨P, shoreSwapVertex root,
      (G.shoreSwap_isPerfectMatching_iff P).1 hP, ?_, ?_⟩
    · have he' : G.shoreSwap.ComponentCarries Pᶜ
          (shoreSwapVertex (shoreSwapVertex root)) e := by
        simpa using he
      exact (G.shoreSwap_componentCarries_iff Pᶜ (shoreSwapVertex root) e).1 he'
    · have hf' : G.shoreSwap.ComponentCarries Pᶜ
          (shoreSwapVertex (shoreSwapVertex root)) f := by
        simpa using hf
      exact (G.shoreSwap_componentCarries_iff Pᶜ (shoreSwapVertex root) f).1 hf'
  · intro h e f hef
    obtain ⟨P, root, hP, he, hf⟩ := h e f hef
    refine ⟨P, shoreSwapVertex root,
      (G.shoreSwap_isPerfectMatching_iff P).2 hP, ?_, ?_⟩
    · exact (G.shoreSwap_componentCarries_iff Pᶜ root e).2 he
    · exact (G.shoreSwap_componentCarries_iff Pᶜ root f).2 hf

/-- EVP is invariant under exchanging the shores. -/
theorem shoreSwap_hasEVP_iff (G : BipartiteMultigraph X Y E) :
    G.shoreSwap.HasEVP ↔ G.HasEVP := by
  constructor
  · intro h e v
    obtain ⟨P, root, hP, he, hv⟩ := h e (shoreSwapVertex v)
    refine ⟨P, shoreSwapVertex root,
      (G.shoreSwap_isPerfectMatching_iff P).1 hP, ?_, ?_⟩
    · have he' : G.shoreSwap.ComponentCarries Pᶜ
          (shoreSwapVertex (shoreSwapVertex root)) e := by
        simpa using he
      exact (G.shoreSwap_componentCarries_iff Pᶜ (shoreSwapVertex root) e).1 he'
    · have hv' :=
        (G.shoreSwap_factorReachable_iff Pᶜ
          (shoreSwapVertex root) v).1 (by simpa using hv)
      simpa using hv'
  · intro h e v
    obtain ⟨P, root, hP, he, hv⟩ := h e (shoreSwapVertex v)
    refine ⟨P, shoreSwapVertex root,
      (G.shoreSwap_isPerfectMatching_iff P).2 hP, ?_, ?_⟩
    · exact (G.shoreSwap_componentCarries_iff Pᶜ root e).2 he
    · have hv' := (G.shoreSwap_factorReachable_iff Pᶜ root
        (shoreSwapVertex v)).2 (by simpa using hv)
      simpa using hv'

/-- Transport a named three-port enumeration across the shore exchange. -/
noncomputable def shoreSwapPortEnumeration
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) :
    G.shoreSwap.PortEnumeration (shoreSwapVertex r) where
  toFun i := ⟨(ports i).1, by
    apply (mem_incidentEdges G.shoreSwap (shoreSwapVertex r) (ports i).1).2
    exact (G.shoreSwap_incident_iff (ports i).1 r).2
      ((mem_incidentEdges G r (ports i).1).1 (ports i).property)⟩
  invFun er := ports.symm ⟨er.1, by
    apply (mem_incidentEdges G r er.1).2
    exact (G.shoreSwap_incident_iff er.1 r).1
      ((mem_incidentEdges G.shoreSwap (shoreSwapVertex r) er.1).1 er.property)⟩
  left_inv i := by simp
  right_inv er := by apply Subtype.ext; simp

@[simp] theorem shoreSwapPortEnumeration_apply_val
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (i : Fin 3) :
    ((G.shoreSwapPortEnumeration r ports) i).1 = (ports i).1 := rfl

/-- Edge-root masks are literally unchanged after transporting the root and
its port names across the shore exchange. -/
theorem shoreSwap_edgeRootMask
    (G : BipartiteMultigraph X Y E) (r : X ⊕ Y)
    (ports : G.PortEnumeration r) (e : E) :
    G.shoreSwap.edgeRootMask (shoreSwapVertex r)
        (G.shoreSwapPortEnumeration r ports) e =
      G.edgeRootMask r ports e := by
  classical
  ext i
  rw [mem_edgeRootMask, mem_edgeRootMask]
  constructor
  · rintro ⟨P, hP, hiP, he⟩
    refine ⟨P, (G.shoreSwap_isPerfectMatching_iff P).1 hP, ?_, ?_⟩
    · simpa using hiP
    · exact (G.shoreSwap_componentCarries_iff Pᶜ r e).1 he
  · rintro ⟨P, hP, hiP, he⟩
    refine ⟨P, (G.shoreSwap_isPerfectMatching_iff P).2 hP, ?_, ?_⟩
    · simpa using hiP
    · exact (G.shoreSwap_componentCarries_iff Pᶜ r e).2 he

end BipartiteMultigraph
end BachThesisLean
