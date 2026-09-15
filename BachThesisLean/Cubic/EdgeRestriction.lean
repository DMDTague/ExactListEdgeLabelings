import BachThesisLean.Cubic.Foundations

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Spanning edge restrictions

A spanning subgraph in the Pfaffian closure argument keeps both vertex shores
and restricts only the set of actual edge copies.  The restricted edge type is
a subtype, so parallel copies remain distinct and no endpoint information is
lost.
-/

/-- Keep exactly the edge copies belonging to `S`, with both vertex shores
unchanged. -/
def restrictEdges (G : BipartiteMultigraph X Y E) (S : Finset E) :
    BipartiteMultigraph X Y {e : E // e ∈ S} where
  left e := G.left e.val
  right e := G.right e.val

/-- The canonical embedding of restricted edge copies back into the ambient
edge-copy type. -/
def restrictedEdgeEmbedding (S : Finset E) : {e : E // e ∈ S} ↪ E :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Lift a finite set of restricted edge copies back to the ambient graph. -/
def liftRestrictedEdgeSet (S : Finset E)
    (T : Finset {e : E // e ∈ S}) : Finset E :=
  T.map (restrictedEdgeEmbedding S)

@[simp] theorem mem_liftRestrictedEdgeSet_iff
    (S : Finset E) (T : Finset {e : E // e ∈ S}) (e : E) :
    e ∈ liftRestrictedEdgeSet S T ↔ ∃ a ∈ T, a.val = e := by
  simp [liftRestrictedEdgeSet, restrictedEdgeEmbedding]

/-- Incidence in the restricted graph is exactly ambient incidence of the
underlying edge copy. -/
@[simp] theorem restrictEdges_incident
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (e : {e : E // e ∈ S}) (v : X ⊕ Y) :
    (G.restrictEdges S).Incident e v ↔ G.Incident e.val v := by
  cases v <;> rfl

/-- Selected incidence commutes with lifting a restricted edge set. -/
theorem selectedIncident_liftRestrictedEdgeSet
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (T : Finset {e : E // e ∈ S}) (v : X ⊕ Y) :
    G.selectedIncident (liftRestrictedEdgeSet S T) v =
      ((G.restrictEdges S).selectedIncident T v).map
        (restrictedEdgeEmbedding S) := by
  ext e
  constructor
  · intro he
    have hsel := (G.mem_selectedIncident (liftRestrictedEdgeSet S T) v e).1 he
    obtain ⟨a, haT, haVal⟩ :=
      (mem_liftRestrictedEdgeSet_iff S T e).1 hsel.1
    apply Finset.mem_map.mpr
    refine ⟨a, ?_, haVal⟩
    apply ((G.restrictEdges S).mem_selectedIncident T v a).2
    refine ⟨haT, ?_⟩
    apply (G.restrictEdges_incident S a v).2
    simpa [haVal] using hsel.2
  · intro he
    obtain ⟨a, haSel, haVal⟩ := Finset.mem_map.mp he
    have ha := ((G.restrictEdges S).mem_selectedIncident T v a).1 haSel
    apply (G.mem_selectedIncident (liftRestrictedEdgeSet S T) v e).2
    refine ⟨?_, ?_⟩
    · exact (mem_liftRestrictedEdgeSet_iff S T e).2 ⟨a, ha.1, haVal⟩
    · have hInc : G.Incident a.val v :=
        (G.restrictEdges_incident S a v).1 ha.2
      rw [← haVal]
      exact hInc

/-- Lifting preserves every selected incidence cardinality. -/
theorem selectedIncident_liftRestrictedEdgeSet_card
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (T : Finset {e : E // e ∈ S}) (v : X ⊕ Y) :
    (G.selectedIncident (liftRestrictedEdgeSet S T) v).card =
      ((G.restrictEdges S).selectedIncident T v).card := by
  rw [G.selectedIncident_liftRestrictedEdgeSet S T v]
  exact Finset.card_map _

/-- A spanning factor of a spanning edge restriction lifts to a spanning factor
of the same degree in the ambient graph. -/
theorem IsSpanningFactor.lift_restrictEdges
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    {d : ℕ} {T : Finset {e : E // e ∈ S}}
    (hT : (G.restrictEdges S).IsSpanningFactor d T) :
    G.IsSpanningFactor d (liftRestrictedEdgeSet S T) := by
  intro v
  rw [G.selectedIncident_liftRestrictedEdgeSet_card S T v]
  exact hT v

/-- In particular, a perfect matching of a spanning edge restriction is the
same collection of actual copies viewed as a perfect matching of the ambient
graph. -/
noncomputable def PerfectMatching.lift_restrictEdges
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (P : (G.restrictEdges S).PerfectMatching) : G.PerfectMatching :=
  ⟨liftRestrictedEdgeSet S P.val,
    P.property.lift_restrictEdges G S⟩

@[simp] theorem PerfectMatching.lift_restrictEdges_val
    (G : BipartiteMultigraph X Y E) (S : Finset E)
    (P : (G.restrictEdges S).PerfectMatching) :
    (P.lift_restrictEdges G S).val = liftRestrictedEdgeSet S P.val := rfl

end BipartiteMultigraph
end BachThesisLean
