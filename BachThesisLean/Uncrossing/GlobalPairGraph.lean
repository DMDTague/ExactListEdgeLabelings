import BachThesisLean.Uncrossing.FibreFlip
import BachThesisLean.Uncrossing.Support

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# The active pair graph for a global uncrossing

For a full labeling `σ : E → Λ` and two selected labels `a,b`, the active
edge copies are exactly those currently carrying `a` or `b`.  Their line graph
is kept on the original edge-copy type `E`; inactive edge copies are isolated.
This lets the later global component flip avoid dependent residual edge types.
-/

noncomputable def pairEdges (σ : E → Λ) (a b : Λ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => σ e = a ∨ σ e = b)

@[simp] theorem mem_pairEdges (σ : E → Λ) (a b : Λ) (e : E) :
    e ∈ pairEdges σ a b ↔ σ e = a ∨ σ e = b := by
  classical
  simp [pairEdges]

/-- The edge-copy line graph induced by the two selected labels. -/
def pairEdgeGraph
    (G : BipartiteMultigraph X Y E) (P : Finset E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ e ∈ P ∧ f ∈ P ∧
    (G.left e = G.left f ∨ G.right e = G.right f)
  symm := by
    rintro e f ⟨hef, heP, hfP, hL | hR⟩
    · exact ⟨hef.symm, hfP, heP, Or.inl hL.symm⟩
    · exact ⟨hef.symm, hfP, heP, Or.inr hR.symm⟩
  loopless := by
    intro e h
    exact h.1 rfl

@[simp] theorem pairEdgeGraph_adj
    (G : BipartiteMultigraph X Y E) (P : Finset E) (e f : E) :
    (pairEdgeGraph G P).Adj e f ↔
      e ≠ f ∧ e ∈ P ∧ f ∈ P ∧
        (G.left e = G.left f ∨ G.right e = G.right f) := Iff.rfl

/-- Encode the selected pair by `Fin 2`, sending `a` to `0` and every other
label to `1`. On `pairEdges σ a b`, distinctness of `a,b` makes this exactly
the expected `a ↔ 0`, `b ↔ 1` encoding. -/
def pairCode (σ : E → Λ) (a : Λ) (e : E) : Fin 2 :=
  if σ e = a then 0 else 1

/-- Equality of pair codes on active edges forces equality of the underlying
selected labels. -/
theorem pairCode_eq_imp_label_eq
    (σ : E → Λ) {a b : Λ} (hab : a ≠ b) {e f : E}
    (he : e ∈ pairEdges σ a b) (hf : f ∈ pairEdges σ a b)
    (hcode : pairCode σ a e = pairCode σ a f) :
    σ e = σ f := by
  have hep := (mem_pairEdges σ a b e).1 he
  have hfp := (mem_pairEdges σ a b f).1 hf
  by_cases hea : σ e = a
  · have hfa : σ f = a := by
      by_contra hfa
      simp [pairCode, hea, hfa] at hcode
    exact hea.trans hfa.symm
  · have heb : σ e = b := hep.resolve_left hea
    have hfa : σ f ≠ a := by
      intro hfa
      simp [pairCode, hea, hfa] at hcode
    have hfb : σ f = b := hfp.resolve_left hfa
    exact heb.trans hfb.symm

/-- Any admissible full labeling gives a proper two-coloring of its active
pair graph. -/
noncomputable def admissiblePairColoring
    (G : BipartiteMultigraph X Y E)
    {L : ExactLeftLists G Λ} (σ : E → Λ) (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b) :
    (pairEdgeGraph G (pairEdges σ a b)).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (pairCode σ a) (by
    intro e f hef
    rcases hef with ⟨hef, heP, hfP, hL | hR⟩
    · intro hcode
      have hlabel := pairCode_eq_imp_label_eq σ hab heP hfP hcode
      exact hef (hσ.left_injOn (G.left e)
        ((G.mem_leftIncident (G.left e) e).2 rfl)
        ((G.mem_leftIncident (G.left e) f).2 hL.symm) hlabel)
    · intro hcode
      have hlabel := pairCode_eq_imp_label_eq σ hab heP hfP hcode
      exact hef (hσ.right_injOn (G.right e)
        ((G.mem_rightIncident (G.right e) e).2 rfl)
        ((G.mem_rightIncident (G.right e) f).2 hR.symm) hlabel))

/-- Three distinct active edge copies cannot share one left endpoint under an
admissible full labeling: the active pair has only two colors. -/
theorem no_three_active_same_left
    (G : BipartiteMultigraph X Y E)
    {L : ExactLeftLists G Λ} {σ : E → Λ} (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b)
    {e f g : E}
    (heP : e ∈ pairEdges σ a b) (hfP : f ∈ pairEdges σ a b)
    (hgP : g ∈ pairEdges σ a b)
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hefL : G.left e = G.left f) (hfgL : G.left f = G.left g) : False := by
  let c := admissiblePairColoring G σ hσ hab
  have hefAdj : (pairEdgeGraph G (pairEdges σ a b)).Adj e f :=
    ⟨hef, heP, hfP, Or.inl hefL⟩
  have hfgAdj : (pairEdgeGraph G (pairEdges σ a b)).Adj f g :=
    ⟨hfg, hfP, hgP, Or.inl hfgL⟩
  have hegAdj : (pairEdgeGraph G (pairEdges σ a b)).Adj e g :=
    ⟨heg, heP, hgP, Or.inl (hefL.trans hfgL)⟩
  have hEF := c.valid hefAdj
  have hFG := c.valid hfgAdj
  have hEG := c.valid hegAdj
  rcases finTwo_eq_zero_or_one (c e) with he0 | he1 <;>
    rcases finTwo_eq_zero_or_one (c f) with hf0 | hf1 <;>
      rcases finTwo_eq_zero_or_one (c g) with hg0 | hg1 <;>
        simp_all

/-- Three distinct active edge copies cannot share one right endpoint. -/
theorem no_three_active_same_right
    (G : BipartiteMultigraph X Y E)
    {L : ExactLeftLists G Λ} {σ : E → Λ} (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b)
    {e f g : E}
    (heP : e ∈ pairEdges σ a b) (hfP : f ∈ pairEdges σ a b)
    (hgP : g ∈ pairEdges σ a b)
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hefR : G.right e = G.right f) (hfgR : G.right f = G.right g) : False := by
  let c := admissiblePairColoring G σ hσ hab
  have hefAdj : (pairEdgeGraph G (pairEdges σ a b)).Adj e f :=
    ⟨hef, heP, hfP, Or.inr hefR⟩
  have hfgAdj : (pairEdgeGraph G (pairEdges σ a b)).Adj f g :=
    ⟨hfg, hfP, hgP, Or.inr hfgR⟩
  have hegAdj : (pairEdgeGraph G (pairEdges σ a b)).Adj e g :=
    ⟨heg, heP, hgP, Or.inr (hefR.trans hfgR)⟩
  have hEF := c.valid hefAdj
  have hFG := c.valid hfgAdj
  have hEG := c.valid hegAdj
  rcases finTwo_eq_zero_or_one (c e) with he0 | he1 <;>
    rcases finTwo_eq_zero_or_one (c f) with hf0 | hf1 <;>
      rcases finTwo_eq_zero_or_one (c g) with hg0 | hg1 <;>
        simp_all

/-- Consecutive transitions of a simple active-pair path must use opposite
shores. -/
theorem pairEdgeGraph_adj_sides_alternate
    (G : BipartiteMultigraph X Y E)
    {L : ExactLeftLists G Λ} {σ : E → Λ} (hσ : L.IsAdmissible σ)
    {a b : Λ} (hab : a ≠ b)
    {e f g : E}
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f)
    (hfg : (pairEdgeGraph G (pairEdges σ a b)).Adj f g)
    (heg : e ≠ g) :
    (G.left e = G.left f ∧ G.right f = G.right g) ∨
      (G.right e = G.right f ∧ G.left f = G.left g) := by
  rcases hef with ⟨hef_ne, heP, hfP, hefL | hefR⟩
  · rcases hfg with ⟨hfg_ne, _, hgP, hfgL | hfgR⟩
    · exact (no_three_active_same_left G hσ hab heP hfP hgP
        hef_ne hfg_ne heg hefL hfgL).elim
    · exact Or.inl ⟨hefL, hfgR⟩
  · rcases hfg with ⟨hfg_ne, _, hgP, hfgL | hfgR⟩
    · exact Or.inr ⟨hefR, hfgL⟩
    · exact (no_three_active_same_right G hσ hab heP hfP hgP
        hef_ne hfg_ne heg hefR hfgR).elim

end BachThesisLean
