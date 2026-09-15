import BachThesisLean.Uncrossing.GlobalPairParity

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq E] [DecidableEq Λ]

/-!
# Global component flip for one uncrossed support pair

For an admissible labeling of an uncrossed support family, only edges carrying
the selected labels `a,b` may change.  We mark exactly those active-pair
components that contain a left endpoint in `S b \ S a`; on a marked component
we swap `a` and `b`.  The active edge set is invariant under this swap, which
makes the transformation an involution on all labelings.
-/

/-- An active edge is marked when its active-pair component contains an active
edge at a `S b \ S a` left endpoint. -/
def reachesRightSdiffGlobal
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (σ : E → Λ) (e : E) : Prop :=
  e ∈ pairEdges σ a b ∧
    ∃ f : E, f ∈ pairEdges σ a b ∧
      (pairEdgeGraph G (pairEdges σ a b)).Reachable e f ∧
      G.left f ∈ S b ∧ G.left f ∉ S a

/-- The global component mark is constant across an active-pair adjacency. -/
theorem reachesRightSdiffGlobal_adj_iff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (σ : E → Λ) {e f : E}
    (hef : (pairEdgeGraph G (pairEdges σ a b)).Adj e f) :
    reachesRightSdiffGlobal G S a b σ e ↔
      reachesRightSdiffGlobal G S a b σ f := by
  have hefReach : (pairEdgeGraph G (pairEdges σ a b)).Reachable e f := hef.reachable
  have hfeReach : (pairEdgeGraph G (pairEdges σ a b)).Reachable f e := hef.symm.reachable
  rcases hef with ⟨_, heP, hfP, _⟩
  constructor
  · rintro ⟨_, g, hgP, heg, hgB, hgA⟩
    exact ⟨hfP, g, hgP, hfeReach.trans heg, hgB, hgA⟩
  · rintro ⟨_, g, hgP, hfg, hgB, hgA⟩
    exact ⟨heP, g, hgP, hefReach.trans hfg, hgB, hgA⟩

/-- Active edges sharing a left endpoint have the same component mark. -/
theorem reachesRightSdiffGlobal_same_left_iff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (σ : E → Λ) {e f : E}
    (heP : e ∈ pairEdges σ a b) (hfP : f ∈ pairEdges σ a b)
    (hleft : G.left e = G.left f) :
    reachesRightSdiffGlobal G S a b σ e ↔
      reachesRightSdiffGlobal G S a b σ f := by
  by_cases hef : e = f
  · subst f
    rfl
  · exact reachesRightSdiffGlobal_adj_iff G S a b σ
      ⟨hef, heP, hfP, Or.inl hleft⟩

/-- Active edges sharing a right endpoint have the same component mark. -/
theorem reachesRightSdiffGlobal_same_right_iff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (σ : E → Λ) {e f : E}
    (heP : e ∈ pairEdges σ a b) (hfP : f ∈ pairEdges σ a b)
    (hright : G.right e = G.right f) :
    reachesRightSdiffGlobal G S a b σ e ↔
      reachesRightSdiffGlobal G S a b σ f := by
  by_cases hef : e = f
  · subst f
    rfl
  · exact reachesRightSdiffGlobal_adj_iff G S a b σ
      ⟨hef, heP, hfP, Or.inr hright⟩

/-- An active edge at a `S b \ S a` endpoint marks its own component. -/
theorem reachesRightSdiffGlobal_of_right_sdiff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (σ : E → Λ) {e : E}
    (heP : e ∈ pairEdges σ a b)
    (hB : G.left e ∈ S b) (hA : G.left e ∉ S a) :
    reachesRightSdiffGlobal G S a b σ e := by
  exact ⟨heP, e, heP, SimpleGraph.Reachable.rfl, hB, hA⟩

/-- Under an admissible uncrossed labeling, an active edge at a
`S a \ S b` endpoint is never marked. -/
theorem not_reachesRightSdiffGlobal_of_left_sdiff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b)
    (hinc : ExactSupportIncidence G (uncross S a b))
    {σ : E → Λ}
    (hσ : (exactListsOfSupports (uncross S a b) hinc).IsAdmissible σ)
    {e : E} (heP : e ∈ pairEdges σ a b)
    (hA : G.left e ∈ S a) (hB : G.left e ∉ S b) :
    ¬ reachesRightSdiffGlobal G S a b σ e := by
  rintro ⟨_, f, hfP, hef, hfB, hfA⟩
  exact no_reachable_opposite_sdiff_global
    G S hab hinc hσ heP hfP hA hB hfB hfA hef

/-- Swap `a,b` on precisely the marked active components. -/
noncomputable def globalPairFlip
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (a b : Λ) (σ : E → Λ) : E → Λ := by
  classical
  exact fun e =>
    if reachesRightSdiffGlobal G S a b σ e then
      Equiv.swap a b (σ e)
    else σ e

/-- The component flip preserves membership in the selected active pair. -/
theorem globalPairFlip_mem_pair_iff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (σ : E → Λ) (e : E) :
    (globalPairFlip G S a b σ e = a ∨ globalPairFlip G S a b σ e = b) ↔
      (σ e = a ∨ σ e = b) := by
  classical
  by_cases hm : reachesRightSdiffGlobal G S a b σ e
  · have hp := (mem_pairEdges σ a b e).1 hm.1
    rcases hp with ha | hb
    · simp [globalPairFlip, hm, ha, hab]
    · simp [globalPairFlip, hm, hb, hab]
  · simp [globalPairFlip, hm]

/-- Consequently the active edge set itself is unchanged by the flip. -/
theorem pairEdges_globalPairFlip
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (σ : E → Λ) :
    pairEdges (globalPairFlip G S a b σ) a b = pairEdges σ a b := by
  classical
  ext e
  rw [mem_pairEdges, mem_pairEdges]
  exact globalPairFlip_mem_pair_iff G S hab σ e

/-- Because the active graph is unchanged, the component mark is unchanged. -/
theorem reachesRightSdiffGlobal_flip_iff
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (σ : E → Λ) (e : E) :
    reachesRightSdiffGlobal G S a b (globalPairFlip G S a b σ) e ↔
      reachesRightSdiffGlobal G S a b σ e := by
  classical
  unfold reachesRightSdiffGlobal
  simp only [pairEdges_globalPairFlip G S hab σ]

/-- The global component flip is an involution on all labelings. -/
theorem globalPairFlip_involutive
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (σ : E → Λ) :
    globalPairFlip G S a b (globalPairFlip G S a b σ) = σ := by
  funext e
  have hmark := reachesRightSdiffGlobal_flip_iff G S hab σ e
  by_cases hm : reachesRightSdiffGlobal G S a b σ e
  · have hm' : reachesRightSdiffGlobal G S a b (globalPairFlip G S a b σ) e :=
      hmark.mpr hm
    simp [globalPairFlip, hm, hm']
  · have hm' : ¬ reachesRightSdiffGlobal G S a b (globalPairFlip G S a b σ) e := by
      intro h
      exact hm (hmark.mp h)
    simp [globalPairFlip, hm, hm']

/-- In particular, the global component flip is injective. -/
theorem globalPairFlip_injective
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) :
    Function.Injective (globalPairFlip G S a b) := by
  intro σ τ hστ
  calc
    σ = globalPairFlip G S a b (globalPairFlip G S a b σ) :=
      (globalPairFlip_involutive G S hab σ).symm
    _ = globalPairFlip G S a b (globalPairFlip G S a b τ) := by
      exact congrArg (globalPairFlip G S a b) hστ
    _ = τ := globalPairFlip_involutive G S hab τ

end BachThesisLean
