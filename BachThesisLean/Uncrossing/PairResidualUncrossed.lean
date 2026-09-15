import BachThesisLean.Uncrossing.PairResidualEquiv

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E] [DecidableEq Λ]

/-- The two-label residual instance obtained after uncrossing the selected
supports, expressed on the fixed active edge-copy graph of an original frozen
completion. -/
noncomputable abbrev frozenPairUncrossedLists
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :=
  twoLabelLists (frozenPairResidualGraph G ψ) (S a ∪ S b) (S a ∩ S b)
    (uncrossed_twoLabel_degree (frozenPairResidualGraph G ψ) (S a) (S b)
      (frozenPairResidual_leftDegree G S hab hS ψ base))

/-- A binary completion of the uncrossed residual instance, together with the
frozen labels from an original completion, reconstructs an admissible global
completion of the uncrossed support family. Frozen labels are outside the
selected pair and therefore keep the same support under uncrossing. -/
noncomputable def uncrossedResidualToPairFiber
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b))
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :
    (frozenPairUncrossedLists G S hab hS ψ base).AdmissibleLabeling →
      PairCompletionFiber (exactListsOfSupports (uncross S a b) hinc) a b ψ := by
  classical
  intro ρ
  let H := frozenPairResidualGraph G ψ
  let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
  let hdegU := uncrossed_twoLabel_degree H (S a) (S b) hdeg
  let τ : E → Λ := fun e =>
    if he : ψ e = none then
      pairLabel a b (ρ.val ⟨e, (mem_frozenPairEdges ψ e).2 he⟩)
    else
      base.val.val e
  refine ⟨⟨τ, ?_⟩, ?_⟩
  · apply isAdmissible_of_label_mem_of_injOn
    · intro e
      by_cases heNone : ψ e = none
      · have heP : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
        have hmem := ρ.property.label_mem ⟨e, heP⟩
        rcases finTwo_eq_zero_or_one (ρ.val ⟨e, heP⟩) with h0 | h1
        · have hx : G.left e ∈ S a ∪ S b := by
            apply (zero_mem_twoLabelLists_labels H (S a ∪ S b) (S a ∩ S b)
              hdegU (G.left e)).1
            simpa [h0] using hmem
          change τ e ∈ listsOfSupports (uncross S a b) (G.left e)
          rw [mem_listsOfSupports]
          simpa [τ, heNone, h0, uncross_at_left S hab] using hx
        · have hx : G.left e ∈ S a ∩ S b := by
            apply (one_mem_twoLabelLists_labels H (S a ∪ S b) (S a ∩ S b)
              hdegU (G.left e)).1
            simpa [h1] using hmem
          change τ e ∈ listsOfSupports (uncross S a b) (G.left e)
          rw [mem_listsOfSupports]
          simpa [τ, heNone, h1, uncross_at_right S hab] using hx
      · have heP : e ∉ frozenPairEdges ψ := by
          intro hemem
          exact heNone ((mem_frozenPairEdges ψ e).1 hemem)
        have hePair : e ∉ pairEdges base.val.val a b := by
          have hp := pairEdges_eq_frozenPairEdges_of_fiber
            (exactListsOfSupports S hS) a b ψ base
          simpa [hp] using heP
        have hout : ¬ (base.val.val e = a ∨ base.val.val e = b) :=
          (mem_pairEdges base.val.val a b e).not.mp hePair
        have hbase := base.val.property.label_mem e
        change base.val.val e ∈ listsOfSupports S (G.left e) at hbase
        rw [mem_listsOfSupports] at hbase
        change τ e ∈ listsOfSupports (uncross S a b) (G.left e)
        rw [mem_listsOfSupports]
        have hτ : τ e = base.val.val e := by
          simp [τ, heNone]
        rw [hτ]
        rw [uncross_away S (fun h => hout (Or.inl h)) (fun h => hout (Or.inr h))]
        exact hbase
    · intro x e he f hf hτ
      by_cases heNone : ψ e = none <;> by_cases hfNone : ψ f = none
      · have heP : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
        have hfP : f ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ f).2 hfNone
        have heH : (⟨e, heP⟩ : {e : E // e ∈ frozenPairEdges ψ}) ∈ H.leftIncident x :=
          (H.mem_leftIncident x _).2 ((G.mem_leftIncident x e).1 he)
        have hfH : (⟨f, hfP⟩ : {e : E // e ∈ frozenPairEdges ψ}) ∈ H.leftIncident x :=
          (H.mem_leftIncident x _).2 ((G.mem_leftIncident x f).1 hf)
        have hcode : ρ.val ⟨e, heP⟩ = ρ.val ⟨f, hfP⟩ := by
          apply pairLabel_injective hab
          simpa [τ, heNone, hfNone] using hτ
        exact congrArg Subtype.val (ρ.property.left_injOn x heH hfH hcode)
      · have heP : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
        have hfP : f ∉ frozenPairEdges ψ := by
          intro hfmem
          exact hfNone ((mem_frozenPairEdges ψ f).1 hfmem)
        have hfPair : f ∉ pairEdges base.val.val a b := by
          have hp := pairEdges_eq_frozenPairEdges_of_fiber
            (exactListsOfSupports S hS) a b ψ base
          simpa [hp] using hfP
        have hfoutside : ¬ (base.val.val f = a ∨ base.val.val f = b) :=
          (mem_pairEdges base.val.val a b f).not.mp hfPair
        have hactive : pairLabel a b (ρ.val ⟨e, heP⟩) = a ∨
            pairLabel a b (ρ.val ⟨e, heP⟩) = b := by
          rcases finTwo_eq_zero_or_one (ρ.val ⟨e, heP⟩) with h0 | h1
          · exact Or.inl (by simp [h0])
          · exact Or.inr (by simp [h1])
        have heq : pairLabel a b (ρ.val ⟨e, heP⟩) = base.val.val f := by
          simpa [τ, heNone, hfNone] using hτ
        rcases hactive with ha | hb
        · exact (hfoutside (Or.inl (heq.symm.trans ha))).elim
        · exact (hfoutside (Or.inr (heq.symm.trans hb))).elim
      · have heP : e ∉ frozenPairEdges ψ := by
          intro hemel
          exact heNone ((mem_frozenPairEdges ψ e).1 hemel)
        have hfP : f ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ f).2 hfNone
        have hePair : e ∉ pairEdges base.val.val a b := by
          have hp := pairEdges_eq_frozenPairEdges_of_fiber
            (exactListsOfSupports S hS) a b ψ base
          simpa [hp] using heP
        have heoutside : ¬ (base.val.val e = a ∨ base.val.val e = b) :=
          (mem_pairEdges base.val.val a b e).not.mp hePair
        have hactive : pairLabel a b (ρ.val ⟨f, hfP⟩) = a ∨
            pairLabel a b (ρ.val ⟨f, hfP⟩) = b := by
          rcases finTwo_eq_zero_or_one (ρ.val ⟨f, hfP⟩) with h0 | h1
          · exact Or.inl (by simp [h0])
          · exact Or.inr (by simp [h1])
        have heq : base.val.val e = pairLabel a b (ρ.val ⟨f, hfP⟩) := by
          simpa [τ, heNone, hfNone] using hτ
        rcases hactive with ha | hb
        · exact (heoutside (Or.inl (heq.trans ha))).elim
        · exact (heoutside (Or.inr (heq.trans hb))).elim
      · apply base.val.property.left_injOn x he hf
        simpa [τ, heNone, hfNone] using hτ
    · intro y e he f hf hτ
      by_cases heNone : ψ e = none <;> by_cases hfNone : ψ f = none
      · have heP : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
        have hfP : f ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ f).2 hfNone
        have heH : (⟨e, heP⟩ : {e : E // e ∈ frozenPairEdges ψ}) ∈ H.rightIncident y :=
          (H.mem_rightIncident y _).2 ((G.mem_rightIncident y e).1 he)
        have hfH : (⟨f, hfP⟩ : {e : E // e ∈ frozenPairEdges ψ}) ∈ H.rightIncident y :=
          (H.mem_rightIncident y _).2 ((G.mem_rightIncident y f).1 hf)
        have hcode : ρ.val ⟨e, heP⟩ = ρ.val ⟨f, hfP⟩ := by
          apply pairLabel_injective hab
          simpa [τ, heNone, hfNone] using hτ
        exact congrArg Subtype.val (ρ.property.right_injOn y heH hfH hcode)
      · have heP : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
        have hfP : f ∉ frozenPairEdges ψ := by
          intro hfmem
          exact hfNone ((mem_frozenPairEdges ψ f).1 hfmem)
        have hfPair : f ∉ pairEdges base.val.val a b := by
          have hp := pairEdges_eq_frozenPairEdges_of_fiber
            (exactListsOfSupports S hS) a b ψ base
          simpa [hp] using hfP
        have hfoutside : ¬ (base.val.val f = a ∨ base.val.val f = b) :=
          (mem_pairEdges base.val.val a b f).not.mp hfPair
        have hactive : pairLabel a b (ρ.val ⟨e, heP⟩) = a ∨
            pairLabel a b (ρ.val ⟨e, heP⟩) = b := by
          rcases finTwo_eq_zero_or_one (ρ.val ⟨e, heP⟩) with h0 | h1
          · exact Or.inl (by simp [h0])
          · exact Or.inr (by simp [h1])
        have heq : pairLabel a b (ρ.val ⟨e, heP⟩) = base.val.val f := by
          simpa [τ, heNone, hfNone] using hτ
        rcases hactive with ha | hb
        · exact (hfoutside (Or.inl (heq.symm.trans ha))).elim
        · exact (hfoutside (Or.inr (heq.symm.trans hb))).elim
      · have heP : e ∉ frozenPairEdges ψ := by
          intro hemel
          exact heNone ((mem_frozenPairEdges ψ e).1 hemel)
        have hfP : f ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ f).2 hfNone
        have hePair : e ∉ pairEdges base.val.val a b := by
          have hp := pairEdges_eq_frozenPairEdges_of_fiber
            (exactListsOfSupports S hS) a b ψ base
          simpa [hp] using heP
        have heoutside : ¬ (base.val.val e = a ∨ base.val.val e = b) :=
          (mem_pairEdges base.val.val a b e).not.mp hePair
        have hactive : pairLabel a b (ρ.val ⟨f, hfP⟩) = a ∨
            pairLabel a b (ρ.val ⟨f, hfP⟩) = b := by
          rcases finTwo_eq_zero_or_one (ρ.val ⟨f, hfP⟩) with h0 | h1
          · exact Or.inl (by simp [h0])
          · exact Or.inr (by simp [h1])
        have heq : base.val.val e = pairLabel a b (ρ.val ⟨f, hfP⟩) := by
          simpa [τ, heNone, hfNone] using hτ
        rcases hactive with ha | hb
        · exact (heoutside (Or.inl (heq.trans ha))).elim
        · exact (heoutside (Or.inr (heq.trans hb))).elim
      · apply base.val.property.right_injOn y he hf
        simpa [τ, heNone, hfNone] using hτ
  · funext e
    by_cases heNone : ψ e = none
    · have heP : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
      have hnew : τ e = a ∨ τ e = b := by
        rcases finTwo_eq_zero_or_one (ρ.val ⟨e, heP⟩) with h0 | h1
        · exact Or.inl (by simp [τ, heNone, h0])
        · exact Or.inr (by simp [τ, heNone, h1])
      have hnoneNew : freezePair a b τ e = none := by
        simp [freezePair, hnew]
      rw [hnoneNew, heNone]
    · have heP : e ∉ frozenPairEdges ψ := by
        intro hemem
        exact heNone ((mem_frozenPairEdges ψ e).1 hemem)
      have hbaseP : e ∉ pairEdges base.val.val a b := by
        have hp := pairEdges_eq_frozenPairEdges_of_fiber
          (exactListsOfSupports S hS) a b ψ base
        simpa [hp] using heP
      have hbase := (mem_pairEdges base.val.val a b e).not.mp hbaseP
      simpa [freezePair, τ, heNone, hbase] using congrFun base.property e

/-- The uncrossed frozen fibre and the uncrossed binary residual problem have
the same cardinality whenever the original frozen fibre is nonempty. The
empty uncrossed-fibre branch is forced empty on the residual side by the
reconstruction above. -/
theorem pairCompletionCount_uncross_eq_twoLabelUncrossedCount
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (hinc : ExactSupportIncidence G (uncross S a b))
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :
    pairCompletionCount (exactListsOfSupports (uncross S a b) hinc) a b ψ =
      twoLabelUncrossedCount (frozenPairResidualGraph G ψ) (S a) (S b)
        (frozenPairResidual_leftDegree G S hab hS ψ base) := by
  classical
  let U := exactListsOfSupports (uncross S a b) hinc
  let K := frozenPairUncrossedLists G S hab hS ψ base
  by_cases hU : Nonempty (PairCompletionFiber U a b ψ)
  · let ubase := Classical.choice hU
    have hgeneric := pairCompletionCount_eq_twoLabelCount
      G (uncross S a b) hab hinc ψ ubase
    simpa [U, K, frozenPairUncrossedLists, twoLabelUncrossedCount,
      uncross_at_left S hab, uncross_at_right S hab] using hgeneric
  · have hcountU : pairCompletionCount U a b ψ = 0 := by
      unfold pairCompletionCount
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun u => hU ⟨u⟩⟩
    have hcountK : K.count = 0 := by
      apply (count_eq_zero_iff K).2
      intro ρ hρ
      exact hU ⟨uncrossedResidualToPairFiber G S hab hS hinc ψ base ⟨ρ, hρ⟩⟩
    rw [hcountU]
    change 0 = K.count
    exact hcountK.symm

end BachThesisLean
