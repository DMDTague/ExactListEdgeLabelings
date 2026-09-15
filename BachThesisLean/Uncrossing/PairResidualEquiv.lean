import BachThesisLean.Uncrossing.PairResidual

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists
open scoped Classical

universe u v w z

variable {X : Type u} {Y : Type v} {E : Type w} {Λ : Type z}
variable [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E] [DecidableEq Λ]

/-- The active edge copies encoded by a frozen pair assignment. -/
noncomputable def frozenPairEdges (ψ : E → Option Λ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ψ e = none)

@[simp] theorem mem_frozenPairEdges (ψ : E → Option Λ) (e : E) :
    e ∈ frozenPairEdges ψ ↔ ψ e = none := by
  classical
  simp [frozenPairEdges]

/-- The fixed residual graph associated to a frozen pair assignment. -/
noncomputable abbrev frozenPairResidualGraph
    (G : BipartiteMultigraph X Y E) (ψ : E → Option Λ) :=
  G.restrictEdges (frozenPairEdges ψ)

/-- Freezing a labeling determines its active edge-copy set exactly. -/
theorem pairEdges_eq_frozenPairEdges_of_freezePair_eq
    (a b : Λ) {σ : E → Λ} {ψ : E → Option Λ}
    (h : freezePair a b σ = ψ) :
    pairEdges σ a b = frozenPairEdges ψ := by
  classical
  ext e
  have he := congrFun h e
  by_cases hp : σ e = a ∨ σ e = b
  · have hnone : ψ e = none := by
      simpa [freezePair, hp] using he.symm
    simp [mem_pairEdges, hp, hnone]
  · have hsome : ψ e = some (σ e) := by
      simpa [freezePair, hp] using he.symm
    have hnotnone : ψ e ≠ none := by simp [hsome]
    simp [mem_pairEdges, hp, hnotnone]

/-- Every completion in one frozen fibre has the same active edge-copy set. -/
theorem pairEdges_eq_frozenPairEdges_of_fiber
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ)
    (a b : Λ) (ψ : E → Option Λ)
    (σ : PairCompletionFiber L a b ψ) :
    pairEdges σ.val.val a b = frozenPairEdges ψ :=
  pairEdges_eq_frozenPairEdges_of_freezePair_eq a b σ.property

/-- A nonempty original frozen fibre supplies the exact left-degree equation
for the fixed residual graph. -/
theorem frozenPairResidual_leftDegree
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ)
    (σ : PairCompletionFiber (exactListsOfSupports S hS) a b ψ)
    (x : X) :
    (frozenPairResidualGraph G ψ).leftDegree x =
      (if x ∈ S a then 1 else 0) + (if x ∈ S b then 1 else 0) := by
  classical
  have hp := pairEdges_eq_frozenPairEdges_of_fiber
    (exactListsOfSupports S hS) a b ψ σ
  let edgeEquiv : {e : E // e ∈ frozenPairEdges ψ} ≃
      {e : E // e ∈ pairEdges σ.val.val a b} := {
    toFun := fun e => ⟨e.val, by simpa [hp] using e.property⟩
    invFun := fun e => ⟨e.val, by simpa [hp] using e.property⟩
    left_inv := fun e => Subtype.ext rfl
    right_inv := fun e => Subtype.ext rfl
  }
  have hcard :
      ((frozenPairResidualGraph G ψ).leftIncident x).card =
        ((pairResidualGraph G σ.val.val a b).leftIncident x).card := by
    apply Finset.card_equiv edgeEquiv
    intro e
    simp [edgeEquiv, frozenPairResidualGraph, pairResidualGraph,
      BipartiteMultigraph.restrictEdges]
  change ((frozenPairResidualGraph G ψ).leftIncident x).card = _
  rw [hcard]
  exact pairResidual_leftDegree G S hab hS σ.val.property x

/-- Encode a completion in a frozen global fibre as a binary labeling of the
fixed residual edge-copy graph. -/
noncomputable def pairFiberToResidual
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :
    PairCompletionFiber (exactListsOfSupports S hS) a b ψ →
      (twoLabelLists (frozenPairResidualGraph G ψ) (S a) (S b)
        (frozenPairResidual_leftDegree G S hab hS ψ base)).AdmissibleLabeling := by
  classical
  intro τ
  let H := frozenPairResidualGraph G ψ
  let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
  let ρ : {e : E // e ∈ frozenPairEdges ψ} → Fin 2 :=
    fun e => pairCode τ.val.val a e.val
  refine ⟨ρ, ?_⟩
  apply isAdmissible_of_label_mem_of_injOn
  · intro e
    have hP : e.val ∈ pairEdges τ.val.val a b := by
      have hp := pairEdges_eq_frozenPairEdges_of_fiber
        (exactListsOfSupports S hS) a b ψ τ
      simpa [hp] using e.property
    rcases (mem_pairEdges τ.val.val a b e.val).1 hP with hea | heb
    · have hmem := τ.val.property.label_mem e.val
      change τ.val.val e.val ∈ listsOfSupports S (G.left e.val) at hmem
      rw [mem_listsOfSupports] at hmem
      have hx : G.left e.val ∈ S a := by simpa [hea] using hmem
      have hcode : ρ e = 0 := by simp [ρ, pairCode, hea]
      rw [hcode]
      exact (zero_mem_twoLabelLists_labels H (S a) (S b) hdeg (H.left e)).2 hx
    · have hnea : τ.val.val e.val ≠ a := by
        intro hea
        exact hab (hea.symm.trans heb)
      have hmem := τ.val.property.label_mem e.val
      change τ.val.val e.val ∈ listsOfSupports S (G.left e.val) at hmem
      rw [mem_listsOfSupports] at hmem
      have hx : G.left e.val ∈ S b := by simpa [heb] using hmem
      have hcode : ρ e = 1 := by simp [ρ, pairCode, hnea]
      rw [hcode]
      exact (one_mem_twoLabelLists_labels H (S a) (S b) hdeg (H.left e)).2 hx
  · intro x e he f hf hcode
    apply Subtype.ext
    apply τ.val.property.left_injOn x
      ((G.mem_leftIncident x e.val).2 ((H.mem_leftIncident x e).1 he))
      ((G.mem_leftIncident x f.val).2 ((H.mem_leftIncident x f).1 hf))
    have heP : e.val ∈ pairEdges τ.val.val a b := by
      have hp := pairEdges_eq_frozenPairEdges_of_fiber
        (exactListsOfSupports S hS) a b ψ τ
      simpa [hp] using e.property
    have hfP : f.val ∈ pairEdges τ.val.val a b := by
      have hp := pairEdges_eq_frozenPairEdges_of_fiber
        (exactListsOfSupports S hS) a b ψ τ
      simpa [hp] using f.property
    exact pairCode_eq_imp_label_eq τ.val.val hab heP hfP hcode
  · intro y e he f hf hcode
    apply Subtype.ext
    apply τ.val.property.right_injOn y
      ((G.mem_rightIncident y e.val).2 ((H.mem_rightIncident y e).1 he))
      ((G.mem_rightIncident y f.val).2 ((H.mem_rightIncident y f).1 hf))
    have heP : e.val ∈ pairEdges τ.val.val a b := by
      have hp := pairEdges_eq_frozenPairEdges_of_fiber
        (exactListsOfSupports S hS) a b ψ τ
      simpa [hp] using e.property
    have hfP : f.val ∈ pairEdges τ.val.val a b := by
      have hp := pairEdges_eq_frozenPairEdges_of_fiber
        (exactListsOfSupports S hS) a b ψ τ
      simpa [hp] using f.property
    exact pairCode_eq_imp_label_eq τ.val.val hab heP hfP hcode

/-- Decode a binary residual labeling by retaining the frozen labels from a
base completion and decoding `0,1` as the selected labels `a,b`. -/
noncomputable def residualToPairFiber
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :
    (twoLabelLists (frozenPairResidualGraph G ψ) (S a) (S b)
      (frozenPairResidual_leftDegree G S hab hS ψ base)).AdmissibleLabeling →
      PairCompletionFiber (exactListsOfSupports S hS) a b ψ := by
  classical
  intro ρ
  let H := frozenPairResidualGraph G ψ
  let hdeg := frozenPairResidual_leftDegree G S hab hS ψ base
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
        · have hx : G.left e ∈ S a := by
            apply (zero_mem_twoLabelLists_labels H (S a) (S b) hdeg (G.left e)).1
            simpa [h0] using hmem
          change τ e ∈ listsOfSupports S (G.left e)
          rw [mem_listsOfSupports]
          simpa [τ, heNone, h0] using hx
        · have hx : G.left e ∈ S b := by
            apply (one_mem_twoLabelLists_labels H (S a) (S b) hdeg (G.left e)).1
            simpa [h1] using hmem
          change τ e ∈ listsOfSupports S (G.left e)
          rw [mem_listsOfSupports]
          simpa [τ, heNone, h1] using hx
      · simpa [τ, heNone] using base.val.property.label_mem e
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

/-- The frozen global completion fibre is exactly the binary residual
completion space on its active actual edge copies. -/
noncomputable def pairCompletionFiberEquivResidual
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :
    PairCompletionFiber (exactListsOfSupports S hS) a b ψ ≃
      (twoLabelLists (frozenPairResidualGraph G ψ) (S a) (S b)
        (frozenPairResidual_leftDegree G S hab hS ψ base)).AdmissibleLabeling where
  toFun := pairFiberToResidual G S hab hS ψ base
  invFun := residualToPairFiber G S hab hS ψ base
  left_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    by_cases heNone : ψ e = none
    · have he : e ∈ frozenPairEdges ψ := (mem_frozenPairEdges ψ e).2 heNone
      have hτP : e ∈ pairEdges τ.val.val a b := by
        have hp := pairEdges_eq_frozenPairEdges_of_fiber
          (exactListsOfSupports S hS) a b ψ τ
        simpa [hp] using he
      simp [residualToPairFiber, pairFiberToResidual, heNone, he,
        pairLabel_pairCode τ.val.val e hτP]
    · have he : e ∉ frozenPairEdges ψ := by
        intro hemem
        exact heNone ((mem_frozenPairEdges ψ e).1 hemem)
      have heq : τ.val.val e = base.val.val e :=
        label_eq_of_freezePair_eq a b (τ.property.trans base.property.symm) (by
          have hp := pairEdges_eq_frozenPairEdges_of_fiber
            (exactListsOfSupports S hS) a b ψ base
          simpa [hp] using he)
      simp [residualToPairFiber, pairFiberToResidual, heNone, he, heq]
  right_inv ρ := by
    apply Subtype.ext
    funext e
    have he : e.val ∈ frozenPairEdges ψ := e.property
    have heNone : ψ e.val = none := (mem_frozenPairEdges ψ e.val).1 he
    change pairCode
      ((residualToPairFiber G S hab hS ψ base ρ).val.val) a e.val = ρ.val e
    have hval :
        (residualToPairFiber G S hab hS ψ base ρ).val.val e.val =
          pairLabel a b (ρ.val e) := by
      simp [residualToPairFiber, heNone, he]
    unfold pairCode
    rw [hval]
    exact pairCode_pairLabel hab (ρ.val e)

/-- Cardinal version of the frozen-fibre / residual equivalence. -/
theorem pairCompletionCount_eq_twoLabelCount
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    {a b : Λ} (hab : a ≠ b) (hS : ExactSupportIncidence G S)
    (ψ : E → Option Λ)
    (base : PairCompletionFiber (exactListsOfSupports S hS) a b ψ) :
    pairCompletionCount (exactListsOfSupports S hS) a b ψ =
      (twoLabelLists (frozenPairResidualGraph G ψ) (S a) (S b)
        (frozenPairResidual_leftDegree G S hab hS ψ base)).count := by
  classical
  unfold pairCompletionCount
  rw [count_eq_card]
  exact Fintype.card_congr (pairCompletionFiberEquivResidual G S hab hS ψ base)

end BachThesisLean
