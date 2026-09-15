import BachThesisLean.Uncrossing.FibreGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

namespace BachThesisLean

open BipartiteMultigraph ExactLeftLists

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq E]

/-!
# Exact counting in a two-label fibre

Once one admissible `Fin 2` labeling exists, every other admissible labeling
is obtained by independently swapping the two labels on precisely those
edge-copy line-graph components on which every incident left list is the full
two-label palette. Components meeting a forced singleton list have no binary
choice. Parallel edge copies remain distinct vertices throughout.
-/

/-- A line-graph component is free when every edge copy in it is incident at
a left vertex whose list is the full two-label palette. -/
def IsFreeTwoLabelComponent
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (c : (fibreLineGraph G).ConnectedComponent) : Prop :=
  ∀ e : E, (fibreLineGraph G).connectedComponentMk e = c →
    L.labels (G.left e) = Finset.univ

/-- The finite type of free edge-copy components. -/
abbrev FreeTwoLabelComponent
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2)) :=
  {c : (fibreLineGraph G).ConnectedComponent // IsFreeTwoLabelComponent L c}

/-- Number of free binary-choice components. -/
noncomputable def freeTwoLabelComponentCount
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2)) : ℕ := by
  classical
  exact Fintype.card (FreeTwoLabelComponent L)

private theorem finTwo_other_unique {a b c : Fin 2}
    (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  apply Fin.ext
  have habv : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have hacv : a.val ≠ c.val := by
    intro h
    exact hac (Fin.ext h)
  omega

/-- For two proper two-colorings, agreement is preserved across one
line-graph edge. -/
theorem twoLabel_admissible_agree_adj_iff
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ τ : E → Fin 2} (hσ : L.IsAdmissible σ) (hτ : L.IsAdmissible τ)
    {e f : E} (hef : (fibreLineGraph G).Adj e f) :
    σ e = τ e ↔ σ f = τ f := by
  have hσne : σ e ≠ σ f :=
    (admissibleFibreColoring L σ hσ).valid hef
  have hτne : τ e ≠ τ f :=
    (admissibleFibreColoring L τ hτ).valid hef
  constructor
  · intro heq
    have hother : σ e ≠ τ f := by
      intro h
      exact hτne (heq.symm.trans h)
    exact finTwo_other_unique hσne hother
  · intro hfeq
    have hother : σ f ≠ τ e := by
      intro h
      exact hτne.symm (hfeq.symm.trans h)
    exact finTwo_other_unique hσne.symm hother

/-- Agreement of two admissible two-labelings is constant on every connected
edge-copy component. -/
theorem twoLabel_admissible_agree_reachable_iff
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ τ : E → Fin 2} (hσ : L.IsAdmissible σ) (hτ : L.IsAdmissible τ)
    {e f : E} (hef : (fibreLineGraph G).Reachable e f) :
    σ e = τ e ↔ σ f = τ f := by
  rw [(fibreLineGraph G).reachable_iff_reflTransGen e f] at hef
  induction hef with
  | refl => rfl
  | tail hreach hadj ih =>
      exact ih.trans (twoLabel_admissible_agree_adj_iff L hσ hτ hadj)

/-- A representative actual edge copy of a connected component. -/
noncomputable def fibreComponentRep
    (G : BipartiteMultigraph X Y E)
    (c : (fibreLineGraph G).ConnectedComponent) : E :=
  Classical.choose (Quot.exists_rep c)

@[simp] theorem fibreComponentRep_component
    (G : BipartiteMultigraph X Y E)
    (c : (fibreLineGraph G).ConnectedComponent) :
    (fibreLineGraph G).connectedComponentMk (fibreComponentRep G c) = c :=
  Classical.choose_spec (Quot.exists_rep c)

/-- Swapping `0` and `1` has no fixed point. -/
theorem finTwo_swap_ne (c : Fin 2) : Equiv.swap (0 : Fin 2) 1 c ≠ c := by
  intro h
  have h0 : c = 0 ∨ c = 1 := by
    by_cases hc : c.val = 0
    · left
      exact Fin.ext hc
    · right
      apply Fin.ext
      omega
  rcases h0 with rfl | rfl <;> simp at h

/-- On a non-free component there is an actual edge copy whose left list is
not the full two-label palette. -/
theorem exists_nonfull_of_not_free
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (c : (fibreLineGraph G).ConnectedComponent)
    (hc : ¬ IsFreeTwoLabelComponent L c) :
    ∃ e : E, (fibreLineGraph G).connectedComponentMk e = c ∧
      L.labels (G.left e) ≠ Finset.univ := by
  classical
  by_contra hn
  apply hc
  intro e hec
  by_contra hlist
  exact hn ⟨e, hec, hlist⟩

/-- Two admissible labelings agree at an edge whose left list is not the full
`Fin 2` palette: the existing edge makes the exact list nonempty, so a proper
subset of the two-element palette is a singleton. -/
theorem twoLabel_admissible_eq_of_nonfull
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ τ : E → Fin 2} (hσ : L.IsAdmissible σ) (hτ : L.IsAdmissible τ)
    (e : E) (hne : L.labels (G.left e) ≠ Finset.univ) :
    σ e = τ e := by
  have hσmem := hσ.label_mem e
  have hτmem := hτ.label_mem e
  by_contra hneq
  have hpair : ({σ e, τ e} : Finset (Fin 2)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hneq]
    rfl
  apply hne
  apply Finset.eq_univ_iff_forall.mpr
  intro c
  have hc : c = σ e ∨ c = τ e := by
    have : c ∈ ({σ e, τ e} : Finset (Fin 2)) := by
      rw [hpair]
      exact Finset.mem_univ c
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hc with rfl | rfl
  · exact hσmem
  · exact hτmem

/-- Therefore all admissible labelings agree with a chosen base labeling on
non-free connected components. -/
theorem twoLabel_admissible_eq_on_nonfree
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ τ : E → Fin 2} (hσ : L.IsAdmissible σ) (hτ : L.IsAdmissible τ)
    (e : E) (hfree : ¬ IsFreeTwoLabelComponent L
      ((fibreLineGraph G).connectedComponentMk e)) :
    τ e = σ e := by
  obtain ⟨f, hfc, hnonfull⟩ :=
    exists_nonfull_of_not_free L ((fibreLineGraph G).connectedComponentMk e) hfree
  have hreach : (fibreLineGraph G).Reachable f e :=
    SimpleGraph.ConnectedComponent.eq.mp hfc
  have hagree := twoLabel_admissible_agree_reachable_iff L hτ hσ hreach
  exact hagree.mp (twoLabel_admissible_eq_of_nonfull L hτ hσ f hnonfull)

/-- The binary choice assigned to a component. Non-free components carry the
canonical zero bit, so the decoder below no longer has dependent branches. -/
noncomputable def freeChoiceAt
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (bits : FreeTwoLabelComponent L → Fin 2)
    (c : (fibreLineGraph G).ConnectedComponent) : Fin 2 := by
  classical
  exact if hc : IsFreeTwoLabelComponent L c then bits ⟨c, hc⟩ else 0

@[simp] theorem freeChoiceAt_of_free
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (bits : FreeTwoLabelComponent L → Fin 2)
    (c : (fibreLineGraph G).ConnectedComponent)
    (hc : IsFreeTwoLabelComponent L c) :
    freeChoiceAt L bits c = bits ⟨c, hc⟩ := by
  classical
  simp [freeChoiceAt, hc]

@[simp] theorem freeChoiceAt_of_not_free
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (bits : FreeTwoLabelComponent L → Fin 2)
    (c : (fibreLineGraph G).ConnectedComponent)
    (hc : ¬ IsFreeTwoLabelComponent L c) :
    freeChoiceAt L bits c = 0 := by
  classical
  simp [freeChoiceAt, hc]

/-- Decode a choice bit on every free component by independently swapping the
base admissible labeling on that component. -/
noncomputable def decodeFreeChoices
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (σ : E → Fin 2) (bits : FreeTwoLabelComponent L → Fin 2) : E → Fin 2 := by
  classical
  exact fun e =>
    if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk e) = 0 then
      σ e
    else
      Equiv.swap (0 : Fin 2) 1 (σ e)

/-- Decoding free-component bits preserves admissibility. -/
theorem decodeFreeChoices_isAdmissible
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ : E → Fin 2} (hσ : L.IsAdmissible σ)
    (bits : FreeTwoLabelComponent L → Fin 2) :
    L.IsAdmissible (decodeFreeChoices L σ bits) := by
  classical
  apply isAdmissible_of_label_mem_of_injOn
  · intro e
    by_cases hc : IsFreeTwoLabelComponent L
        ((fibreLineGraph G).connectedComponentMk e)
    · rw [hc e rfl]
      exact Finset.mem_univ _
    · have hb := freeChoiceAt_of_not_free L bits
        ((fibreLineGraph G).connectedComponentMk e) hc
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk e) = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) ∈ L.labels (G.left e)
      rw [if_pos hb]
      exact hσ.label_mem e
  · intro x e he f hf hval
    have hcomp : (fibreLineGraph G).connectedComponentMk e =
        (fibreLineGraph G).connectedComponentMk f := by
      by_cases hef : e = f
      · simpa [hef]
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ⟨hef, Or.inl ((G.mem_leftIncident x e).1 he |>.trans
            ((G.mem_leftIncident x f).1 hf).symm)⟩
    have hchoice := congrArg (freeChoiceAt L bits) hcomp
    by_cases hb : freeChoiceAt L bits
        ((fibreLineGraph G).connectedComponentMk e) = 0
    · have hbf : freeChoiceAt L bits
          ((fibreLineGraph G).connectedComponentMk f) = 0 :=
        hchoice.symm.trans hb
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk e) = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) =
        (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk f) = 0
        then σ f else Equiv.swap (0 : Fin 2) 1 (σ f)) at hval
      rw [if_pos hb, if_pos hbf] at hval
      exact hσ.left_injOn x he hf hval
    · have hbf : freeChoiceAt L bits
          ((fibreLineGraph G).connectedComponentMk f) ≠ 0 := by
        intro hf0
        exact hb (hchoice.trans hf0)
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk e) = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) =
        (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk f) = 0
        then σ f else Equiv.swap (0 : Fin 2) 1 (σ f)) at hval
      rw [if_neg hb, if_neg hbf] at hval
      apply hσ.left_injOn x he hf
      exact (Equiv.swap (0 : Fin 2) 1).injective hval
  · intro y e he f hf hval
    have hcomp : (fibreLineGraph G).connectedComponentMk e =
        (fibreLineGraph G).connectedComponentMk f := by
      by_cases hef : e = f
      · simpa [hef]
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ⟨hef, Or.inr ((G.mem_rightIncident y e).1 he |>.trans
            ((G.mem_rightIncident y f).1 hf).symm)⟩
    have hchoice := congrArg (freeChoiceAt L bits) hcomp
    by_cases hb : freeChoiceAt L bits
        ((fibreLineGraph G).connectedComponentMk e) = 0
    · have hbf : freeChoiceAt L bits
          ((fibreLineGraph G).connectedComponentMk f) = 0 :=
        hchoice.symm.trans hb
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk e) = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) =
        (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk f) = 0
        then σ f else Equiv.swap (0 : Fin 2) 1 (σ f)) at hval
      rw [if_pos hb, if_pos hbf] at hval
      exact hσ.right_injOn y he hf hval
    · have hbf : freeChoiceAt L bits
          ((fibreLineGraph G).connectedComponentMk f) ≠ 0 := by
        intro hf0
        exact hb (hchoice.trans hf0)
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk e) = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) =
        (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk f) = 0
        then σ f else Equiv.swap (0 : Fin 2) 1 (σ f)) at hval
      rw [if_neg hb, if_neg hbf] at hval
      apply hσ.right_injOn y he hf
      exact (Equiv.swap (0 : Fin 2) 1).injective hval

/-- Encode an admissible labeling by whether it agrees with a chosen base
labeling on a representative of each free component. -/
noncomputable def encodeFreeChoices
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (σ τ : E → Fin 2) : FreeTwoLabelComponent L → Fin 2 := by
  classical
  intro c
  exact if τ (fibreComponentRep G c.1) = σ (fibreComponentRep G c.1) then 0 else 1

/-- Encoding after decoding returns the chosen free-component bits. -/
theorem encode_decode_freeChoices
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ : E → Fin 2} (hσ : L.IsAdmissible σ)
    (bits : FreeTwoLabelComponent L → Fin 2) :
    encodeFreeChoices L σ (decodeFreeChoices L σ bits) = bits := by
  classical
  funext c
  let rep := fibreComponentRep G c.1
  have hrep : (fibreLineGraph G).connectedComponentMk rep = c.1 :=
    fibreComponentRep_component G c.1
  have hfree : IsFreeTwoLabelComponent L
      ((fibreLineGraph G).connectedComponentMk rep) := by
    simpa [hrep] using c.2
  have hsub :
      (⟨(fibreLineGraph G).connectedComponentMk rep, hfree⟩ :
        FreeTwoLabelComponent L) = c :=
    Subtype.ext hrep
  have hchoice := freeChoiceAt_of_free L bits
    ((fibreLineGraph G).connectedComponentMk rep) hfree
  rw [hsub] at hchoice
  by_cases hb : bits c = 0
  · have hc0 : freeChoiceAt L bits
        ((fibreLineGraph G).connectedComponentMk rep) = 0 := hchoice.trans hb
    have hdec : decodeFreeChoices L σ bits rep = σ rep := by
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk rep) = 0
        then σ rep else Equiv.swap (0 : Fin 2) 1 (σ rep)) = σ rep
      rw [if_pos hc0]
    change (if decodeFreeChoices L σ bits rep = σ rep then 0 else 1) = bits c
    rw [if_pos hdec, hb]
  · have hone : bits c = 1 := by
      rcases finTwo_eq_zero_or_one (bits c) with h0 | h1
      · exact (hb h0).elim
      · exact h1
    have hc1 : freeChoiceAt L bits
        ((fibreLineGraph G).connectedComponentMk rep) = 1 := hchoice.trans hone
    have hcne : freeChoiceAt L bits
        ((fibreLineGraph G).connectedComponentMk rep) ≠ 0 := by
      rw [hc1]
      decide
    have hdecne : decodeFreeChoices L σ bits rep ≠ σ rep := by
      change (if freeChoiceAt L bits ((fibreLineGraph G).connectedComponentMk rep) = 0
        then σ rep else Equiv.swap (0 : Fin 2) 1 (σ rep)) ≠ σ rep
      rw [if_neg hcne]
      exact finTwo_swap_ne _
    change (if decodeFreeChoices L σ bits rep = σ rep then 0 else 1) = bits c
    rw [if_neg hdecne, hone]

/-- Decoding the bits of an admissible labeling recovers that labeling. -/
theorem decode_encode_freeChoices
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ τ : E → Fin 2} (hσ : L.IsAdmissible σ) (hτ : L.IsAdmissible τ) :
    decodeFreeChoices L σ (encodeFreeChoices L σ τ) = τ := by
  classical
  funext e
  let c := (fibreLineGraph G).connectedComponentMk e
  by_cases hc : IsFreeTwoLabelComponent L c
  · let rep := fibreComponentRep G c
    have hrep : (fibreLineGraph G).connectedComponentMk rep = c :=
      fibreComponentRep_component G c
    have hreach : (fibreLineGraph G).Reachable rep e :=
      SimpleGraph.ConnectedComponent.eq.mp (by simpa [c] using hrep)
    have hagree := twoLabel_admissible_agree_reachable_iff L hτ hσ hreach
    by_cases heq : τ rep = σ rep
    · have heq' : τ e = σ e := hagree.mp heq
      have hbit : freeChoiceAt L (encodeFreeChoices L σ τ) c = 0 := by
        rw [freeChoiceAt_of_free L (encodeFreeChoices L σ τ) c hc]
        simp [encodeFreeChoices, rep, heq]
      change (if freeChoiceAt L (encodeFreeChoices L σ τ) c = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) = τ e
      rw [if_pos hbit]
      exact heq'.symm
    · have hneq' : τ e ≠ σ e := by
        intro h
        exact heq (hagree.mpr h)
      have hswap : Equiv.swap (0 : Fin 2) 1 (σ e) = τ e := by
        have hother : τ e = Equiv.swap (0 : Fin 2) 1 (σ e) := by
          apply finTwo_other_unique (a := σ e)
          · exact hneq'.symm
          · exact (finTwo_swap_ne (σ e)).symm
        exact hother.symm
      have hbit : freeChoiceAt L (encodeFreeChoices L σ τ) c ≠ 0 := by
        rw [freeChoiceAt_of_free L (encodeFreeChoices L σ τ) c hc]
        simp [encodeFreeChoices, rep, heq]
      change (if freeChoiceAt L (encodeFreeChoices L σ τ) c = 0
        then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) = τ e
      rw [if_neg hbit]
      exact hswap
  · have heq : τ e = σ e := twoLabel_admissible_eq_on_nonfree L hσ hτ e hc
    have hbit : freeChoiceAt L (encodeFreeChoices L σ τ) c = 0 :=
      freeChoiceAt_of_not_free L (encodeFreeChoices L σ τ) c hc
    change (if freeChoiceAt L (encodeFreeChoices L σ τ) c = 0
      then σ e else Equiv.swap (0 : Fin 2) 1 (σ e)) = τ e
    rw [if_pos hbit]
    exact heq.symm

/-- Admissible two-labelings are equivalent to independent binary choices on
the free edge-copy components once a base admissible labeling is fixed. -/
noncomputable def admissibleLabelingEquivFreeChoices
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    (σ : L.AdmissibleLabeling) :
    L.AdmissibleLabeling ≃ (FreeTwoLabelComponent L → Fin 2) where
  toFun τ := encodeFreeChoices L σ.1 τ.1
  invFun bits := ⟨decodeFreeChoices L σ.1 bits,
    decodeFreeChoices_isAdmissible L σ.2 bits⟩
  left_inv τ := by
    apply Subtype.ext
    exact decode_encode_freeChoices L σ.2 τ.2
  right_inv bits := encode_decode_freeChoices L σ.2 bits

/-- If a two-label exact-list instance is admissible, its exact number of
completions is one binary choice per free component. -/
theorem twoLabel_count_eq_pow_of_admissible
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G (Fin 2))
    {σ : E → Fin 2} (hσ : L.IsAdmissible σ) :
    L.count = 2 ^ freeTwoLabelComponentCount L := by
  classical
  rw [count_eq_card]
  let s : L.AdmissibleLabeling := ⟨σ, hσ⟩
  rw [Fintype.card_congr (admissibleLabelingEquivFreeChoices L s)]
  simp [freeTwoLabelComponentCount]

end BachThesisLean
