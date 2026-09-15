import BachThesisLean.Cubic.BraceSimplicity
import BachThesisLean.Cubic.IsomorphismProperties
import Mathlib.Data.Fintype.Pi

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

private instance decidableForallFintypeTwo
    {α β : Type*} [Fintype α] [Fintype β]
    {p : α → β → Prop} [∀ a b, Decidable (p a b)] :
    Decidable (∀ a b, p a b) := by
  letI : DecidablePred (fun a : α => ∀ b : β, p a b) := fun a => by
    letI : DecidablePred (p a) := fun b => inferInstance
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-!
# Tiny cubic prescribed-pair certificates

The only nonsimple terminal brace sizes not covered by the simplicity theorem
have one or two vertices on each shore.  We keep the finite computation away
from `FactorReachable`: a decidable bridge certificate records a perfect
matching avoiding the prescribed pair and either a common left endpoint or an
explicit two-edge path in the complementary factor.  A separate theorem turns
that finite certificate into the manuscript's actual component witness.
-/

/-- A finite, decidable certificate strong enough to imply the two-edge
component witness.  In the second branch, `g` and `h` give an explicit
length-two path between the left endpoints of `e` and `f`. -/
def EdgePairBridgeCertificate (G : BipartiteMultigraph X Y E) (e f : E) : Prop :=
  ∃ P : Finset E,
    G.IsPerfectMatching P ∧ e ∉ P ∧ f ∉ P ∧
      (G.left e = G.left f ∨
        ∃ g h : E,
          g ∉ P ∧ h ∉ P ∧
          G.left g = G.left e ∧ G.left h = G.left f ∧
          G.right g = G.right h)

instance (G : BipartiteMultigraph X Y E) (e f : E) :
    Decidable (G.EdgePairBridgeCertificate e f) := by
  unfold EdgePairBridgeCertificate
  infer_instance

/-- The finite bridge certificate produces the genuine complementary-factor
component witness used by EEP. -/
theorem edgePairWitness_of_bridgeCertificate
    (G : BipartiteMultigraph X Y E) {e f : E}
    (h : G.EdgePairBridgeCertificate e f) : G.EdgePairWitness e f := by
  rcases h with ⟨P, hP, heP, hfP, hleft | hbridge⟩
  · refine ⟨P, .inl (G.left e), hP, ?_, ?_⟩
    · exact ⟨Finset.mem_compl.mpr heP,
        G.factorReachable_refl Pᶜ (.inl (G.left e))⟩
    · refine ⟨Finset.mem_compl.mpr hfP, ?_⟩
      simpa [hleft] using
        G.factorReachable_refl Pᶜ (.inl (G.left e))
  · rcases hbridge with ⟨g, h, hgP, hhP, hge, hhf, hright⟩
    have hgReach :=
      G.factorReachable_endpoints (S := Pᶜ) (e := g)
        (Finset.mem_compl.mpr hgP)
    have hhReach :=
      G.factorReachable_endpoints (S := Pᶜ) (e := h)
        (Finset.mem_compl.mpr hhP)
    have hhReach' :
        G.FactorReachable Pᶜ (.inr (G.right g)) (.inl (G.left h)) := by
      simpa [hright] using hhReach.symm
    have hpath := hgReach.trans hhReach'
    have hefReach :
        G.FactorReachable Pᶜ (.inl (G.left e)) (.inl (G.left f)) := by
      simpa [hge, hhf] using hpath
    refine ⟨P, .inl (G.left e), hP, ?_, ?_⟩
    · exact ⟨Finset.mem_compl.mpr heP,
        G.factorReachable_refl Pᶜ (.inl (G.left e))⟩
    · exact ⟨Finset.mem_compl.mpr hfP, hefReach⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- On one vertex per shore, cubicity leaves three parallel copies.  The
kernel checks the finite matching/bridge certificate; reachability itself is
proved above rather than decided. -/
theorem finOne_cubic_bridgeCertificate :
    ∀ l r : Fin 3 → Fin 1,
      let G : BipartiteMultigraph (Fin 1) (Fin 1) (Fin 3) :=
        { left := l, right := r }
      G.IsCubic → ∀ e f : Fin 3, e ≠ f →
        G.EdgePairBridgeCertificate e f := by
  decide

/-- Every cubic edge-copy graph on one vertex per shore and three edge copies
has EEP. -/
theorem finOne_cubic_hasEEP :
    ∀ l r : Fin 3 → Fin 1,
      let G : BipartiteMultigraph (Fin 1) (Fin 1) (Fin 3) :=
        { left := l, right := r }
      G.IsCubic → G.HasEEP := by
  intro l r
  dsimp
  intro hG e f hef
  exact edgePairWitness_of_bridgeCertificate _
    (finOne_cubic_bridgeCertificate l r hG e f hef)

/-- The other element of `Fin 2`. -/
def finTwoOther (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

@[simp] theorem finTwoOther_ne_self (i : Fin 2) :
    finTwoOther i ≠ i := by
  decide +revert

@[simp] theorem finTwo_ne_finTwoOther (i : Fin 2) :
    i ≠ finTwoOther i := by
  exact (finTwoOther_ne_self i).symm

@[simp] theorem finTwoOther_involutive (i : Fin 2) :
    finTwoOther (finTwoOther i) = i := by
  decide +revert

/-- Every element of `Fin 2` is either the named element or its mate. -/
theorem finTwo_eq_or_eq_other (i j : Fin 2) :
    j = i ∨ j = finTwoOther i := by
  decide +revert

theorem finTwo_eq_other_of_ne {i j : Fin 2} (h : j ≠ i) :
    j = finTwoOther i :=
  (finTwo_eq_or_eq_other i j).resolve_left h

/-- Any three-element finite set contains an element distinct from two given
distinct names. -/
private theorem exists_third_of_card_eq_three
    {α : Type*} [DecidableEq α] (S : Finset α) {a b : α}
    (hcard : S.card = 3) (hab : a ≠ b) :
    ∃ c ∈ S, c ≠ a ∧ c ≠ b := by
  by_contra h
  have hsub : S ⊆ ({a, b} : Finset α) := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    · by_cases hcb : c = b
      · simp [hcb]
      · exact (h ⟨c, hc, hca, hcb⟩).elim
  have hc := Finset.card_le_card hsub
  have hp : ({a, b} : Finset α).card = 2 := by
    simp [hab]
  rw [hcard, hp] at hc
  omega

/-- Two edges joining opposite left and opposite right vertices form a perfect
matching on a `2 × 2` bipartite graph. -/
private theorem finTwo_pair_isPerfectMatching
    (G : BipartiteMultigraph (Fin 2) (Fin 2) E) {p q : E}
    (hleft : G.left q = finTwoOther (G.left p))
    (hright : G.right q = finTwoOther (G.right p)) :
    G.IsPerfectMatching {p, q} := by
  have hpq : p ≠ q := by
    intro hpq
    have h := congrArg G.left hpq
    rw [hleft] at h
    exact finTwo_ne_finTwoOther (G.left p) h
  intro v
  cases v with
  | inl x =>
      rcases finTwo_eq_or_eq_other (G.left p) x with hx | hx
      · subst x
        have hset :
            G.selectedIncident ({p, q} : Finset E) (.inl (G.left p)) = {p} := by
          ext z
          simp only [mem_selectedIncident, Finset.mem_insert, Finset.mem_singleton,
            Incident]
          constructor
          · rintro ⟨hz, hzi⟩
            rcases hz with hz | hz
            · exact hz
            · subst z
              exfalso
              rw [hleft] at hzi
              exact finTwoOther_ne_self (G.left p) hzi
          · intro hz
            subst z
            exact ⟨Or.inl rfl, rfl⟩
        rw [hset]
        simp
      · rw [hx]
        have hset :
            G.selectedIncident ({p, q} : Finset E)
              (.inl (finTwoOther (G.left p))) = {q} := by
          ext z
          simp only [mem_selectedIncident, Finset.mem_insert, Finset.mem_singleton,
            Incident]
          constructor
          · rintro ⟨hz, hzi⟩
            rcases hz with hz | hz
            · subst z
              exact (finTwo_ne_finTwoOther (G.left p) hzi).elim
            · exact hz
          · intro hz
            subst z
            exact ⟨Or.inr rfl, hleft⟩
        rw [hset]
        simp
  | inr y =>
      rcases finTwo_eq_or_eq_other (G.right p) y with hy | hy
      · subst y
        have hset :
            G.selectedIncident ({p, q} : Finset E) (.inr (G.right p)) = {p} := by
          ext z
          simp only [mem_selectedIncident, Finset.mem_insert, Finset.mem_singleton,
            Incident]
          constructor
          · rintro ⟨hz, hzi⟩
            rcases hz with hz | hz
            · exact hz
            · subst z
              exfalso
              rw [hright] at hzi
              exact finTwoOther_ne_self (G.right p) hzi
          · intro hz
            subst z
            exact ⟨Or.inl rfl, rfl⟩
        rw [hset]
        simp
      · rw [hy]
        have hset :
            G.selectedIncident ({p, q} : Finset E)
              (.inr (finTwoOther (G.right p))) = {q} := by
          ext z
          simp only [mem_selectedIncident, Finset.mem_insert, Finset.mem_singleton,
            Incident]
          constructor
          · rintro ⟨hz, hzi⟩
            rcases hz with hz | hz
            · subst z
              exact (finTwo_ne_finTwoOther (G.right p) hzi).elim
            · exact hz
          · intro hz
            subst z
            exact ⟨Or.inr rfl, hright⟩
        rw [hset]
        simp

/-- If one endpoint cell is empty in a cubic `2 × 2` graph, the opposite
left/right pair is an isolated shore.  This proof uses degree-three saturation
rather than enumerating all endpoint maps. -/
theorem finTwo_missing_cell_edgeCut_empty :
    ∀ l r : Fin 6 → Fin 2, ∀ x y : Fin 2,
      let G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) :=
        { left := l, right := r }
      G.IsCubic →
        (¬ ∃ e : Fin 6, G.left e = x ∧ G.right e = y) →
        G.edgeCut ({Sum.inl x, Sum.inr (finTwoOther y)} :
          Finset (Fin 2 ⊕ Fin 2)) = ∅ := by
  intro l r x y
  let G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) :=
    { left := l, right := r }
  change G.IsCubic →
    (¬ ∃ e : Fin 6, G.left e = x ∧ G.right e = y) →
    G.edgeCut ({Sum.inl x, Sum.inr (finTwoOther y)} :
      Finset (Fin 2 ⊕ Fin 2)) = ∅
  intro hG hmissing
  have hleftCard : (G.leftIncident x).card = 3 := by
    simpa using hG (.inl x)
  have hrightCard : (G.rightIncident (finTwoOther y)).card = 3 := by
    simpa using hG (.inr (finTwoOther y))
  have hleftToRight :
      ∀ e : Fin 6, G.left e = x → G.right e = finTwoOther y := by
    intro e hle
    rcases finTwo_eq_or_eq_other y (G.right e) with hre | hre
    · exact (hmissing ⟨e, hle, hre⟩).elim
    · exact hre
  have hsub :
      G.leftIncident x ⊆ G.rightIncident (finTwoOther y) := by
    intro e he
    have hle : G.left e = x := (G.mem_leftIncident x e).1 he
    exact (G.mem_rightIncident (finTwoOther y) e).2 (hleftToRight e hle)
  have hset :
      G.leftIncident x = G.rightIncident (finTwoOther y) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hleftCard, hrightCard]
  have hsides :
      ∀ e : Fin 6, G.left e = x ↔ G.right e = finTwoOther y := by
    intro e
    constructor
    · exact hleftToRight e
    · intro hre
      have heR : e ∈ G.rightIncident (finTwoOther y) :=
        (G.mem_rightIncident (finTwoOther y) e).2 hre
      rw [← hset] at heR
      exact (G.mem_leftIncident x e).1 heR
  ext e
  simp [edgeCut, hsides e]

/-- The isolated shore used above and its complement are both nonempty. -/
theorem finTwo_isolatedShore_nonempty :
    ∀ x y : Fin 2,
      let W := ({Sum.inl x, Sum.inr (finTwoOther y)} :
        Finset (Fin 2 ⊕ Fin 2))
      W.Nonempty ∧ Wᶜ.Nonempty := by
  decide

/-- Connectedness rules out the empty-cell pattern, so every endpoint cell of
a connected cubic `2 × 2` graph contains an actual edge copy. -/
theorem finTwo_connected_cubic_fullSupport
    (G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6))
    (hconn : G.IsConnected) (hG : G.IsCubic) :
    ∀ x y : Fin 2, ∃ e : Fin 6, G.left e = x ∧ G.right e = y := by
  intro x y
  by_contra hxy
  let W := ({Sum.inl x, Sum.inr (finTwoOther y)} :
    Finset (Fin 2 ⊕ Fin 2))
  have hcut : G.edgeCut W = ∅ := by
    simpa [W] using
      finTwo_missing_cell_edgeCut_empty G.left G.right x y hG hxy
  have hshores : W.Nonempty ∧ Wᶜ.Nonempty := by
    simpa [W] using finTwo_isolatedShore_nonempty x y
  obtain ⟨e, he⟩ :=
    hconn.edgeCut_nonempty_of_nonempty_shores hshores.1 hshores.2
  rw [hcut] at he
  simpa using he

/-- Once all four endpoint cells are nonempty, cubicity supplies an explicit
matching/bridge certificate for every prescribed pair.  The proof uses only
third-edge choices in three-element incidence sets and therefore preserves
individual parallel edge copies without a global finite enumeration. -/
theorem finTwo_fullSupport_cubic_bridgeCertificate :
    ∀ l r : Fin 6 → Fin 2,
      let G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) :=
        { left := l, right := r }
      G.IsCubic →
        (∀ x y : Fin 2, ∃ e : Fin 6, G.left e = x ∧ G.right e = y) →
        ∀ e f : Fin 6, e ≠ f → G.EdgePairBridgeCertificate e f := by
  intro l r
  let G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) :=
    { left := l, right := r }
  change G.IsCubic →
    (∀ x y : Fin 2, ∃ e : Fin 6, G.left e = x ∧ G.right e = y) →
    ∀ e f : Fin 6, e ≠ f → G.EdgePairBridgeCertificate e f
  intro hG hsupport e f hef
  have hleftCard (x : Fin 2) : (G.leftIncident x).card = 3 := by
    simpa using hG (.inl x)
  have hrightCard (y : Fin 2) : (G.rightIncident y).card = 3 := by
    simpa using hG (.inr y)
  by_cases hleft : G.left e = G.left f
  · obtain ⟨p, hpI, hpe, hpf⟩ :=
      exists_third_of_card_eq_three (G.leftIncident (G.left e))
        (hleftCard (G.left e)) hef
    have hpL : G.left p = G.left e :=
      (G.mem_leftIncident (G.left e) p).1 hpI
    obtain ⟨q, hqL, hqR⟩ :=
      hsupport (finTwoOther (G.left p)) (finTwoOther (G.right p))
    have hP : G.IsPerfectMatching ({p, q} : Finset (Fin 6)) :=
      finTwo_pair_isPerfectMatching G hqL hqR
    have hqe : q ≠ e := by
      intro hqe
      have hl := congrArg G.left hqe
      rw [hqL, hpL] at hl
      exact finTwoOther_ne_self (G.left e) hl
    have hpLf : G.left p = G.left f := hpL.trans hleft
    have hqf : q ≠ f := by
      intro hqf
      have hl := congrArg G.left hqf
      rw [hqL, hpLf] at hl
      exact finTwoOther_ne_self (G.left f) hl
    have hep : e ≠ p := hpe.symm
    have heq : e ≠ q := hqe.symm
    have hfp : f ≠ p := hpf.symm
    have hfq : f ≠ q := hqf.symm
    have heP : e ∉ ({p, q} : Finset (Fin 6)) := by
      simp [hep, heq]
    have hfP : f ∉ ({p, q} : Finset (Fin 6)) := by
      simp [hfp, hfq]
    exact ⟨{p, q}, hP, heP, hfP, Or.inl hleft⟩
  · by_cases hright : G.right e = G.right f
    · obtain ⟨p, hpI, hpe, hpf⟩ :=
        exists_third_of_card_eq_three (G.rightIncident (G.right e))
          (hrightCard (G.right e)) hef
      have hpR : G.right p = G.right e :=
        (G.mem_rightIncident (G.right e) p).1 hpI
      obtain ⟨q, hqL, hqR⟩ :=
        hsupport (finTwoOther (G.left p)) (finTwoOther (G.right p))
      have hP : G.IsPerfectMatching ({p, q} : Finset (Fin 6)) :=
        finTwo_pair_isPerfectMatching G hqL hqR
      have hqe : q ≠ e := by
        intro hqe
        have hr := congrArg G.right hqe
        rw [hqR, hpR] at hr
        exact finTwoOther_ne_self (G.right e) hr
      have hpRf : G.right p = G.right f := hpR.trans hright
      have hqf : q ≠ f := by
        intro hqf
        have hr := congrArg G.right hqf
        rw [hqR, hpRf] at hr
        exact finTwoOther_ne_self (G.right f) hr
      have hep : e ≠ p := hpe.symm
      have heq : e ≠ q := hqe.symm
      have hfp : f ≠ p := hpf.symm
      have hfq : f ≠ q := hqf.symm
      have heP : e ∉ ({p, q} : Finset (Fin 6)) := by
        simp [hep, heq]
      have hfP : f ∉ ({p, q} : Finset (Fin 6)) := by
        simp [hfp, hfq]
      exact ⟨{p, q}, hP, heP, hfP,
        Or.inr ⟨e, f, heP, hfP, rfl, rfl, hright⟩⟩
    · have hfLeftOther : G.left f = finTwoOther (G.left e) :=
        finTwo_eq_other_of_ne (i := G.left e) (j := G.left f)
          (by intro h; exact hleft h.symm)
      have hfRightOther : G.right f = finTwoOther (G.right e) :=
        finTwo_eq_other_of_ne (i := G.right e) (j := G.right f)
          (by intro h; exact hright h.symm)
      by_cases halt : ∃ a : Fin 6,
          a ≠ e ∧ G.left a = G.left e ∧ G.right a = G.right e
      · rcases halt with ⟨a, hae, haL, haR⟩
        obtain ⟨b, hbL, hbR⟩ := hsupport (G.left e) (G.right f)
        have hea : e ≠ a := hae.symm
        have heb : e ≠ b := by
          intro heb
          have hr := congrArg G.right heb
          exact hright (hr.trans hbR)
        have hab : a ≠ b := by
          intro hab
          have hr := congrArg G.right hab
          exact hright (haR.symm.trans (hr.trans hbR))
        have hfb : f ≠ b := by
          intro hfb
          have hl := congrArg G.left hfb
          exact hleft (hbL.symm.trans hl.symm)
        have hsub :
            ({e, a, b} : Finset (Fin 6)) ⊆ G.leftIncident (G.left e) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with hte | hta | htb
          · subst t
            exact (G.mem_leftIncident (G.left e) e).2 rfl
          · subst t
            exact (G.mem_leftIncident (G.left e) a).2 haL
          · subst t
            exact (G.mem_leftIncident (G.left e) b).2 hbL
        have htripleCard : ({e, a, b} : Finset (Fin 6)).card = 3 := by
          simp [hea, heb, hab]
        have hleftSet :
            ({e, a, b} : Finset (Fin 6)) = G.leftIncident (G.left e) := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [hleftCard (G.left e), htripleCard]
        obtain ⟨d, hdRI, hdneF, hdneB⟩ :=
          exists_third_of_card_eq_three (G.rightIncident (G.right f))
            (hrightCard (G.right f)) hfb
        have hdR : G.right d = G.right f :=
          (G.mem_rightIncident (G.right f) d).1 hdRI
        have hdL : G.left d = G.left f := by
          rcases finTwo_eq_or_eq_other (G.left e) (G.left d) with hdSame | hdOther
          · exfalso
            have hdLI : d ∈ G.leftIncident (G.left e) :=
              (G.mem_leftIncident (G.left e) d).2 hdSame
            rw [← hleftSet] at hdLI
            simp only [Finset.mem_insert, Finset.mem_singleton] at hdLI
            rcases hdLI with hde | hda | hdb
            · exact hright ((congrArg G.right hde).symm.trans hdR)
            · exact hright
                (haR.symm.trans ((congrArg G.right hda).symm.trans hdR))
            · exact hdneB hdb
          · exact hdOther.trans hfLeftOther.symm
        have hdPairL : G.left d = finTwoOther (G.left a) := by
          calc
            G.left d = G.left f := hdL
            _ = finTwoOther (G.left e) := hfLeftOther
            _ = finTwoOther (G.left a) := by rw [haL]
        have hdPairR : G.right d = finTwoOther (G.right a) := by
          calc
            G.right d = G.right f := hdR
            _ = finTwoOther (G.right e) := hfRightOther
            _ = finTwoOther (G.right a) := by rw [haR]
        have hP : G.IsPerfectMatching ({a, d} : Finset (Fin 6)) :=
          finTwo_pair_isPerfectMatching G hdPairL hdPairR
        have hde : d ≠ e := by
          intro hde
          exact hright ((congrArg G.right hde).symm.trans hdR)
        have haf : a ≠ f := by
          intro haf
          exact hleft (haL.symm.trans (congrArg G.left haf))
        have heP : e ∉ ({a, d} : Finset (Fin 6)) := by
          simp [hea, hde.symm]
        have hfP : f ∉ ({a, d} : Finset (Fin 6)) := by
          simp [haf.symm, hdneF.symm]
        have hbP : b ∉ ({a, d} : Finset (Fin 6)) := by
          simp [hab.symm, hdneB.symm]
        exact ⟨{a, d}, hP, heP, hfP,
          Or.inr ⟨b, f, hbP, hfP, hbL, rfl, hbR⟩⟩
      · obtain ⟨p, hpL, hpR⟩ := hsupport (G.left e) (G.right f)
        obtain ⟨q, hqL, hqR⟩ := hsupport (G.left f) (G.right e)
        have hqPairL : G.left q = finTwoOther (G.left p) := by
          calc
            G.left q = G.left f := hqL
            _ = finTwoOther (G.left e) := hfLeftOther
            _ = finTwoOther (G.left p) := by rw [hpL]
        have hqPairR : G.right q = finTwoOther (G.right p) := by
          calc
            G.right q = G.right e := hqR
            _ = finTwoOther (finTwoOther (G.right e)) :=
              (finTwoOther_involutive (G.right e)).symm
            _ = finTwoOther (G.right f) := by rw [hfRightOther]
            _ = finTwoOther (G.right p) := by rw [hpR]
        have hP : G.IsPerfectMatching ({p, q} : Finset (Fin 6)) :=
          finTwo_pair_isPerfectMatching G hqPairL hqPairR
        have hep : e ≠ p := by
          intro hep
          exact hright ((congrArg G.right hep).trans hpR)
        have heq : e ≠ q := by
          intro heq
          exact hleft ((congrArg G.left heq).trans hqL)
        have hfp : f ≠ p := by
          intro hfp
          exact hleft (((congrArg G.left hfp).trans hpL).symm)
        have hfq : f ≠ q := by
          intro hfq
          exact hright (((congrArg G.right hfq).trans hqR).symm)
        have heP : e ∉ ({p, q} : Finset (Fin 6)) := by
          simp [hep, heq]
        have hfP : f ∉ ({p, q} : Finset (Fin 6)) := by
          simp [hfp, hfq]
        obtain ⟨h, hhRI, hhneE, hhneQ⟩ :=
          exists_third_of_card_eq_three (G.rightIncident (G.right e))
            (hrightCard (G.right e)) heq
        have hhR : G.right h = G.right e :=
          (G.mem_rightIncident (G.right e) h).1 hhRI
        have hhL : G.left h = G.left f := by
          rcases finTwo_eq_or_eq_other (G.left e) (G.left h) with hhSame | hhOther
          · exact (halt ⟨h, hhneE, hhSame, hhR⟩).elim
          · exact hhOther.trans hfLeftOther.symm
        have hhp : h ≠ p := by
          intro hhp
          exact hright (hhR.symm.trans ((congrArg G.right hhp).trans hpR))
        have hhP : h ∉ ({p, q} : Finset (Fin 6)) := by
          simp [hhp, hhneQ]
        exact ⟨{p, q}, hP, heP, hfP,
          Or.inr ⟨e, h, heP, hhP, rfl, hhL, hhR.symm⟩⟩

/-- Every connected cubic edge-copy graph on two vertices per shore and six
edge copies has EEP. -/
theorem finTwo_connected_cubic_hasEEP :
    ∀ l r : Fin 6 → Fin 2,
      let G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) :=
        { left := l, right := r }
      G.IsConnected → G.IsCubic → G.HasEEP := by
  intro l r
  dsimp
  intro hconn hG e f hef
  let G : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) :=
    { left := l, right := r }
  have hsupport :
      ∀ x y : Fin 2, ∃ g : Fin 6, G.left g = x ∧ G.right g = y :=
    G.finTwo_connected_cubic_fullSupport hconn hG
  have hcert : G.EdgePairBridgeCertificate e f :=
    finTwo_fullSupport_cubic_bridgeCertificate l r hG hsupport e f hef
  exact edgePairWitness_of_bridgeCertificate G hcert

/-- Cubicity fixes the number of edge copies at three times the left-shore
cardinality. -/
theorem edgeCard_eq_three_mul_leftCard_of_cubic
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic) :
    Fintype.card E = 3 * Fintype.card X := by
  have hreg := (G.isCubic_iff).1 hG
  have h :=
    G.card_biUnion_leftIncident_of_regular hreg.1 (Finset.univ : Finset X)
  simpa using h

/-- Relabel all three finite carrier types of a bipartite multigraph by fixed
finite intervals of the same cardinalities. -/
noncomputable def finRelabel
    (G : BipartiteMultigraph X Y E) {n m : ℕ}
    (hX : Fintype.card X = n) (hY : Fintype.card Y = n)
    (hE : Fintype.card E = m) :
    BipartiteMultigraph (Fin n) (Fin n) (Fin m) := by
  let xeq : X ≃ Fin n := Fintype.equivFinOfCardEq hX
  let yeq : Y ≃ Fin n := Fintype.equivFinOfCardEq hY
  let eeq : E ≃ Fin m := Fintype.equivFinOfCardEq hE
  exact
    { left := fun i => xeq (G.left (eeq.symm i))
      right := fun i => yeq (G.right (eeq.symm i)) }

/-- The canonical finite relabeling is graph-isomorphic to the original
edge-copy presentation. -/
noncomputable def graphIsoFinRelabel
    (G : BipartiteMultigraph X Y E) {n m : ℕ}
    (hX : Fintype.card X = n) (hY : Fintype.card Y = n)
    (hE : Fintype.card E = m) :
    GraphIso G (G.finRelabel hX hY hE) := by
  let xeq : X ≃ Fin n := Fintype.equivFinOfCardEq hX
  let yeq : Y ≃ Fin n := Fintype.equivFinOfCardEq hY
  let eeq : E ≃ Fin m := Fintype.equivFinOfCardEq hE
  refine
    { leftEquiv := xeq
      rightEquiv := yeq
      edgeEquiv := eeq
      map_left := ?_
      map_right := ?_ }
  · intro e
    simp [finRelabel, xeq, yeq, eeq]
  · intro e
    simp [finRelabel, xeq, yeq, eeq]

/-- The one-vertex-per-shore cubic case is exactly the triple-parallel case up
to relabeling, and therefore has EEP. -/
theorem hasEEP_of_cubic_card_left_eq_one
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic)
    (hX : Fintype.card X = 1) : G.HasEEP := by
  classical
  have hY : Fintype.card Y = 1 := by
    calc
      Fintype.card Y = Fintype.card X :=
        (G.card_left_eq_card_right_of_cubic hG).symm
      _ = 1 := hX
  have hE : Fintype.card E = 3 := by
    rw [G.edgeCard_eq_three_mul_leftCard_of_cubic hG, hX]
  let H : BipartiteMultigraph (Fin 1) (Fin 1) (Fin 3) := G.finRelabel hX hY hE
  let φ : GraphIso G H := G.graphIsoFinRelabel hX hY hE
  have hHcubic : H.IsCubic := (φ.isCubic_iff).2 hG
  have hHEEP : H.HasEEP := by
    simpa [H] using finOne_cubic_hasEEP H.left H.right hHcubic
  exact (φ.hasEEP_iff).1 hHEEP

/-- The connected two-vertices-per-shore cubic case has EEP by transport to the
finite six-edge certificate. -/
theorem hasEEP_of_connected_cubic_card_left_eq_two
    (G : BipartiteMultigraph X Y E) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hX : Fintype.card X = 2) : G.HasEEP := by
  classical
  have hY : Fintype.card Y = 2 := by
    calc
      Fintype.card Y = Fintype.card X :=
        (G.card_left_eq_card_right_of_cubic hG).symm
      _ = 2 := hX
  have hE : Fintype.card E = 6 := by
    rw [G.edgeCard_eq_three_mul_leftCard_of_cubic hG, hX]
  let H : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) := G.finRelabel hX hY hE
  let φ : GraphIso G H := G.graphIsoFinRelabel hX hY hE
  have hHconn : H.IsConnected := φ.isConnected_map hconn
  have hHcubic : H.IsCubic := (φ.isCubic_iff).2 hG
  have hHEEP : H.HasEEP := by
    simpa [H] using finTwo_connected_cubic_hasEEP H.left H.right hHconn hHcubic
  exact (φ.hasEEP_iff).1 hHEEP

/-- Every connected cubic graph with fewer than three vertices on its left
shore belongs to one of the two finite base cases and has EEP. -/
theorem hasEEP_of_connected_cubic_card_left_lt_three
    (G : BipartiteMultigraph X Y E) (hconn : G.IsConnected) (hG : G.IsCubic)
    (hsmall : Fintype.card X < 3) : G.HasEEP := by
  have hXpos : 0 < Fintype.card X := by
    obtain ⟨v⟩ := hconn.1
    cases v with
    | inl x => exact Fintype.card_pos_iff.mpr ⟨x⟩
    | inr y =>
        have hYpos : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨y⟩
        rw [G.card_left_eq_card_right_of_cubic hG]
        exact hYpos
  have hcases : Fintype.card X = 1 ∨ Fintype.card X = 2 := by
    omega
  rcases hcases with hX | hX
  · exact G.hasEEP_of_cubic_card_left_eq_one hG hX
  · exact G.hasEEP_of_connected_cubic_card_left_eq_two hconn hG hX

end BipartiteMultigraph
end BachThesisLean
