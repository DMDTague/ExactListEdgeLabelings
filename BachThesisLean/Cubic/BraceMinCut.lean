import BachThesisLean.Cubic.BraceSimplicity
import BachThesisLean.Cubic.TightCutCubic

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Three-edge cut lower bound for simple cubic braces

A cubic bipartite cut with fewer than three copies cannot have size one:
the oriented cubic balance forces a multiple-of-three difference between the
two cut orientations.  Hence a hypothetical small nonempty cut has exactly one
copy in each orientation.  Moving the outside right endpoint of the
left-to-right copy into the shore kills that orientation and turns the cut
into a tight three-cut.  Simplicity supplies enough vertices on the remaining
side to make this new tight cut nontrivial, contradicting the brace axiom.
-/

/-- Every proper nonempty vertex cut in a simple cubic brace has at least three
edge copies.  This is intentionally stated with simplicity: the tiny cubic
multigraph amplifier has a two-edge cut. -/
theorem IsBrace.edgeCut_card_ge_three_of_simple_cubic
    {G : BipartiteMultigraph X Y E}
    (hbrace : G.IsBrace) (hG : G.IsCubic) (hsimple : G.IsSimple)
    (W : Finset (X ⊕ Y)) (hW : W.Nonempty) (hWc : Wᶜ.Nonempty) :
    3 ≤ (G.edgeCut W).card := by
  classical
  by_contra hsmall
  have hlt : (G.edgeCut W).card < 3 := by omega
  have hcutNonempty : (G.edgeCut W).Nonempty :=
    hbrace.1.1.edgeCut_nonempty_of_nonempty_shores hW hWc
  have hpos : 0 < (G.edgeCut W).card := Finset.card_pos.mpr hcutNonempty
  have hcutCard :
      (G.edgeCut W).card =
        (G.cutFromLeft W).card + (G.cutFromRight W).card := by
    rw [G.edgeCut_eq_oriented_union W,
      Finset.card_union_of_disjoint (G.cutFromLeft_disjoint_cutFromRight W)]
  have hcubicBal := hG.cut_orientation_balance W
  have hleftCard : (G.cutFromLeft W).card = 1 := by omega
  have hrightCard : (G.cutFromRight W).card = 1 := by omega
  have hshoreCard :
      (cutLeftVertices W).card = (cutRightVertices W).card := by
    omega

  obtain ⟨e, heqLeft⟩ := Finset.card_eq_one.mp hleftCard
  obtain ⟨f, heqRight⟩ := Finset.card_eq_one.mp hrightCard
  have heLeft : e ∈ G.cutFromLeft W := by
    rw [heqLeft]
    simp
  have hfRight : f ∈ G.cutFromRight W := by
    rw [heqRight]
    simp
  have heData := (G.mem_cutFromLeft W e).1 heLeft
  have hfData := (G.mem_cutFromRight W f).1 hfRight

  let y0 : Y := G.right e
  let x0 : X := G.left f
  let W' : Finset (X ⊕ Y) := insert (.inr y0) W
  have hy0out : (Sum.inr y0 : X ⊕ Y) ∉ W := by
    simpa [y0] using heData.2
  have hx0out : (Sum.inl x0 : X ⊕ Y) ∉ W := by
    simpa [x0] using hfData.1

  /- Adding `y0` removes the unique left-to-right boundary copy and cannot
     create another such copy. -/
  have hleftEmpty : G.cutFromLeft W' = ∅ := by
    ext g
    constructor
    · intro hg
      have hgData := (G.mem_cutFromLeft W' g).1 hg
      have hgin : (Sum.inl (G.left g) : X ⊕ Y) ∈ W := by
        simpa [W'] using hgData.1
      have hgout : (Sum.inr (G.right g) : X ⊕ Y) ∉ W := by
        intro hmem
        exact hgData.2 (by simp [W', hmem])
      have hgOld : g ∈ G.cutFromLeft W :=
        (G.mem_cutFromLeft W g).2 ⟨hgin, hgout⟩
      have hge : g = e := by
        rw [heqLeft] at hgOld
        simpa using hgOld
      subst g
      exact False.elim (hgData.2 (by simp [W', y0]))
    · intro hg
      simp at hg

  have hleftVertices : cutLeftVertices W' = cutLeftVertices W := by
    ext x
    simp [W']
  have hrightVertices :
      cutRightVertices W' = insert y0 (cutRightVertices W) := by
    ext y
    simp [W']
  have hy0notRight : y0 ∉ cutRightVertices W := by
    simpa using hy0out

  /- The new shore is nontrivial on its own side: it contains an old left
     vertex of `W` and the newly inserted right vertex. -/
  have hW'large : 1 < W'.card := by
    apply Finset.one_lt_card_iff_nontrivial.mpr
    refine ⟨.inl (G.left e), ?_, .inr y0, ?_, by simp⟩
    · exact Finset.mem_insert_of_mem (by simpa using heData.1)
    · simp [W']

  /- On the complement side, use cubicity at the outside left endpoint `x0`.
     Besides the unique cut copy `f`, there is an incident copy whose right
     endpoint is neither in `W` nor `y0`.  If a first alternative points to
     `y0`, the third incident copy works; simplicity prevents both alternatives
     from being parallel to that same endpoint. -/
  have hgood : ∃ g : E,
      G.left g = x0 ∧ g ≠ f ∧ G.right g ≠ y0 := by
    obtain ⟨g, hgInc, hgf⟩ := hG.exists_incident_ne (.inl x0) f
    have hgLeft : G.left g = x0 := by
      simpa [Incident] using hgInc
    by_cases hgy : G.right g = y0
    · let I : Finset E := G.incidentEdges (.inl x0)
      have hfI : f ∈ I := by
        dsimp [I]
        apply (G.mem_incidentEdges (.inl x0) f).2
        simp [Incident, x0]
      have hgI : g ∈ I := by
        dsimp [I]
        exact (G.mem_incidentEdges (.inl x0) g).2 hgInc
      have hIcard : I.card = 3 := by
        simpa [I] using hG (.inl x0)
      have hEraseCard : (I.erase f).card = 2 := by
        rw [Finset.card_erase_of_mem hfI, hIcard]
      have hgt : 1 < (I.erase f).card := by omega
      obtain ⟨g', hg'Erase, hg'ne⟩ := Finset.exists_mem_ne hgt g
      have hg'Data := Finset.mem_erase.mp hg'Erase
      have hg'f : g' ≠ f := hg'Data.1
      have hg'I : g' ∈ I := hg'Data.2
      have hg'Inc : G.Incident g' (.inl x0) := by
        exact (G.mem_incidentEdges (.inl x0) g').1 (by simpa [I] using hg'I)
      have hg'Left : G.left g' = x0 := by
        simpa [Incident] using hg'Inc
      have hg'Right : G.right g' ≠ y0 := by
        intro hg'y
        have hgg' : g = g' := by
          apply hsimple
          apply Prod.ext
          · exact hgLeft.trans hg'Left.symm
          · exact hgy.trans hg'y.symm
        exact hg'ne hgg'.symm
      exact ⟨g', hg'Left, hg'f, hg'Right⟩
    · exact ⟨g, hgLeft, hgf, hgy⟩

  obtain ⟨g, hgLeft, hgf, hgy⟩ := hgood
  have hgrightOut : (Sum.inr (G.right g) : X ⊕ Y) ∉ W := by
    intro hrightIn
    have hgRightCut : g ∈ G.cutFromRight W :=
      (G.mem_cutFromRight W g).2 ⟨by simpa [hgLeft] using hx0out, hrightIn⟩
    have hgfEq : g = f := by
      rw [heqRight] at hgRightCut
      simpa using hgRightCut
    exact hgf hgfEq
  have hx0out' : (Sum.inl x0 : X ⊕ Y) ∉ W' := by
    simp [W', hx0out]
  have hgrightOut' : (Sum.inr (G.right g) : X ⊕ Y) ∉ W' := by
    simp [W', hgrightOut, hgy]
  have hW'compLarge : 1 < W'ᶜ.card := by
    apply Finset.one_lt_card_iff_nontrivial.mpr
    refine ⟨.inl x0, Finset.mem_compl.mpr hx0out',
      .inr (G.right g), Finset.mem_compl.mpr hgrightOut', by simp⟩
  have hnontriv : IsNontrivialCutShore W' := ⟨hW'large, hW'compLarge⟩

  have hcutEq : G.edgeCut W' = G.cutFromRight W' := by
    rw [G.edgeCut_eq_oriented_union W', hleftEmpty]
    simp

  /- Matching balance now forces every perfect matching to cross `W'` exactly
     once, so `W'` is a tight cut. -/
  have hTight : G.IsTightCut W' := by
    intro P hP
    have hmatchBal := hP.cut_orientation_balance W'
    rw [hleftVertices, hrightVertices, hleftEmpty] at hmatchBal
    simp only [Finset.inter_empty, Finset.card_empty, Nat.add_zero] at hmatchBal
    rw [Finset.card_insert_of_not_mem hy0notRight] at hmatchBal
    have hselected : (P ∩ G.cutFromRight W').card = 1 := by omega
    rw [hcutEq]
    exact hselected

  exact (hbrace.2 W' hnontriv) hTight

end BipartiteMultigraph
end BachThesisLean
