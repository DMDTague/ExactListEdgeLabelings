import BachThesisLean.Cubic.TightCutCorrespondence
import BachThesisLean.Cubic.TightCutContractionSize

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# Reduction of EEP to braces

A connected cubic bipartite multigraph is either already a brace or has a
nontrivial tight cut.  In the latter case, normalize the cut orientation,
contract both shores, recurse on the two strictly smaller connected cubic
factors, and recover EEP by the tight-cut correspondence.
-/

/-- If every connected cubic brace has EEP, then every connected cubic
bipartite multigraph has EEP.  The induction measure is the total number of
vertices, and nontriviality of the tight cut makes both contractions strictly
smaller. -/
theorem universal_connected_cubic_hasEEP_of_braces
    (hBrace :
      ∀ (X Y E : Type)
        [Fintype X] [Fintype Y] [Fintype E]
        [DecidableEq X] [DecidableEq Y] [DecidableEq E],
        ∀ G : BipartiteMultigraph X Y E,
          G.IsConnected → G.IsCubic → G.IsBrace → G.HasEEP) :
    ∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEEP := by
  classical
  let Good : ℕ → Prop := fun n =>
    ∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.vertexCard = n → G.IsConnected → G.IsCubic → G.HasEEP
  have hGood : ∀ n, Good n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp [Good]
        intro X Y E instX instY instE decX decY decE G hsize hconn hCubic
        by_cases hbrace : G.IsBrace
        · exact hBrace X Y E G hconn hCubic hbrace
        · have hMC : G.IsMatchingCovered :=
            G.isMatchingCovered_of_connected_cubic hconn hCubic
          have hsplit :
              ∃ W : Finset (X ⊕ Y),
                IsNontrivialCutShore W ∧ G.IsTightCut W := by
            by_contra hnone
            apply hbrace
            refine ⟨hMC, ?_⟩
            intro W hnontriv hT
            apply hnone
            exact ⟨W, hnontriv, hT⟩
          obtain ⟨W, hnontriv, hT⟩ := hsplit
          obtain ⟨U, _, hTU, hUnontriv, hOrient⟩ :=
            hT.exists_right_oriented_shore hconn hCubic hnontriv
          have hConnected :=
            hTU.right_oriented_contractions_connected hconn hUnontriv hOrient
          have hCubics :=
            hTU.right_oriented_contractions_cubic hconn hCubic hOrient
          have hSetLt : (G.contractSet U).vertexCard < n := by
            have h := G.contractSet_vertexCard_lt U hUnontriv
            simpa [hsize] using h
          have hComplementLt : (G.contractComplement U).vertexCard < n := by
            have h := G.contractComplement_vertexCard_lt U hUnontriv
            simpa [hsize] using h
          have hSetEEP : (G.contractSet U).HasEEP := by
            exact
              (ih (G.contractSet U).vertexCard hSetLt)
                (ContractSetLeft X Y U)
                (ContractSetRight X Y U)
                (ContractSetEdge G U)
                (G.contractSet U) rfl hConnected.2 hCubics.2
          have hComplementEEP : (G.contractComplement U).HasEEP := by
            exact
              (ih (G.contractComplement U).vertexCard hComplementLt)
                (ContractComplementLeft X Y U)
                (ContractComplementRight X Y U)
                (ContractComplementEdge G U)
                (G.contractComplement U) rfl hConnected.1 hCubics.1
          exact
            (hTU.right_oriented_hasEEP_iff_contractions hconn hCubic hOrient).2
              ⟨hSetEEP, hComplementEEP⟩
  intro X Y E instX instY instE decX decY decE G hconn hCubic
  exact hGood G.vertexCard X Y E G rfl hconn hCubic

/-- Universal EEP for connected cubic bipartite multigraphs is equivalent to
EEP on the brace cases. -/
theorem universal_connected_cubic_hasEEP_iff_braces :
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEEP) ↔
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.IsBrace → G.HasEEP) := by
  constructor
  · intro h X Y E instX instY instE decX decY decE G hconn hCubic _
    exact h X Y E G hconn hCubic
  · exact universal_connected_cubic_hasEEP_of_braces

end BipartiteMultigraph
end BachThesisLean
