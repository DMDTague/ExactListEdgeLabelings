import BachThesisLean.Cubic.BraceReduction
import BachThesisLean.Cubic.TinyBraceCases
import BachThesisLean.Cubic.UniversalEEPEVP

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# Universal prescribed-pair reduction to braces

The universal EEP--EVP amplification theorem and the tight-cut brace reduction
combine without any additional graph construction.  The direct simplicity
theorem and the two finite tiny cases then sharpen the terminal class to simple
cubic bipartite braces, matching the manuscript's universal prescribed-pair
reduction.
-/

/-- Universal EVP is equivalent to EEP on all connected cubic bipartite
braces. -/
theorem universal_connected_cubic_hasEVP_iff_braces :
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEVP) ↔
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.IsBrace → G.HasEEP) := by
  exact universal_connected_cubic_hasEEP_iff_hasEVP.symm.trans
    universal_connected_cubic_hasEEP_iff_braces

/-- Universal EEP is already determined by the simple cubic bipartite braces.
The two possible smaller shore sizes are discharged by the finite tiny-case
certificates. -/
theorem universal_connected_cubic_hasEEP_iff_simple_braces :
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEEP) ↔
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.IsBrace → G.IsSimple → G.HasEEP) := by
  rw [universal_connected_cubic_hasEEP_iff_braces]
  constructor
  · intro h X Y E instX instY instE decX decY decE G hconn hG hbrace _
    exact h X Y E G hconn hG hbrace
  · intro h X Y E instX instY instE decX decY decE G hconn hG hbrace
    by_cases hlarge : 3 ≤ Fintype.card X
    · exact h X Y E G hconn hG hbrace
        (hbrace.isSimple_of_three_le_card_left hG hlarge)
    · have hsmall : Fintype.card X < 3 := by omega
      exact G.hasEEP_of_connected_cubic_card_left_lt_three hconn hG hsmall

/-- Manuscript corollary: universal EVP, universal EEP, and EEP restricted to
simple cubic bipartite braces are equivalent. -/
theorem universal_connected_cubic_hasEVP_iff_simple_braces :
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEVP) ↔
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.IsBrace → G.IsSimple → G.HasEEP) := by
  exact universal_connected_cubic_hasEEP_iff_hasEVP.symm.trans
    universal_connected_cubic_hasEEP_iff_simple_braces

end BipartiteMultigraph
end BachThesisLean
