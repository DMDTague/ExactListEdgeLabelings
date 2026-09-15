import BachThesisLean.Cubic.TF3ProbeWitness
import BachThesisLean.Cubic.ShoreSwap
import BachThesisLean.Cubic.UniversalEEPEVP

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# The unconditional probe direction: universal TF3 implies universal EVP

The manuscript's reverse pointwise direction `EVP → TF3` invokes an external
brace theorem.  This file deliberately proves only the elementary direction
that needs no external input: applying universal `TF3` to the two-vertex probe
forces the prescribed edge and vertex into one complementary factor component.
-/

/-- Universal `TF3` on connected cubic bipartite multigraphs implies universal
EVP.  Left-shore targets use the probe directly; right-shore targets use the
same probe after exchanging the bipartition shores. -/
theorem universal_connected_cubic_hasTF3_implies_hasEVP
    (hTF3 :
      ∀ (X Y E : Type)
        [Fintype X] [Fintype Y] [Fintype E]
        [DecidableEq X] [DecidableEq Y] [DecidableEq E],
        ∀ G : BipartiteMultigraph X Y E,
          G.IsConnected → G.IsCubic → G.HasTF3) :
    ∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEVP := by
  intro X Y E instX instY instE decX decY decE G hconn hG e z
  cases z with
  | inl x =>
      have hpConn : (G.edgeProbe e).IsConnected :=
        G.edgeProbe_isConnected hconn e
      have hpCubic : (G.edgeProbe e).IsCubic :=
        G.edgeProbe_isCubic hG e
      have hpTF3 : (G.edgeProbe e).HasTF3 :=
        hTF3 (EdgeProbeLeft X) (EdgeProbeRight Y) (EdgeProbeEdge e)
          (G.edgeProbe e) hpConn hpCubic
      exact G.edgeProbe_hasTF3_edgeVertex_left hG e x hpTF3
  | inr y =>
      let H : BipartiteMultigraph Y X E := G.shoreSwap
      have hHconn : H.IsConnected := by
        simpa [H] using (G.shoreSwap_isConnected_iff).2 hconn
      have hHCubic : H.IsCubic := by
        simpa [H] using (G.shoreSwap_isCubic_iff).2 hG
      have hpConn : (H.edgeProbe e).IsConnected :=
        H.edgeProbe_isConnected hHconn e
      have hpCubic : (H.edgeProbe e).IsCubic :=
        H.edgeProbe_isCubic hHCubic e
      have hpTF3 : (H.edgeProbe e).HasTF3 :=
        hTF3 (EdgeProbeLeft Y) (EdgeProbeRight X) (EdgeProbeEdge e)
          (H.edgeProbe e) hpConn hpCubic
      obtain ⟨P, root, hP, heCarry, hyReach⟩ :=
        H.edgeProbe_hasTF3_edgeVertex_left hHCubic e y hpTF3
      have hPswap : G.shoreSwap.IsPerfectMatching P := by
        simpa [H] using hP
      have heSwap : G.shoreSwap.ComponentCarries Pᶜ root e := by
        simpa [H] using heCarry
      have hySwap :
          G.shoreSwap.FactorReachable Pᶜ root (.inl y) := by
        simpa [H] using hyReach
      refine ⟨P, shoreSwapVertex root,
        (G.shoreSwap_isPerfectMatching_iff P).1 hPswap, ?_, ?_⟩
      · apply (G.shoreSwap_componentCarries_iff Pᶜ
          (shoreSwapVertex root) e).1
        simpa using heSwap
      · apply (G.shoreSwap_factorReachable_iff Pᶜ
          (shoreSwapVertex root) (.inr y)).1
        simpa using hySwap

/-- Consequently universal `TF3` also implies universal EEP, through the
already formalized universal EEP--EVP equivalence. -/
theorem universal_connected_cubic_hasTF3_implies_hasEEP
    (hTF3 :
      ∀ (X Y E : Type)
        [Fintype X] [Fintype Y] [Fintype E]
        [DecidableEq X] [DecidableEq Y] [DecidableEq E],
        ∀ G : BipartiteMultigraph X Y E,
          G.IsConnected → G.IsCubic → G.HasTF3) :
    ∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEEP := by
  apply universal_connected_cubic_hasEEP_iff_hasEVP.mpr
  exact universal_connected_cubic_hasTF3_implies_hasEVP hTF3

end BipartiteMultigraph
end BachThesisLean
