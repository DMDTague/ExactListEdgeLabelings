import BachThesisLean.Cubic.UniversalAmplification
import BachThesisLean.Cubic.AmplifierConnectivity

namespace BachThesisLean
namespace BipartiteMultigraph

open CubicRegression

/-!
# Universal EEP--EVP amplification equivalence

This is manuscript Theorem `thm:universal-eep-evp`.  The universal statement
is written over finite `Type`-level edge-copy presentations so that the same
quantifier can be instantiated directly with the fixed four-vertex star
products (and with their shore swaps).  Every finite graph admits such a
presentation.
-/

/-- Universal prescribed-edge-pair and prescribed-edge-vertex properties are
equivalent for connected cubic bipartite multigraphs. -/
theorem universal_connected_cubic_hasEEP_iff_hasEVP :
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEEP) ↔
    (∀ (X Y E : Type)
      [Fintype X] [Fintype Y] [Fintype E]
      [DecidableEq X] [DecidableEq Y] [DecidableEq E],
      ∀ G : BipartiteMultigraph X Y E,
        G.IsConnected → G.IsCubic → G.HasEVP) := by
  constructor
  · intro hEEP X Y E instX instY instE decX decY decE G hconn hG
    exact (hEEP X Y E G hconn hG).hasEVP hG
  · intro hEVP X Y E instX instY instE decX decY decE A hconn hA
    by_contra hnotEEP
    rcases A.not_hasEEP_implies_not_hasEVP_or_fourVertexAmplifier
      hconn hA hnotEEP with hself | hright | hleft
    · exact hself (hEVP X Y E A hconn hA)
    · obtain ⟨r, σ, hfail⟩ := hright
      let p : A.PortEnumeration (.inr r) := A.portsOfCubic hA (.inr r)
      let Gstar := A.starProduct amplifier r 0 p amplifierPorts σ
      have hconnStar : Gstar.IsConnected :=
        A.starProduct_amplifier_isConnected hconn r p σ
      have hcubStar : Gstar.IsCubic :=
        A.starProduct_isCubic amplifier r 0 p amplifierPorts σ hA amplifier_cubic
      apply hfail
      simpa [Gstar, p] using
        (hEVP
          (StarLeft X (Fin 2) 0)
          (StarRight Y (Fin 2) r)
          (StarEdge A amplifier r 0)
          Gstar hconnStar hcubStar)
    · obtain ⟨x, σ, hfail⟩ := hleft
      let p : A.PortEnumeration (.inl x) := A.portsOfCubic hA (.inl x)
      let ps : A.shoreSwap.PortEnumeration (.inr x) :=
        A.shoreSwapPortEnumeration (.inl x) p
      let Gstar := A.shoreSwap.starProduct amplifier x 0 ps amplifierPorts σ
      have hconnStar : Gstar.IsConnected :=
        A.shoreSwap_starProduct_amplifier_isConnected hconn x p σ
      have hswapCubic : A.shoreSwap.IsCubic :=
        (A.shoreSwap_isCubic_iff).2 hA
      have hcubStar : Gstar.IsCubic :=
        A.shoreSwap.starProduct_isCubic amplifier x 0 ps amplifierPorts σ
          hswapCubic amplifier_cubic
      apply hfail
      simpa [Gstar, p, ps] using
        (hEVP
          (StarLeft Y (Fin 2) 0)
          (StarRight X (Fin 2) x)
          (StarEdge A.shoreSwap amplifier x 0)
          Gstar hconnStar hcubStar)

end BipartiteMultigraph
end BachThesisLean
