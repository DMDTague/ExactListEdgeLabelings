import BachThesisLean.Cubic.ConnectedRootDeletion
import BachThesisLean.Cubic.StarProductFactorLift
import BachThesisLean.Cubic.Regression
import BachThesisLean.Cubic.ShoreSwap

namespace BachThesisLean
namespace BipartiteMultigraph

open CubicRegression

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Connectivity of the fixed-amplifier star product

The universal amplification theorem quantifies only over connected cubic
multigraphs, so the four-vertex gadget must preserve connectedness.  The
amplifier minus its first left vertex is a three-edge path core joining its two
right vertices.  Every surviving source vertex reaches some deleted-root port,
and every such port reaches that core through its bridge.
-/

/-- Every right vertex of the fixed amplifier reaches right vertex `0` inside
an arbitrary star product, using only surviving internal amplifier edges. -/
theorem starProduct_amplifier_right_reaches_hub
    (A : BipartiteMultigraph X Y E) (r : Y)
    (p : A.PortEnumeration (.inr r)) (σ : Equiv.Perm (Fin 3))
    (y : Fin 2) :
    (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
      (.inr (.inr y)) (.inr (.inr (0 : Fin 2))) := by
  classical
  fin_cases y
  · exact (A.starProduct amplifier r 0 p amplifierPorts σ).factorReachable_refl
      Finset.univ (.inr (.inr (0 : Fin 2)))
  · let e4 : StarEdge A amplifier r 0 :=
      .inr (.inl ⟨(4 : Fin 6), by decide⟩)
    let e3 : StarEdge A amplifier r 0 :=
      .inr (.inl ⟨(3 : Fin 6), by decide⟩)
    have h4 :=
      (A.starProduct amplifier r 0 p amplifierPorts σ).factorReachable_endpoints
        (S := Finset.univ) (e := e4) (by simp)
    have h3 :=
      (A.starProduct amplifier r 0 p amplifierPorts σ).factorReachable_endpoints
        (S := Finset.univ) (e := e3) (by simp)
    simpa [e4, e3, starProduct, amplifier] using h4.symm.trans h3

/-- The sole surviving left vertex of the amplifier reaches the same hub. -/
theorem starProduct_amplifier_left_reaches_hub
    (A : BipartiteMultigraph X Y E) (r : Y)
    (p : A.PortEnumeration (.inr r)) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 2 // x ≠ 0}) :
    (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
      (.inl (.inr x)) (.inr (.inr (0 : Fin 2))) := by
  classical
  have hxval : x.1 = (1 : Fin 2) := by omega
  have hx : x = (⟨1, by decide⟩ : {x : Fin 2 // x ≠ 0}) :=
    Subtype.ext hxval
  rw [hx]
  let e3 : StarEdge A amplifier r 0 :=
    .inr (.inl ⟨(3 : Fin 6), by decide⟩)
  have h3 :=
    (A.starProduct amplifier r 0 p amplifierPorts σ).factorReachable_endpoints
      (S := Finset.univ) (e := e3) (by simp)
  simpa [e3, starProduct, amplifier] using h3

/-- Every joining bridge leads from its source port endpoint into the connected
amplifier core. -/
theorem starProduct_amplifier_bridge_reaches_hub
    (A : BipartiteMultigraph X Y E) (r : Y)
    (p : A.PortEnumeration (.inr r)) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) :
    (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
      (.inl (.inl (A.left (p i).1)))
      (.inr (.inr (0 : Fin 2))) := by
  let b : StarEdge A amplifier r 0 := .inr (.inr i)
  have hb :=
    (A.starProduct amplifier r 0 p amplifierPorts σ).factorReachable_endpoints
      (S := Finset.univ) (e := b) (by simp)
  have hcore := A.starProduct_amplifier_right_reaches_hub r p σ
    (amplifier.right (amplifierPorts (σ i)).1)
  have hb' :
      (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
        (.inl (.inl (A.left (p i).1)))
        (.inr (.inr (amplifier.right (amplifierPorts (σ i)).1))) := by
    simpa [b, starProduct] using hb
  exact hb'.trans hcore

/-- A surviving source vertex, represented through `starAVertexMap`, reaches
the amplifier hub. -/
theorem starProduct_amplifier_starAVertexMap_reaches_hub
    (A : BipartiteMultigraph X Y E) (hconn : A.IsConnected)
    (r : Y) (p : A.PortEnumeration (.inr r)) (σ : Equiv.Perm (Fin 3))
    (z : X ⊕ Y) (hz : z ≠ .inr r) :
    (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
      (A.starAVertexMap amplifier r 0 p z)
      (.inr (.inr (0 : Fin 2))) := by
  classical
  rcases hconn.factorDeleteRightRoot_reaches_some_incident r z with hroot | ⟨a, ha, hpath⟩
  · exact (hz hroot).elim
  · let i : Fin 3 := p.symm ⟨a, ha⟩
    have hpi : (p i).1 = a := by
      exact congrArg Subtype.val (p.apply_symm_apply ⟨a, ha⟩)
    have hpath' :
        A.FactorReachable (A.factorDeleteRoot (∅ : Finset E)ᶜ (.inr r))
          (.inl (A.left a)) z := by
      simpa using hpath
    have hlift :=
      A.factorReachable_starA_of_factorDeleteRoot amplifier r 0 p amplifierPorts σ
        (∅ : Finset E) (∅ : Finset (Fin 6)) (0 : Fin 3) hpath'
    have hliftU := hlift.mono (fun _ _ => Finset.mem_univ _)
    have htoPort :
        (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
          (A.starAVertexMap amplifier r 0 p z)
          (.inl (.inl (A.left a))) := by
      simpa [starAVertexMap] using hliftU.symm
    have hbridge := A.starProduct_amplifier_bridge_reaches_hub r p σ i
    have hbridge' :
        (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
          (.inl (.inl (A.left a)))
          (.inr (.inr (0 : Fin 2))) := by
      simpa [hpi] using hbridge
    exact htoPort.trans hbridge'

/-- Every star-product vertex reaches a fixed hub in the amplifier. -/
theorem starProduct_amplifier_reaches_hub
    (A : BipartiteMultigraph X Y E) (hconn : A.IsConnected)
    (r : Y) (p : A.PortEnumeration (.inr r)) (σ : Equiv.Perm (Fin 3))
    (z : StarLeft X (Fin 2) 0 ⊕ StarRight Y (Fin 2) r) :
    (A.starProduct amplifier r 0 p amplifierPorts σ).FactorReachable Finset.univ
      z (.inr (.inr (0 : Fin 2))) := by
  rcases z with z | z
  · rcases z with x | x
    · simpa using
        A.starProduct_amplifier_starAVertexMap_reaches_hub hconn r p σ
          (.inl x) (by simp)
    · exact A.starProduct_amplifier_left_reaches_hub r p σ x
  · rcases z with y | y
    · have hy : (Sum.inr y.1 : X ⊕ Y) ≠ .inr r := by
        intro h
        exact y.2 (Sum.inr.inj h)
      simpa [starAVertexMap, y.2] using
        A.starProduct_amplifier_starAVertexMap_reaches_hub hconn r p σ
          (.inr y.1) hy
    · exact A.starProduct_amplifier_right_reaches_hub r p σ y

/-- Star product with the fixed four-vertex amplifier preserves connectedness. -/
theorem starProduct_amplifier_isConnected
    (A : BipartiteMultigraph X Y E) (hconn : A.IsConnected)
    (r : Y) (p : A.PortEnumeration (.inr r)) (σ : Equiv.Perm (Fin 3)) :
    (A.starProduct amplifier r 0 p amplifierPorts σ).IsConnected := by
  let hub : StarLeft X (Fin 2) 0 ⊕ StarRight Y (Fin 2) r :=
    .inr (.inr (0 : Fin 2))
  refine ⟨⟨hub⟩, ?_⟩
  intro u v
  have hu := A.starProduct_amplifier_reaches_hub hconn r p σ u
  have hv := A.starProduct_amplifier_reaches_hub hconn r p σ v
  exact hu.trans hv.symm

/-- The left-root orientation used by the amplifier reduction is connected as
well, by applying the preceding theorem after shore exchange. -/
theorem shoreSwap_starProduct_amplifier_isConnected
    (A : BipartiteMultigraph X Y E) (hconn : A.IsConnected)
    (x : X) (p : A.PortEnumeration (.inl x)) (σ : Equiv.Perm (Fin 3)) :
    (A.shoreSwap.starProduct amplifier x 0
      (A.shoreSwapPortEnumeration (.inl x) p) amplifierPorts σ).IsConnected := by
  exact A.shoreSwap.starProduct_amplifier_isConnected
    ((A.shoreSwap_isConnected_iff).2 hconn) x
      (A.shoreSwapPortEnumeration (.inl x) p) σ

end BipartiteMultigraph
end BachThesisLean
