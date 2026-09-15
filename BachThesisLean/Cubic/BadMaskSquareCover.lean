import BachThesisLean.Cubic.MinimalSquareCount
import BachThesisLean.Cubic.SquarePortAvoidance
import BachThesisLean.Cubic.PortMasks

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Bad root masks and square covers

The local port-mask characterization sharpens the minimum-counterexample square
restriction.  A singleton root mask has one and only one bad root port, so
that bad pair covers every square.  A zero root mask makes every root port bad;
choosing, for each square, a cubic root port outside that square forces the
prescribed edge itself onto the square.  Since one fixed edge belongs to at
most two left-indexed square supports, the zero-mask case has at most two.
-/

namespace IsMinimalEEPCounterexample

/-- A zero edge-root mask makes the prescribed edge bad with every root port. -/
theorem badPair_with_port_of_edgeRootMask_card_eq_zero
    (hmin : G.IsMinimalEEPCounterexample)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r)
    (hzero :
      (G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e).card = 0)
    (i : Fin 3) :
    e ≠ (G.portsOfCubic hmin.cubic r i).val ∧
      ¬ G.EdgePairWitness e (G.portsOfCubic hmin.cubic r i).val := by
  let ports : G.PortEnumeration r := G.portsOfCubic hmin.cubic r
  have hpiInc : G.Incident (ports i).val r :=
    (mem_incidentEdges G r (ports i).val).1 (ports i).property
  have hei : e ≠ (ports i).val := by
    intro h
    apply hne
    rw [h]
    exact hpiInc
  refine ⟨by simpa [ports] using hei, ?_⟩
  intro hw
  have hw' : G.EdgePairWitness e (ports i).val := by
    simpa [ports] using hw
  obtain ⟨j, hj, _⟩ :=
    (G.edgePairWitness_port_iff_exists_mask_ne r ports e i).1 hw'
  have hempty : G.edgeRootMask r ports e = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [ports] using hzero
  rw [hempty] at hj
  simp at hj

/-- If a nonincident prescribed edge has zero root mask in a minimum
counterexample, that edge belongs to every displayed square. -/
theorem edge_on_every_square_of_edgeRootMask_card_eq_zero
    (hmin : G.IsMinimalEEPCounterexample)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r)
    (hzero :
      (G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e).card = 0)
    (Q : SquareFrame G) :
    ¬ Q.OutsideSquare e := by
  intro heOut
  obtain ⟨i, hiOut⟩ :=
    Q.exists_port_outsideSquare_of_cubic hmin.cubic r
  obtain ⟨hei, hbad⟩ :=
    hmin.badPair_with_port_of_edgeRootMask_card_eq_zero r e hne hzero i
  have hmeet :=
    SquareFrame.IsMinimalEEPCounterexample.badPair_meets_square_exactly_one
      hmin Q hei hbad
  rcases hmeet with hfirst | hsecond
  · exact hfirst.1 heOut
  · exact hsecond.2 hiOut

/-- The zero-mask case has at most two left-indexed square supports. -/
theorem squareLeftPairs_card_le_two_of_edgeRootMask_card_eq_zero
    (hmin : G.IsMinimalEEPCounterexample)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r)
    (hzero :
      (G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e).card = 0) :
    G.squareLeftPairs.card ≤ 2 := by
  classical
  have hsimple : G.IsSimple :=
    hmin.isBrace.isSimple_of_three_le_card_left hmin.cubic (by
      have hfive := hmin.five_le_card_left
      omega)
  let A : Finset (Finset X) := G.squareLeftPairsAtEdge e
  have hcover : G.squareLeftPairs ⊆ A := by
    intro S hS
    obtain ⟨W, -⟩ :=
      G.exists_indexedSquareFrameOfSquareLeftPair hsimple hmin.cubic hS
    have heSquare : ¬ W.frame.OutsideSquare e :=
      hmin.edge_on_every_square_of_edgeRootMask_card_eq_zero
        r e hne hzero W.frame
    have hSe : S ∈ G.squareLeftPairsAtEdge e :=
      W.mem_squareLeftPairsAtEdge_of_not_outside hsimple e heSquare
    simpa [A] using hSe
  have hcard : G.squareLeftPairs.card ≤ A.card := Finset.card_le_card hcover
  have hA : A.card ≤ 2 := by
    simpa [A] using G.squareLeftPairsAtEdge_card_le_two hsimple hmin.cubic e
  omega

/-- A singleton edge-root mask has a unique bad port. -/
theorem exists_unique_bad_port_of_edgeRootMask_card_eq_one
    (hmin : G.IsMinimalEEPCounterexample)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r)
    (hone :
      (G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e).card = 1) :
    ∃ i : Fin 3,
      i ∈ G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e ∧
      ∀ k : Fin 3,
        (¬ G.EdgePairWitness e (G.portsOfCubic hmin.cubic r k).val) ↔ k = i := by
  classical
  let ports : G.PortEnumeration r := G.portsOfCubic hmin.cubic r
  let M : Finset (Fin 3) := G.edgeRootMask r ports e
  have hMcard : M.card = 1 := by simpa [M, ports] using hone
  have hMpos : 0 < M.card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hMpos
  refine ⟨i, by simpa [M, ports] using hi, ?_⟩
  intro k
  constructor
  · intro hbad
    by_contra hki
    have hik : i ≠ k := Ne.symm hki
    have hw : G.EdgePairWitness e (ports k).val :=
      (G.edgePairWitness_port_iff_exists_mask_ne r ports e k).2
        ⟨i, by simpa [M] using hi, hik⟩
    exact hbad (by simpa [ports] using hw)
  · intro hki
    subst k
    intro hw
    have hw' : G.EdgePairWitness e (ports i).val := by
      simpa [ports] using hw
    obtain ⟨j, hj, hji⟩ :=
      (G.edgePairWitness_port_iff_exists_mask_ne r ports e i).1 hw'
    have htwo : 1 < M.card := by
      rw [Finset.one_lt_card]
      exact ⟨j, by simpa [M] using hj, i, hi, hji⟩
    rw [hMcard] at htwo
    omega

/-- In the singleton-mask case, the unique bad port and the prescribed edge
cover every displayed square. -/
theorem exists_singleton_bad_port_covering_every_square
    (hmin : G.IsMinimalEEPCounterexample)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r)
    (hone :
      (G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e).card = 1) :
    ∃ i : Fin 3,
      i ∈ G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e ∧
      (∀ k : Fin 3,
        (¬ G.EdgePairWitness e (G.portsOfCubic hmin.cubic r k).val) ↔ k = i) ∧
      ∀ Q : SquareFrame G,
        ¬ Q.OutsideSquare e ∨
          ¬ Q.OutsideSquare (G.portsOfCubic hmin.cubic r i).val := by
  obtain ⟨i, hi, huniq⟩ :=
    hmin.exists_unique_bad_port_of_edgeRootMask_card_eq_one r e hne hone
  refine ⟨i, hi, huniq, ?_⟩
  intro Q
  have hpiInc :
      G.Incident (G.portsOfCubic hmin.cubic r i).val r :=
    (mem_incidentEdges G r (G.portsOfCubic hmin.cubic r i).val).1
      (G.portsOfCubic hmin.cubic r i).property
  have hei : e ≠ (G.portsOfCubic hmin.cubic r i).val := by
    intro h
    apply hne
    rw [h]
    exact hpiInc
  have hbad :
      ¬ G.EdgePairWitness e (G.portsOfCubic hmin.cubic r i).val :=
    (huniq i).2 rfl
  have hmeet :=
    SquareFrame.IsMinimalEEPCounterexample.badPair_meets_square_exactly_one
      hmin Q hei hbad
  rcases hmeet with hfirst | hsecond
  · exact Or.inl hfirst.1
  · exact Or.inr hsecond.2

/-- The singleton-mask case inherits the global four-square-support bound. -/
theorem squareLeftPairs_card_le_four_of_edgeRootMask_card_eq_one
    (hmin : G.IsMinimalEEPCounterexample)
    (r : X ⊕ Y) (e : E) (hne : ¬ G.Incident e r)
    (hone :
      (G.edgeRootMask r (G.portsOfCubic hmin.cubic r) e).card = 1) :
    G.squareLeftPairs.card ≤ 4 := by
  exact hmin.squareLeftPairs_card_le_four

end IsMinimalEEPCounterexample
end BipartiteMultigraph
end BachThesisLean
