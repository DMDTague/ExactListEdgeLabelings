import BachThesisLean.Cubic.BraceSquareIndex

namespace BachThesisLean
namespace BipartiteMultigraph
namespace SquareFrame

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# A displayed square misses one port at every cubic root

A cubic root has three distinct incident edge copies.  A displayed square can
use at most the two square copies in one row or one column at that root.  The
third port is therefore outside the square.  The proof is phrased directly in
terms of the `PortEnumeration`, so parallel copies elsewhere remain distinct.
-/

/-- At every vertex of a cubic graph, at least one of its three enumerated
incident copies is outside any fixed displayed square. -/
theorem exists_port_outsideSquare_of_cubic
    (Q : SquareFrame G) (hG : G.IsCubic) (r : X ⊕ Y) :
    ∃ i : Fin 3, Q.OutsideSquare ((G.portsOfCubic hG r) i).val := by
  classical
  let ports : G.PortEnumeration r := G.portsOfCubic hG r
  by_contra hnone
  push_neg at hnone
  have hex : ∀ i : Fin 3, ∃ a b : Bool,
      (ports i).val = Q.square a b := by
    intro i
    exact (Q.not_outsideSquare_iff_exists_square (ports i).val).1 (hnone i)
  choose a b hab using hex
  rcases r with x | y
  · have hrow : ∀ i : Fin 3, Q.leftVertex (a i) = x := by
      intro i
      have hi : G.Incident (ports i).val (.inl x) :=
        (mem_incidentEdges G (.inl x) (ports i).val).1 (ports i).property
      change G.left (ports i).val = x at hi
      rw [hab i, Q.square_left] at hi
      exact hi
    have hleftInj : Function.Injective Q.leftVertex := by
      intro p q hp
      cases p <;> cases q
      · rfl
      · exact False.elim (Q.leftVertex_ne hp)
      · exact False.elim (Q.leftVertex_ne hp.symm)
      · rfl
    have ha : ∀ i j : Fin 3, a i = a j := by
      intro i j
      apply hleftInj
      exact (hrow i).trans (hrow j).symm
    have hbInj : Function.Injective b := by
      intro i j hij
      apply ports.injective
      apply Subtype.ext
      rw [hab i, hab j, ha i j, hij]
    have hcard : Fintype.card (Fin 3) ≤ Fintype.card Bool :=
      Fintype.card_le_of_injective b hbInj
    have : 3 ≤ 2 := by simpa using hcard
    omega
  · have hcol : ∀ i : Fin 3, Q.rightVertex (b i) = y := by
      intro i
      have hi : G.Incident (ports i).val (.inr y) :=
        (mem_incidentEdges G (.inr y) (ports i).val).1 (ports i).property
      change G.right (ports i).val = y at hi
      rw [hab i, Q.square_right] at hi
      exact hi
    have hrightInj : Function.Injective Q.rightVertex := by
      intro p q hp
      cases p <;> cases q
      · rfl
      · exact False.elim (Q.rightVertex_ne hp)
      · exact False.elim (Q.rightVertex_ne hp.symm)
      · rfl
    have hb : ∀ i j : Fin 3, b i = b j := by
      intro i j
      apply hrightInj
      exact (hcol i).trans (hcol j).symm
    have haInj : Function.Injective a := by
      intro i j hij
      apply ports.injective
      apply Subtype.ext
      rw [hab i, hab j, hb i j, hij]
    have hcard : Fintype.card (Fin 3) ≤ Fintype.card Bool :=
      Fintype.card_le_of_injective a haInj
    have : 3 ≤ 2 := by simpa using hcard
    omega

end SquareFrame
end BipartiteMultigraph
end BachThesisLean
