import BachThesisLean.Cubic.Isomorphism
import BachThesisLean.Cubic.BraceSimplicity

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w u' v' w'

variable {X : Type u} {Y : Type v} {E : Type w}
variable {X' : Type u'} {Y' : Type v'} {E' : Type w'}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [Fintype X'] [Fintype Y'] [Fintype E']
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq E']

/-!
# Isomorphisms from occupied endpoint cells

For simple bipartite multigraphs there is at most one actual edge copy in any
left/right endpoint cell.  Consequently, once relabellings of the two shores
preserve exactly which cells are occupied, the edge-copy equivalence is forced.
This small construction lets later finite classifications work entirely with
the missing-cell relation and recover a genuine `GraphIso` only at the end.
-/

/-- A pair of shore equivalences preserving occupied endpoint cells between
simple bipartite graphs lifts canonically (up to choice of the unique edge in
each cell) to an edge-copy graph isomorphism. -/
noncomputable def graphIsoOfSupportEquiv
    (G : BipartiteMultigraph X Y E) (H : BipartiteMultigraph X' Y' E')
    (hsimpleG : G.IsSimple) (hsimpleH : H.IsSimple)
    (leftEquiv : X ≃ X') (rightEquiv : Y ≃ Y')
    (hsupport : ∀ x y,
      (∃ e : E, G.left e = x ∧ G.right e = y) ↔
        ∃ e' : E', H.left e' = leftEquiv x ∧ H.right e' = rightEquiv y) :
    GraphIso G H := by
  classical
  have hexists : ∀ e : E, ∃ e' : E',
      H.left e' = leftEquiv (G.left e) ∧
      H.right e' = rightEquiv (G.right e) := by
    intro e
    exact (hsupport (G.left e) (G.right e)).1 ⟨e, rfl, rfl⟩
  choose edgeMap hmapLeft hmapRight using hexists
  have hedgeInj : Function.Injective edgeMap := by
    intro e f hef
    apply hsimpleG
    apply Prod.ext
    · apply leftEquiv.injective
      rw [← hmapLeft e, ← hmapLeft f, hef]
    · apply rightEquiv.injective
      rw [← hmapRight e, ← hmapRight f, hef]
  have hedgeSurj : Function.Surjective edgeMap := by
    intro e'
    let x : X := leftEquiv.symm (H.left e')
    let y : Y := rightEquiv.symm (H.right e')
    have htarget :
        ∃ f : E', H.left f = leftEquiv x ∧ H.right f = rightEquiv y := by
      refine ⟨e', ?_, ?_⟩
      · simp [x]
      · simp [y]
    obtain ⟨e, heL, heR⟩ := (hsupport x y).2 htarget
    refine ⟨e, ?_⟩
    apply hsimpleH
    apply Prod.ext
    · change H.left (edgeMap e) = H.left e'
      rw [hmapLeft e, heL]
      simp [x]
    · change H.right (edgeMap e) = H.right e'
      rw [hmapRight e, heR]
      simp [y]
  let edgeEquiv : E ≃ E' := Equiv.ofBijective edgeMap ⟨hedgeInj, hedgeSurj⟩
  exact
    { leftEquiv := leftEquiv
      rightEquiv := rightEquiv
      edgeEquiv := edgeEquiv
      map_left := by
        intro e
        change H.left (edgeMap e) = leftEquiv (G.left e)
        exact hmapLeft e
      map_right := by
        intro e
        change H.right (edgeMap e) = rightEquiv (G.right e)
        exact hmapRight e }

end BipartiteMultigraph
end BachThesisLean
