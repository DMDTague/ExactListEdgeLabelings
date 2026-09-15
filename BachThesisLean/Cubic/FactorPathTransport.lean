import BachThesisLean.Cubic.Foundations

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
# Transporting factor reachability along edge replacements

Square smoothing and star-product reconstruction repeatedly replace one
selected edge by a path.  Reachability needs only a path for each selected
adjacency, not a literal edge map.  The theorem below packages that induction
once for reuse by the square-factor lift.
-/

/-- A reachability path transports through a vertex map whenever each selected
source adjacency is replaced by target reachability between the mapped
endpoints. -/
theorem FactorReachable.of_edge_paths
    {G : BipartiteMultigraph X Y E}
    {H : BipartiteMultigraph X' Y' E'}
    {S : Finset E} {T : Finset E'}
    {u v : X ⊕ Y}
    (φ : X ⊕ Y → X' ⊕ Y')
    (hstep : ∀ a b, G.SelectedAdjacent S a b →
      H.FactorReachable T (φ a) (φ b))
    (h : G.FactorReachable S u v) :
    H.FactorReachable T (φ u) (φ v) := by
  induction h with
  | refl => exact H.factorReachable_refl T (φ u)
  | tail _ hab ih => exact ih.trans (hstep _ _ hab)

end BipartiteMultigraph
end BachThesisLean
