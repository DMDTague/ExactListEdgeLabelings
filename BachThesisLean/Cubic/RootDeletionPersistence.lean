import BachThesisLean.Cubic.TwoFactorRootComponent

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Components disjoint from a deleted root

Deleting all selected edges incident with a vertex changes only the component
of that vertex.  These elementary reachability lemmas complement the
root-component path lemmas and are useful for 3-edge-sum/tight-cut gluing.
-/

/-- A selected adjacency whose two endpoints are not the deleted root survives
unchanged after all selected root edges are deleted. -/
theorem SelectedAdjacent.of_factorDeleteRoot_of_ne
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    {root u v : X ⊕ Y}
    (h : G.SelectedAdjacent S u v) (hu : u ≠ root) (hv : v ≠ root) :
    G.SelectedAdjacent (G.factorDeleteRoot S root) u v := by
  classical
  rcases h with ⟨e, heS, hdir | hdir⟩
  · refine ⟨e, (G.mem_factorDeleteRoot S root e).2 ⟨heS, ?_⟩, Or.inl hdir⟩
    intro heRoot
    have hinc := ((G.mem_selectedIncident S root e).1 heRoot).2
    cases root with
    | inl x =>
        change G.left e = x at hinc
        apply hu
        exact hdir.1.trans (congrArg Sum.inl hinc)
    | inr y =>
        change G.right e = y at hinc
        apply hv
        exact hdir.2.trans (congrArg Sum.inr hinc)
  · refine ⟨e, (G.mem_factorDeleteRoot S root e).2 ⟨heS, ?_⟩, Or.inr hdir⟩
    intro heRoot
    have hinc := ((G.mem_selectedIncident S root e).1 heRoot).2
    cases root with
    | inl x =>
        change G.left e = x at hinc
        apply hv
        exact hdir.2.trans (congrArg Sum.inl hinc)
    | inr y =>
        change G.right e = y at hinc
        apply hu
        exact hdir.1.trans (congrArg Sum.inr hinc)

/-- If the component of `u` does not contain `root`, every selected path from
`u` survives deletion of the selected root edges. -/
theorem FactorReachable.factorDeleteRoot_of_not_reaches_root
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    {root u v : X ⊕ Y}
    (h : G.FactorReachable S u v)
    (hroot : ¬ G.FactorReachable S u root) :
    G.FactorReachable (G.factorDeleteRoot S root) u v := by
  classical
  induction h with
  | refl => exact G.factorReachable_refl (G.factorDeleteRoot S root) u
  | @tail b c hprev hstep ih =>
      have hbne : b ≠ root := by
        intro hb
        subst b
        exact hroot hprev
      have hcne : c ≠ root := by
        intro hc
        subst c
        exact hroot (Relation.ReflTransGen.tail hprev hstep)
      exact Relation.ReflTransGen.tail ih
        (hstep.of_factorDeleteRoot_of_ne hbne hcne)

/-- Symmetric formulation: if the deleted root is outside the component of
`u`, deleting the root preserves every reachability relation inside that
component. -/
theorem FactorReachable.factorDeleteRoot_of_root_not_reaches
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    {root u v : X ⊕ Y}
    (h : G.FactorReachable S u v)
    (hroot : ¬ G.FactorReachable S root u) :
    G.FactorReachable (G.factorDeleteRoot S root) u v := by
  apply h.factorDeleteRoot_of_not_reaches_root
  intro hur
  exact hroot hur.symm

end BipartiteMultigraph
end BachThesisLean
