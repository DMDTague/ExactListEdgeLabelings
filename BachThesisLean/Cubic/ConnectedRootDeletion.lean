import BachThesisLean.Cubic.TwoFactorRootPath

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Connected graphs after deleting one root

For the fixed-amplifier reduction we need a graph-theoretic analogue of the
two-factor root-deletion lemmas: in a connected graph, every surviving vertex
can be reached from the opposite endpoint of some edge incident with the
deleted root, using no root-incident edges.  The statement is made directly in
the edge-copy model, so parallel edges need no special case.
-/

/-- Reachability is monotone under enlargement of the selected edge set. -/
theorem FactorReachable.mono
    {G : BipartiteMultigraph X Y E} {S T : Finset E} {u v : X ⊕ Y}
    (h : G.FactorReachable S u v) (hST : S ⊆ T) :
    G.FactorReachable T u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
      apply ih.tail
      rcases hstep with ⟨e, heS, hdir⟩
      exact ⟨e, hST heS, hdir⟩

/-- Right-root form.  Every vertex of a connected graph is either the deleted
right root itself or remains reachable, after deleting all root-incident edge
copies, from the opposite endpoint of some root edge. -/
theorem IsConnected.factorDeleteRightRoot_reaches_some_incident
    {G : BipartiteMultigraph X Y E} (hconn : G.IsConnected)
    (r : Y) (z : X ⊕ Y) :
    z = .inr r ∨
      ∃ a : E, a ∈ G.incidentEdges (.inr r) ∧
        G.FactorReachable (G.factorDeleteRoot Finset.univ (.inr r))
          (.inl (G.left a)) z := by
  classical
  let T := G.factorDeleteRoot Finset.univ (.inr r)
  have hz := hconn.2 (.inr r) z
  induction hz with
  | refl =>
      exact Or.inl rfl
  | @tail b c hprev hstep ih =>
      rcases ih with hbroot | ⟨a, haRoot, haT⟩
      · subst b
        rcases hstep with ⟨e, heU, hdir | hdir⟩
        · cases hdir.1
        · right
          have hright : G.right e = r :=
            Sum.inr.inj hdir.1.symm
          refine ⟨e, (G.mem_incidentEdges (.inr r) e).2 ?_, ?_⟩
          · exact hright
          · rw [hdir.2]
            exact G.factorReachable_refl T (.inl (G.left e))
      · have hbne : b ≠ (Sum.inr r : X ⊕ Y) := by
          intro hb
          subst b
          have heq := haT.eq_of_target_isolated (by
            simpa [T] using
              G.selectedIncident_factorDeleteRoot_root Finset.univ (.inr r))
          cases heq
        by_cases hcroot : c = (Sum.inr r : X ⊕ Y)
        · exact Or.inl hcroot
        · right
          refine ⟨a, haRoot, haT.tail ?_⟩
          rcases hstep with ⟨e, heU, hdir | hdir⟩
          · have hnotRoot : e ∉ G.selectedIncident Finset.univ (.inr r) := by
              intro heRoot
              have hinc :=
                ((G.mem_selectedIncident Finset.univ (.inr r) e).1 heRoot).2
              change G.right e = r at hinc
              apply hcroot
              exact hdir.2.trans
                (congrArg (fun y : Y => (Sum.inr y : X ⊕ Y)) hinc)
            exact ⟨e,
              (G.mem_factorDeleteRoot Finset.univ (.inr r) e).2
                ⟨heU, hnotRoot⟩,
              Or.inl hdir⟩
          · have hnotRoot : e ∉ G.selectedIncident Finset.univ (.inr r) := by
              intro heRoot
              have hinc :=
                ((G.mem_selectedIncident Finset.univ (.inr r) e).1 heRoot).2
              change G.right e = r at hinc
              apply hbne
              exact hdir.1.trans
                (congrArg (fun y : Y => (Sum.inr y : X ⊕ Y)) hinc)
            exact ⟨e,
              (G.mem_factorDeleteRoot Finset.univ (.inr r) e).2
                ⟨heU, hnotRoot⟩,
              Or.inr hdir⟩

end BipartiteMultigraph
end BachThesisLean
