import BachThesisLean.Cubic.TwoFactorRootPathLeft

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Root-deletion reachability for whole two-factor components

The port-to-port lemmas show that deleting a vertex from a two-factor opens its
cycle into a path between the two selected root edges.  The lemmas below add
the form needed by the star-product criterion: every vertex that was in the
root component remains reachable from either residual port endpoint, unless it
is the deleted root itself.
-/

/-- Right-root version.  Fix any selected edge `a` at the deleted right root.
Every vertex in the original two-factor component of that root is either the
root itself or is reachable, after root deletion, from the opposite endpoint
of `a`. -/
theorem IsTwoFactor.factorDeleteRightRoot_reaches_of_root_reachable
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {r : Y} {a : E}
    (ha : a ∈ G.selectedIncident S (.inr r)) {z : X ⊕ Y}
    (hz : G.FactorReachable S (.inr r) z) :
    z = .inr r ∨
      G.FactorReachable (G.factorDeleteRoot S (.inr r))
        (.inl (G.left a)) z := by
  classical
  let T := G.factorDeleteRoot S (.inr r)
  induction hz with
  | refl =>
      exact Or.inl rfl
  | @tail b c hprev hstep ih =>
      rcases ih with hbroot | hbT
      · subst b
        rcases hstep with ⟨e, heS, hdir | hdir⟩
        · cases hdir.1
        · right
          have heRoot : e ∈ G.selectedIncident S (.inr r) := by
            apply (G.mem_selectedIncident S (.inr r) e).2
            refine ⟨heS, ?_⟩
            change G.right e = r
            exact Sum.inr.inj hdir.1.symm
          have hports := hS.factorDeleteRightRoot_reaches_between_ports ha heRoot
          rw [hdir.2]
          simpa [T] using hports
      · have hbne : b ≠ (Sum.inr r : X ⊕ Y) := by
          intro hb
          subst b
          have heq := hbT.eq_of_target_isolated (by
            simpa [T] using
              G.selectedIncident_factorDeleteRoot_root S (.inr r))
          simpa using heq
        by_cases hcroot : c = (Sum.inr r : X ⊕ Y)
        · exact Or.inl hcroot
        · right
          apply hbT.tail
          rcases hstep with ⟨e, heS, hdir | hdir⟩
          · have hnotRoot : e ∉ G.selectedIncident S (.inr r) := by
              intro heRoot
              have hinc := ((G.mem_selectedIncident S (.inr r) e).1 heRoot).2
              change G.right e = r at hinc
              apply hcroot
              exact hdir.2.trans
                (congrArg (fun y : Y => (Sum.inr y : X ⊕ Y)) hinc)
            exact ⟨e, (G.mem_factorDeleteRoot S (.inr r) e).2 ⟨heS, hnotRoot⟩,
              Or.inl hdir⟩
          · have hnotRoot : e ∉ G.selectedIncident S (.inr r) := by
              intro heRoot
              have hinc := ((G.mem_selectedIncident S (.inr r) e).1 heRoot).2
              change G.right e = r at hinc
              apply hbne
              exact hdir.1.trans
                (congrArg (fun y : Y => (Sum.inr y : X ⊕ Y)) hinc)
            exact ⟨e, (G.mem_factorDeleteRoot S (.inr r) e).2 ⟨heS, hnotRoot⟩,
              Or.inr hdir⟩

/-- Left-root version of `factorDeleteRightRoot_reaches_of_root_reachable`. -/
theorem IsTwoFactor.factorDeleteLeftRoot_reaches_of_root_reachable
    {G : BipartiteMultigraph X Y E} {S : Finset E}
    (hS : G.IsTwoFactor S) {ell : X} {a : E}
    (ha : a ∈ G.selectedIncident S (.inl ell)) {z : X ⊕ Y}
    (hz : G.FactorReachable S (.inl ell) z) :
    z = .inl ell ∨
      G.FactorReachable (G.factorDeleteRoot S (.inl ell))
        (.inr (G.right a)) z := by
  classical
  let T := G.factorDeleteRoot S (.inl ell)
  induction hz with
  | refl =>
      exact Or.inl rfl
  | @tail b c hprev hstep ih =>
      rcases ih with hbroot | hbT
      · subst b
        rcases hstep with ⟨e, heS, hdir | hdir⟩
        · right
          have heRoot : e ∈ G.selectedIncident S (.inl ell) := by
            apply (G.mem_selectedIncident S (.inl ell) e).2
            refine ⟨heS, ?_⟩
            change G.left e = ell
            exact Sum.inl.inj hdir.1.symm
          have hports := hS.factorDeleteLeftRoot_reaches_between_ports ha heRoot
          rw [hdir.2]
          simpa [T] using hports
        · cases hdir.1
      · have hbne : b ≠ (Sum.inl ell : X ⊕ Y) := by
          intro hb
          subst b
          have heq := hbT.eq_of_target_isolated (by
            simpa [T] using
              G.selectedIncident_factorDeleteRoot_root S (.inl ell))
          simpa using heq
        by_cases hcroot : c = (Sum.inl ell : X ⊕ Y)
        · exact Or.inl hcroot
        · right
          apply hbT.tail
          rcases hstep with ⟨e, heS, hdir | hdir⟩
          · have hnotRoot : e ∉ G.selectedIncident S (.inl ell) := by
              intro heRoot
              have hinc := ((G.mem_selectedIncident S (.inl ell) e).1 heRoot).2
              change G.left e = ell at hinc
              apply hbne
              exact hdir.1.trans
                (congrArg (fun x : X => (Sum.inl x : X ⊕ Y)) hinc)
            exact ⟨e, (G.mem_factorDeleteRoot S (.inl ell) e).2 ⟨heS, hnotRoot⟩,
              Or.inl hdir⟩
          · have hnotRoot : e ∉ G.selectedIncident S (.inl ell) := by
              intro heRoot
              have hinc := ((G.mem_selectedIncident S (.inl ell) e).1 heRoot).2
              change G.left e = ell at hinc
              apply hcroot
              exact hdir.2.trans
                (congrArg (fun x : X => (Sum.inl x : X ⊕ Y)) hinc)
            exact ⟨e, (G.mem_factorDeleteRoot S (.inl ell) e).2 ⟨heS, hnotRoot⟩,
              Or.inr hdir⟩

end BipartiteMultigraph
end BachThesisLean
