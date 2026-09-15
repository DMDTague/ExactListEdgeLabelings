import BachThesisLean.Cubic.StarProductMatchingDecomposition

namespace BachThesisLean
namespace BipartiteMultigraph

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-!
# Contracting star-product complementary paths back to the factors

For the converse direction of the star-port criterion, contract the entire
opposite shore of the star product back to the deleted root.  Internal edges
on the retained factor remain selected-factor steps, internal edges on the
contracted factor become reflexive steps, and an unused bridge becomes the
corresponding unused source port.  Thus every complementary-factor path in the
star product projects to a complementary-factor path in either source graph.
-/

/-- Contract the `B` side of a star product to the deleted right root of `A`. -/
def starAContract
    (r : YA) (ell : XB) :
    StarLeft XA XB ell ⊕ StarRight YA YB r → XA ⊕ YA
  | .inl (.inl x) => .inl x
  | .inl (.inr _) => .inr r
  | .inr (.inl y) => .inr y.1
  | .inr (.inr _) => .inr r

/-- Contract the `A` side of a star product to the deleted left root of `B`. -/
def starBContract
    (r : YA) (ell : XB) :
    StarLeft XA XB ell ⊕ StarRight YA YB r → XB ⊕ YB
  | .inl (.inl _) => .inl ell
  | .inl (.inr x) => .inl x.1
  | .inr (.inl _) => .inl ell
  | .inr (.inr y) => .inr y

/-- One complementary star-product adjacency projects to reachability in the
`A` complementary factor after contracting the `B` side. -/
theorem selectedAdjacent_starAContract_of_glued_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA)
    {u v : StarLeft XA XB ell ⊕ StarRight YA YB r}
    (h : (A.starProduct B r ell p q σ).SelectedAdjacent
      (A.starGluedMatching B r ell PA PB i)ᶜ u v) :
    A.FactorReachable PAᶜ (starAContract r ell u) (starAContract r ell v) := by
  classical
  rcases h with ⟨s, hs, hdir | hdir⟩
  · rcases s with ea | rest
    · have hea : ea.1 ∈ PAᶜ := by
        rw [Finset.mem_compl]
        intro heaPA
        exact (Finset.mem_compl.mp hs)
          ((A.mem_starGluedMatching_aInternal B r ell PA PB i ea).2 heaPA)
      rcases hdir with ⟨rfl, rfl⟩
      simpa [starAContract, starProduct] using
        (A.factorReachable_endpoints hea)
    · rcases rest with eb | j
      · rcases hdir with ⟨rfl, rfl⟩
        exact A.factorReachable_refl PAᶜ (.inr r)
      · have hji : j ≠ i :=
          (A.mem_starGluedMatching_bridge_compl B r ell PA PB i j).1 hs
        have hj : (p j).1 ∈ PAᶜ :=
          (hPA.port_mem_compl_iff_ne A (.inr r) p i hpi j).2 hji
        rcases hdir with ⟨rfl, rfl⟩
        simpa [starAContract, starProduct] using
          (A.factorReachable_endpoints hj)
  · rcases s with ea | rest
    · have hea : ea.1 ∈ PAᶜ := by
        rw [Finset.mem_compl]
        intro heaPA
        exact (Finset.mem_compl.mp hs)
          ((A.mem_starGluedMatching_aInternal B r ell PA PB i ea).2 heaPA)
      rcases hdir with ⟨rfl, rfl⟩
      simpa [starAContract, starProduct] using
        (A.factorReachable_endpoints hea).symm
    · rcases rest with eb | j
      · rcases hdir with ⟨rfl, rfl⟩
        exact A.factorReachable_refl PAᶜ (.inr r)
      · have hji : j ≠ i :=
          (A.mem_starGluedMatching_bridge_compl B r ell PA PB i j).1 hs
        have hj : (p j).1 ∈ PAᶜ :=
          (hPA.port_mem_compl_iff_ne A (.inr r) p i hpi j).2 hji
        rcases hdir with ⟨rfl, rfl⟩
        simpa [starAContract, starProduct] using
          (A.factorReachable_endpoints hj).symm

/-- Every complementary star-product path projects to the `A` complement. -/
theorem factorReachable_starAContract_of_glued_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hpi : (p i).1 ∈ PA)
    {u v : StarLeft XA XB ell ⊕ StarRight YA YB r}
    (h : (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ u v) :
    A.FactorReachable PAᶜ (starAContract r ell u) (starAContract r ell v) := by
  induction h with
  | refl => exact A.factorReachable_refl PAᶜ _
  | tail hprev hstep ih =>
      exact ih.trans
        (A.selectedAdjacent_starAContract_of_glued_compl B r ell p q σ
          PA PB i hPA hpi hstep)

/-- One complementary star-product adjacency projects to reachability in the
`B` complementary factor after contracting the `A` side. -/
theorem selectedAdjacent_starBContract_of_glued_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB)
    {u v : StarLeft XA XB ell ⊕ StarRight YA YB r}
    (h : (A.starProduct B r ell p q σ).SelectedAdjacent
      (A.starGluedMatching B r ell PA PB i)ᶜ u v) :
    B.FactorReachable PBᶜ (starBContract r ell u) (starBContract r ell v) := by
  classical
  rcases h with ⟨s, hs, hdir | hdir⟩
  · rcases s with ea | rest
    · rcases hdir with ⟨rfl, rfl⟩
      exact B.factorReachable_refl PBᶜ (.inl ell)
    · rcases rest with eb | j
      · have heb : eb.1 ∈ PBᶜ := by
          rw [Finset.mem_compl]
          intro hebPB
          exact (Finset.mem_compl.mp hs)
            ((A.mem_starGluedMatching_bInternal B r ell PA PB i eb).2 hebPB)
        rcases hdir with ⟨rfl, rfl⟩
        simpa [starBContract, starProduct] using
          (B.factorReachable_endpoints heb)
      · have hji : j ≠ i :=
          (A.mem_starGluedMatching_bridge_compl B r ell PA PB i j).1 hs
        have hσji : σ j ≠ σ i := fun hσ => hji (σ.injective hσ)
        have hj : (q (σ j)).1 ∈ PBᶜ :=
          (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)).2 hσji
        rcases hdir with ⟨rfl, rfl⟩
        simpa [starBContract, starProduct] using
          (B.factorReachable_endpoints hj)
  · rcases s with ea | rest
    · rcases hdir with ⟨rfl, rfl⟩
      exact B.factorReachable_refl PBᶜ (.inl ell)
    · rcases rest with eb | j
      · have heb : eb.1 ∈ PBᶜ := by
          rw [Finset.mem_compl]
          intro hebPB
          exact (Finset.mem_compl.mp hs)
            ((A.mem_starGluedMatching_bInternal B r ell PA PB i eb).2 hebPB)
        rcases hdir with ⟨rfl, rfl⟩
        simpa [starBContract, starProduct] using
          (B.factorReachable_endpoints heb).symm
      · have hji : j ≠ i :=
          (A.mem_starGluedMatching_bridge_compl B r ell PA PB i j).1 hs
        have hσji : σ j ≠ σ i := fun hσ => hji (σ.injective hσ)
        have hj : (q (σ j)).1 ∈ PBᶜ :=
          (hPB.port_mem_compl_iff_ne B (.inl ell) q (σ i) hqi (σ j)).2 hσji
        rcases hdir with ⟨rfl, rfl⟩
        simpa [starBContract, starProduct] using
          (B.factorReachable_endpoints hj).symm

/-- Every complementary star-product path projects to the `B` complement. -/
theorem factorReachable_starBContract_of_glued_compl
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hqi : (q (σ i)).1 ∈ PB)
    {u v : StarLeft XA XB ell ⊕ StarRight YA YB r}
    (h : (A.starProduct B r ell p q σ).FactorReachable
      (A.starGluedMatching B r ell PA PB i)ᶜ u v) :
    B.FactorReachable PBᶜ (starBContract r ell u) (starBContract r ell v) := by
  induction h with
  | refl => exact B.factorReachable_refl PBᶜ _
  | tail hprev hstep ih =>
      exact ih.trans
        (A.selectedAdjacent_starBContract_of_glued_compl B r ell p q σ
          PA PB i hPB hqi hstep)

end BipartiteMultigraph
end BachThesisLean
