import BachThesisLean.Cubic.StarProductPfaffianSamePortB

namespace BachThesisLean
namespace BipartiteMultigraph

open scoped BigOperators

universe uA vA wA uB vB wB

variable {XA : Type uA} {YA : Type vA} {EA : Type wA}
variable {XB : Type uB} {YB : Type vB} {EB : Type wB}
variable [Fintype XA] [Fintype YA] [Fintype EA]
variable [Fintype XB] [Fintype YB] [Fintype EB]
variable [DecidableEq XA] [DecidableEq YA] [DecidableEq EA]
variable [DecidableEq XB] [DecidableEq YB] [DecidableEq EB]

/-!
# Normalizing the three Pfaffian port classes on the B factor

The `B` ports are named in bridge order: class `i` is the actual source edge
`q (σ i)`, exactly the edge represented by bridge `i`.  The same-port theorem
then gives one raw signed-term constant in each class.  Multiplying the sign of
that root-port copy by `T 0 * (T i)⁻¹` aligns all three constants.
-/

/-- Reindex the native `B` port enumeration into star-bridge order. -/
def bridgeOrderedBPorts
    (B : BipartiteMultigraph XB YB EB) (ell : XB)
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3)) :
    B.PortEnumeration (.inl ell) :=
  σ.trans q

@[simp] theorem bridgeOrderedBPorts_apply_val
    (B : BipartiteMultigraph XB YB EB) (ell : XB)
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ((bridgeOrderedBPorts B ell q σ) i).1 = (q (σ i)).1 := rfl

/-- Edge signs inherited by the `B` source factor from the star product. -/
def sourceBInheritedEdgeSign
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference) :
    EB → ℤˣ :=
  fun e => S.edgeSign (A.starBEdge B r ell q σ e)

/-- Cubicity supplies a perfect-matching representative through each `B` port
in bridge order. -/
noncomputable def sourceBPortRepresentative
    (B : BipartiteMultigraph XB YB EB) (hB : B.IsCubic)
    (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    {P : B.PerfectMatching // ((bridgeOrderedBPorts B ell q σ) i).1 ∈ P.val} := by
  classical
  let h := B.exists_perfectMatching_containing_edge_of_cubic hB
    ((bridgeOrderedBPorts B ell q σ) i).1
  let P : Finset EB := Classical.choose h
  have hspec : B.IsPerfectMatching P ∧
      ((bridgeOrderedBPorts B ell q σ) i).1 ∈ P := Classical.choose_spec h
  exact ⟨⟨P, hspec.1⟩, hspec.2⟩

/-- Any two `B` perfect matchings in the same bridge-ordered root-port class
already have the same raw signed term under inherited signs. -/
theorem PfaffianSigning.sourceB_raw_signedTerm_eq_of_samePort
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceB : XB ≃ YB)
    (P Q : B.PerfectMatching) (i : Fin 3)
    (hPi : ((bridgeOrderedBPorts B ell q σ) i).1 ∈ P.val)
    (hQi : ((bridgeOrderedBPorts B ell q σ) i).1 ∈ Q.val) :
    P.signedTerm referenceB
        (sourceBInheritedEdgeSign A B r ell p q σ S) =
      Q.signedTerm referenceB
        (sourceBInheritedEdgeSign A B r ell p q σ S) := by
  classical
  obtain ⟨PA, hPA, hAi⟩ :=
    A.exists_perfectMatching_containing_edge_of_cubic hA (p i).1
  apply (P.signedTerm_eq_iff_relative referenceB
    (sourceBInheritedEdgeSign A B r ell p q σ S) Q).2
  simpa [sourceBInheritedEdgeSign, bridgeOrderedBPorts] using
    PfaffianSigning.sourceB_samePort_relative_product_eq
      A B r ell p q σ S PA P.val Q.val i
      hPA P.property Q.property hAi hPi hQi

/-- Raw signed term of the chosen representative of bridge class `i`. -/
noncomputable def sourceBPortRawTerm
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB) (i : Fin 3) : ℤˣ :=
  (sourceBPortRepresentative B hB ell q σ i).val.signedTerm referenceB
    (sourceBInheritedEdgeSign A B r ell p q σ S)

/-- Correction for bridge-ordered `B` port class `i`. -/
noncomputable def sourceBPortCorrection
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB) (i : Fin 3) : ℤˣ :=
  sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 *
    (sourceBPortRawTerm A B r ell p q σ S hB referenceB i)⁻¹

/-- Only edges at the deleted `B` left root receive a class correction. -/
noncomputable def sourceBPortCorrectionFactor
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB) (e : EB) : ℤˣ :=
  if h : B.left e = ell then
    sourceBPortCorrection A B r ell p q σ S hB referenceB
      ((bridgeOrderedBPorts B ell q σ).symm
        ⟨e, (mem_incidentEdges B (.inl ell) e).2 (by
          simpa [Incident] using h)⟩)
  else 1

@[simp] theorem sourceBPortCorrectionFactor_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB) (i : Fin 3) :
    sourceBPortCorrectionFactor A B r ell p q σ S hB referenceB
        ((bridgeOrderedBPorts B ell q σ) i).1 =
      sourceBPortCorrection A B r ell p q σ S hB referenceB i := by
  classical
  have hroot : B.left ((bridgeOrderedBPorts B ell q σ) i).1 = ell := by
    exact B.port_left_eq ell (bridgeOrderedBPorts B ell q σ) i
  simp only [sourceBPortCorrectionFactor, dif_pos hroot]
  congr 1
  apply (bridgeOrderedBPorts B ell q σ).injective
  rw [Equiv.apply_symm_apply]

/-- In a matching using bridge-ordered port `i`, the product of all B-side
correction factors is exactly the one class correction. -/
theorem sourceBPortCorrectionFactor_prod_of_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB)
    (P : Finset EB) (hP : B.IsPerfectMatching P) (i : Fin 3)
    (hPi : ((bridgeOrderedBPorts B ell q σ) i).1 ∈ P) :
    (∏ e ∈ P,
      sourceBPortCorrectionFactor A B r ell p q σ S hB referenceB e) =
      sourceBPortCorrection A B r ell p q σ S hB referenceB i := by
  classical
  let qStar := bridgeOrderedBPorts B ell q σ
  calc
    (∏ e ∈ P,
      sourceBPortCorrectionFactor A B r ell p q σ S hB referenceB e) =
        sourceBPortCorrectionFactor A B r ell p q σ S hB referenceB (qStar i).1 := by
      apply Finset.prod_eq_single_of_mem (qStar i).1 hPi
      intro e heP hne
      by_cases hl : B.left e = ell
      · have heq : e = (qStar i).1 :=
          (B.isMatching_iff P).1 hP.isMatching e heP (qStar i).1 hPi (.inl ell)
            (by simpa [Incident] using hl) (by simp [Incident, qStar])
        exact (hne heq).elim
      · simp [sourceBPortCorrectionFactor, hl]
    _ = sourceBPortCorrection A B r ell p q σ S hB referenceB i := by
      simpa [qStar] using
        sourceBPortCorrectionFactor_port A B r ell p q σ S hB referenceB i

/-- Corrected edge signing on `B`. -/
noncomputable def sourceBNormalizedEdgeSign
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB) : EB → ℤˣ :=
  fun e => sourceBInheritedEdgeSign A B r ell p q σ S e *
    sourceBPortCorrectionFactor A B r ell p q σ S hB referenceB e

/-- A B-matching in class `i` acquires exactly its class correction. -/
theorem sourceBNormalizedEdgeSign_prod_of_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceB : XB ≃ YB)
    (P : Finset EB) (hP : B.IsPerfectMatching P) (i : Fin 3)
    (hPi : ((bridgeOrderedBPorts B ell q σ) i).1 ∈ P) :
    (∏ e ∈ P, sourceBNormalizedEdgeSign
      A B r ell p q σ S hB referenceB e) =
      (∏ e ∈ P, sourceBInheritedEdgeSign A B r ell p q σ S e) *
        sourceBPortCorrection A B r ell p q σ S hB referenceB i := by
  classical
  calc
    (∏ e ∈ P, sourceBNormalizedEdgeSign
      A B r ell p q σ S hB referenceB e) =
      (∏ e ∈ P, sourceBInheritedEdgeSign A B r ell p q σ S e) *
        ∏ e ∈ P,
          sourceBPortCorrectionFactor A B r ell p q σ S hB referenceB e := by
            simp only [sourceBNormalizedEdgeSign]
            exact Finset.prod_mul_distrib
    _ = (∏ e ∈ P, sourceBInheritedEdgeSign A B r ell p q σ S e) *
        sourceBPortCorrection A B r ell p q σ S hB referenceB i := by
      rw [sourceBPortCorrectionFactor_prod_of_port
        A B r ell p q σ S hB referenceB P hP i hPi]

/-- Every corrected B-side signed term equals the raw representative term of
bridge class `0`. -/
theorem PfaffianSigning.sourceB_normalized_signedTerm_eq_base
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (hB : B.IsCubic) (referenceB : XB ≃ YB)
    (P : B.PerfectMatching) (i : Fin 3)
    (hPi : ((bridgeOrderedBPorts B ell q σ) i).1 ∈ P.val) :
    P.signedTerm referenceB
        (sourceBNormalizedEdgeSign A B r ell p q σ S hB referenceB) =
      sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 := by
  have hraw :
      P.signedTerm referenceB
          (sourceBInheritedEdgeSign A B r ell p q σ S) =
        sourceBPortRawTerm A B r ell p q σ S hB referenceB i := by
    exact S.sourceB_raw_signedTerm_eq_of_samePort
      A B r ell p q σ hA referenceB P
      (sourceBPortRepresentative B hB ell q σ i).val i hPi
      (sourceBPortRepresentative B hB ell q σ i).property
  have hprod := sourceBNormalizedEdgeSign_prod_of_port
    A B r ell p q σ S hB referenceB P.val P.property i hPi
  calc
    P.signedTerm referenceB
        (sourceBNormalizedEdgeSign A B r ell p q σ S hB referenceB) =
      P.signedTerm referenceB
          (sourceBInheritedEdgeSign A B r ell p q σ S) *
        sourceBPortCorrection A B r ell p q σ S hB referenceB i := by
          unfold PerfectMatching.signedTerm
          rw [hprod]
          ac_rfl
    _ = sourceBPortRawTerm A B r ell p q σ S hB referenceB i *
        sourceBPortCorrection A B r ell p q σ S hB referenceB i := by rw [hraw]
    _ = sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 := by
      rw [sourceBPortCorrection]
      calc
        sourceBPortRawTerm A B r ell p q σ S hB referenceB i *
            (sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 *
              (sourceBPortRawTerm A B r ell p q σ S hB referenceB i)⁻¹) =
          sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 *
            (sourceBPortRawTerm A B r ell p q σ S hB referenceB i *
              (sourceBPortRawTerm A B r ell p q σ S hB referenceB i)⁻¹) := by
                ac_rfl
        _ = sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 := by simp

/-- Port normalization turns the inherited signing into a genuine Pfaffian
signing on the cubic `B` factor. -/
noncomputable def PfaffianSigning.normalizeSourceB
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (hB : B.IsCubic) (referenceB : XB ≃ YB) :
    PfaffianSigning B referenceB where
  edgeSign := sourceBNormalizedEdgeSign A B r ell p q σ S hB referenceB
  terms_eq := by
    intro P Q
    let qStar := bridgeOrderedBPorts B ell q σ
    obtain ⟨i, hPi, -⟩ := P.property.existsUnique_port (.inl ell) qStar
    obtain ⟨j, hQj, -⟩ := Q.property.existsUnique_port (.inl ell) qStar
    calc
      P.signedTerm referenceB
          (sourceBNormalizedEdgeSign A B r ell p q σ S hB referenceB) =
        sourceBPortRawTerm A B r ell p q σ S hB referenceB 0 :=
          S.sourceB_normalized_signedTerm_eq_base
            A B r ell p q σ hA hB referenceB P i hPi
      _ = Q.signedTerm referenceB
          (sourceBNormalizedEdgeSign A B r ell p q σ S hB referenceB) :=
          (S.sourceB_normalized_signedTerm_eq_base
            A B r ell p q σ hA hB referenceB Q j hQj).symm

/-- Witness-level form: a Pfaffian cubic star product has a Pfaffian `B`
factor. -/
noncomputable def PfaffianSigning.sourceBPfaffianWitness
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (hB : B.IsCubic) : PfaffianWitness B := by
  classical
  let P0 : B.PerfectMatching := Classical.choice (B.exists_perfectMatching_of_cubic hB)
  let referenceB : XB ≃ YB := P0.shoreEquiv
  exact ⟨referenceB,
    S.normalizeSourceB A B r ell p q σ hA hB referenceB⟩

end BipartiteMultigraph
end BachThesisLean
