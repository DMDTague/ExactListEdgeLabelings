import BachThesisLean.Cubic.StarProductPfaffianSamePort

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
# Normalizing the three Pfaffian port classes on the A factor

The preceding same-port theorem shows that the inherited star-product edge
signs already give one constant signed term inside each of the three matching
port classes of `A`.  This file aligns those three constants.

Choose one perfect-matching representative through every root port.  If its
raw signed term is `T i`, multiply the sign of port `i` by
`T 0 * (T i)⁻¹`.  Every perfect matching uses exactly one root port, so its
edge-sign product acquires exactly the correction for its class.  Its raw term
is already `T i`; hence every corrected signed term is `T 0`.
-/

/-- Edge signs inherited by the `A` source factor from the star product. -/
def sourceAInheritedEdgeSign
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference) :
    EA → ℤˣ :=
  fun e => S.edgeSign (A.starAEdge B r ell p e)

/-- Cubicity supplies a perfect-matching representative through each actual
root-port edge copy.  The membership proof is stored with the representative. -/
noncomputable def sourceAPortRepresentative
    (A : BipartiteMultigraph XA YA EA) (hA : A.IsCubic)
    (r : YA) (p : A.PortEnumeration (.inr r)) (i : Fin 3) :
    {P : A.PerfectMatching // (p i).1 ∈ P.val} := by
  classical
  let h := A.exists_perfectMatching_containing_edge_of_cubic hA (p i).1
  let P : Finset EA := Classical.choose h
  have hspec : A.IsPerfectMatching P ∧ (p i).1 ∈ P := Classical.choose_spec h
  exact ⟨⟨P, hspec.1⟩, hspec.2⟩

/-- Any two `A` perfect matchings in the same root-port class already have the
same raw signed term under the inherited edge signs. -/
theorem PfaffianSigning.sourceA_raw_signedTerm_eq_of_samePort
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hB : B.IsCubic) (referenceA : XA ≃ YA)
    (P Q : A.PerfectMatching) (i : Fin 3)
    (hPi : (p i).1 ∈ P.val) (hQi : (p i).1 ∈ Q.val) :
    P.signedTerm referenceA
        (sourceAInheritedEdgeSign A B r ell p q σ S) =
      Q.signedTerm referenceA
        (sourceAInheritedEdgeSign A B r ell p q σ S) := by
  classical
  obtain ⟨PB, hPB, hBi⟩ :=
    B.exists_perfectMatching_containing_edge_of_cubic hB (q (σ i)).1
  apply (P.signedTerm_eq_iff_relative referenceA
    (sourceAInheritedEdgeSign A B r ell p q σ S) Q).2
  simpa [sourceAInheritedEdgeSign] using
    PfaffianSigning.sourceA_samePort_relative_product_eq
      A B r ell p q σ S P.val Q.val PB i
      P.property Q.property hPB hPi hQi hBi

/-- Raw signed term of the chosen representative of port class `i`. -/
noncomputable def sourceAPortRawTerm
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA) (i : Fin 3) : ℤˣ :=
  (sourceAPortRepresentative A hA r p i).val.signedTerm referenceA
    (sourceAInheritedEdgeSign A B r ell p q σ S)

/-- Correction applied to port class `i`, normalized against class `0`. -/
noncomputable def sourceAPortCorrection
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA) (i : Fin 3) : ℤˣ :=
  sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 *
    (sourceAPortRawTerm A B r ell p q σ S hA referenceA i)⁻¹

/-- Only root-port edges receive a correction factor. -/
noncomputable def sourceAPortCorrectionFactor
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA) (e : EA) : ℤˣ :=
  if h : A.right e = r then
    sourceAPortCorrection A B r ell p q σ S hA referenceA
      (p.symm ⟨e, (mem_incidentEdges A (.inr r) e).2 (by
        simpa [Incident] using h)⟩)
  else 1

@[simp] theorem sourceAPortCorrectionFactor_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA) (i : Fin 3) :
    sourceAPortCorrectionFactor A B r ell p q σ S hA referenceA (p i).1 =
      sourceAPortCorrection A B r ell p q σ S hA referenceA i := by
  classical
  have hroot : A.right (p i).1 = r := A.port_right_eq r p i
  simp [sourceAPortCorrectionFactor, hroot]

/-- In a matching using port `i`, the product of all correction factors is
exactly the single class correction for `i`. -/
theorem sourceAPortCorrectionFactor_prod_of_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA)
    (P : Finset EA) (hP : A.IsPerfectMatching P) (i : Fin 3)
    (hPi : (p i).1 ∈ P) :
    (∏ e ∈ P,
      sourceAPortCorrectionFactor A B r ell p q σ S hA referenceA e) =
      sourceAPortCorrection A B r ell p q σ S hA referenceA i := by
  classical
  calc
    (∏ e ∈ P,
      sourceAPortCorrectionFactor A B r ell p q σ S hA referenceA e) =
        sourceAPortCorrectionFactor A B r ell p q σ S hA referenceA (p i).1 := by
      apply Finset.prod_eq_single_of_mem (p i).1 hPi
      intro e heP hne
      by_cases hr : A.right e = r
      · have heq : e = (p i).1 :=
          (A.isMatching_iff P).1 hP.isMatching e heP (p i).1 hPi (.inr r)
            (by simpa [Incident] using hr) (by simp [Incident])
        exact (hne heq).elim
      · simp [sourceAPortCorrectionFactor, hr]
    _ = sourceAPortCorrection A B r ell p q σ S hA referenceA i := by simp

/-- Corrected edge signing on `A`. -/
noncomputable def sourceANormalizedEdgeSign
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA) : EA → ℤˣ :=
  fun e => sourceAInheritedEdgeSign A B r ell p q σ S e *
    sourceAPortCorrectionFactor A B r ell p q σ S hA referenceA e

/-- A matching in port class `i` acquires exactly the class correction. -/
theorem sourceANormalizedEdgeSign_prod_of_port
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (referenceA : XA ≃ YA)
    (P : Finset EA) (hP : A.IsPerfectMatching P) (i : Fin 3)
    (hPi : (p i).1 ∈ P) :
    (∏ e ∈ P, sourceANormalizedEdgeSign
      A B r ell p q σ S hA referenceA e) =
      (∏ e ∈ P, sourceAInheritedEdgeSign A B r ell p q σ S e) *
        sourceAPortCorrection A B r ell p q σ S hA referenceA i := by
  classical
  calc
    (∏ e ∈ P, sourceANormalizedEdgeSign
      A B r ell p q σ S hA referenceA e) =
      (∏ e ∈ P, sourceAInheritedEdgeSign A B r ell p q σ S e) *
        ∏ e ∈ P,
          sourceAPortCorrectionFactor A B r ell p q σ S hA referenceA e := by
            simp only [sourceANormalizedEdgeSign]
            exact Finset.prod_mul_distrib
    _ = (∏ e ∈ P, sourceAInheritedEdgeSign A B r ell p q σ S e) *
        sourceAPortCorrection A B r ell p q σ S hA referenceA i := by
      rw [sourceAPortCorrectionFactor_prod_of_port
        A B r ell p q σ S hA referenceA P hP i hPi]

/-- Every corrected signed term is the raw representative term of class `0`. -/
theorem PfaffianSigning.sourceA_normalized_signedTerm_eq_base
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (hB : B.IsCubic) (referenceA : XA ≃ YA)
    (P : A.PerfectMatching) (i : Fin 3) (hPi : (p i).1 ∈ P.val) :
    P.signedTerm referenceA
        (sourceANormalizedEdgeSign A B r ell p q σ S hA referenceA) =
      sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 := by
  have hraw :
      P.signedTerm referenceA
          (sourceAInheritedEdgeSign A B r ell p q σ S) =
        sourceAPortRawTerm A B r ell p q σ S hA referenceA i := by
    exact S.sourceA_raw_signedTerm_eq_of_samePort
      A B r ell p q σ hB referenceA P
      (sourceAPortRepresentative A hA r p i).val i hPi
      (sourceAPortRepresentative A hA r p i).property
  have hprod := sourceANormalizedEdgeSign_prod_of_port
    A B r ell p q σ S hA referenceA P.val P.property i hPi
  calc
    P.signedTerm referenceA
        (sourceANormalizedEdgeSign A B r ell p q σ S hA referenceA) =
      P.signedTerm referenceA
          (sourceAInheritedEdgeSign A B r ell p q σ S) *
        sourceAPortCorrection A B r ell p q σ S hA referenceA i := by
          unfold PerfectMatching.signedTerm
          rw [hprod]
          ac_rfl
    _ = sourceAPortRawTerm A B r ell p q σ S hA referenceA i *
        sourceAPortCorrection A B r ell p q σ S hA referenceA i := by rw [hraw]
    _ = sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 := by
      rw [sourceAPortCorrection]
      calc
        sourceAPortRawTerm A B r ell p q σ S hA referenceA i *
            (sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 *
              (sourceAPortRawTerm A B r ell p q σ S hA referenceA i)⁻¹) =
          sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 *
            (sourceAPortRawTerm A B r ell p q σ S hA referenceA i *
              (sourceAPortRawTerm A B r ell p q σ S hA referenceA i)⁻¹) := by
                ac_rfl
        _ = sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 := by simp

/-- Port normalization turns the inherited signing into a genuine Pfaffian
signing on the cubic `A` factor. -/
noncomputable def PfaffianSigning.normalizeSourceA
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (hB : B.IsCubic) (referenceA : XA ≃ YA) :
    PfaffianSigning A referenceA where
  edgeSign := sourceANormalizedEdgeSign A B r ell p q σ S hA referenceA
  terms_eq := by
    intro P Q
    obtain ⟨i, hPi, -⟩ := P.property.existsUnique_port (.inr r) p
    obtain ⟨j, hQj, -⟩ := Q.property.existsUnique_port (.inr r) p
    calc
      P.signedTerm referenceA
          (sourceANormalizedEdgeSign A B r ell p q σ S hA referenceA) =
        sourceAPortRawTerm A B r ell p q σ S hA referenceA 0 :=
          S.sourceA_normalized_signedTerm_eq_base
            A B r ell p q σ hA hB referenceA P i hPi
      _ = Q.signedTerm referenceA
          (sourceANormalizedEdgeSign A B r ell p q σ S hA referenceA) :=
          (S.sourceA_normalized_signedTerm_eq_base
            A B r ell p q σ hA hB referenceA Q j hQj).symm

/-- Witness-level form: a Pfaffian cubic star product has a Pfaffian `A`
factor.  The reference on `A` is taken from any cubic perfect matching. -/
noncomputable def PfaffianSigning.sourceAPfaffianWitness
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    {reference : StarLeft XA XB ell ≃ StarRight YA YB r}
    (S : PfaffianSigning (A.starProduct B r ell p q σ) reference)
    (hA : A.IsCubic) (hB : B.IsCubic) : PfaffianWitness A := by
  classical
  let P0 : A.PerfectMatching := Classical.choice (A.exists_perfectMatching_of_cubic hA)
  let referenceA : XA ≃ YA := P0.shoreEquiv
  exact ⟨referenceA,
    S.normalizeSourceA A B r ell p q σ hA hB referenceA⟩

end BipartiteMultigraph
end BachThesisLean
