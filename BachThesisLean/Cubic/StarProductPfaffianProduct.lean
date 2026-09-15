import BachThesisLean.Cubic.StarProductPfaffianRelative

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
# Edge-sign products for common-completion star matchings

The images of the two source matchings cover the glued matching and overlap
exactly in the selected bridge.  `Finset.prod_union_inter` therefore gives the
bridge-corrected factorization needed to cancel a common opposite-side
completion in the Pfaffian relative equation.
-/

/-- Image of the selected `A` source edges in the star product. -/
noncomputable def starASelectedImage
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (PA : Finset EA) : Finset (StarEdge A B r ell) := by
  classical
  exact PA.image (A.starAEdge B r ell p)

/-- Image of the selected `B` source edges in the star product. -/
noncomputable def starBSelectedImage
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3)) (PB : Finset EB) : Finset (StarEdge A B r ell) := by
  classical
  exact PB.image (A.starBEdge B r ell q σ)

/-- Every selected `A` source edge maps into the glued matching. -/
theorem starASelectedImage_subset_starGluedMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPi : (p i).1 ∈ PA) :
    starASelectedImage A B r ell p PA ⊆
      A.starGluedMatching B r ell PA PB i := by
  classical
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨e, hePA, rfl⟩
  exact (A.starAEdge_mem_starGluedMatching_iff
    B r ell p PA PB i hPA hPi e).2 hePA

/-- Every selected `B` source edge maps into the glued matching. -/
theorem starBSelectedImage_subset_starGluedMatching
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (q : B.PortEnumeration (.inl ell))
    (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPB : B.IsPerfectMatching PB) (hBi : (q (σ i)).1 ∈ PB) :
    starBSelectedImage A B r ell q σ PB ⊆
      A.starGluedMatching B r ell PA PB i := by
  classical
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨e, hePB, rfl⟩
  exact (A.starBEdge_mem_starGluedMatching_iff
    B r ell q σ PA PB i hPB hBi e).2 hePB

/-- The two source images cover the glued matching exactly. -/
theorem starSelectedImages_union
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hBi : (q (σ i)).1 ∈ PB) :
    starASelectedImage A B r ell p PA ∪
        starBSelectedImage A B r ell q σ PB =
      A.starGluedMatching B r ell PA PB i := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.union_subset
      (starASelectedImage_subset_starGluedMatching
        A B r ell p PA PB i hPA hPi)
      (starBSelectedImage_subset_starGluedMatching
        A B r ell q σ PA PB i hPB hBi)
  · intro s hs
    rcases s with ea | rest
    · have hea : ea.1 ∈ PA :=
        (A.mem_starGluedMatching_aInternal B r ell PA PB i ea).1 hs
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨ea.1, hea, by
        simp [starAEdge, ea.2]⟩
    · rcases rest with eb | j
      · have heb : eb.1 ∈ PB :=
          (A.mem_starGluedMatching_bInternal B r ell PA PB i eb).1 hs
        apply Finset.mem_union_right
        exact Finset.mem_image.2 ⟨eb.1, heb, by
          simp [starBEdge, eb.2]⟩
      · have hji : j = i :=
          (A.mem_starGluedMatching_bridge B r ell PA PB i j).1 hs
        subst j
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨(p i).1, hPi, by simp⟩

/-- The only overlap of the two source images is the selected bridge. -/
theorem starSelectedImages_inter
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA)
    (hPi : (p i).1 ∈ PA) (hBi : (q (σ i)).1 ∈ PB) :
    starASelectedImage A B r ell p PA ∩
        starBSelectedImage A B r ell q σ PB =
      {(Sum.inr (Sum.inr i) : StarEdge A B r ell)} := by
  classical
  apply Finset.Subset.antisymm
  · intro s hs
    rcases Finset.mem_inter.mp hs with ⟨hA, hB⟩
    rcases Finset.mem_image.mp hA with ⟨e, hePA, hes⟩
    rcases Finset.mem_image.mp hB with ⟨f, _hfPB, hfs⟩
    have hef : A.starAEdge B r ell p e = A.starBEdge B r ell q σ f :=
      hes.trans hfs.symm
    have her : A.right e = r := by
      by_contra hne
      by_cases hfl : B.left f = ell
      · simp [starAEdge, hne, starBEdge, hfl] at hef
      · simp [starAEdge, hne, starBEdge, hfl] at hef
    have heq : e = (p i).1 :=
      (A.isMatching_iff PA).1 hPA.isMatching e hePA (p i).1 hPi (.inr r)
        (by simpa [Incident] using her) (by simp [Incident])
    have hsbridge : s = (Sum.inr (Sum.inr i) : StarEdge A B r ell) := by
      calc
        s = A.starAEdge B r ell p e := hes.symm
        _ = A.starAEdge B r ell p (p i).1 := by rw [heq]
        _ = (Sum.inr (Sum.inr i) : StarEdge A B r ell) := by simp
    simpa [hsbridge]
  · intro s hs
    have hsbridge : s = (Sum.inr (Sum.inr i) : StarEdge A B r ell) := by
      simpa using hs
    subst s
    exact Finset.mem_inter.2 ⟨
      Finset.mem_image.2 ⟨(p i).1, hPi, by simp⟩,
      Finset.mem_image.2 ⟨(q (σ i)).1, hBi, by simp⟩⟩

/-- Product factorization for a glued matching.  The selected bridge is counted
in both source products, hence the one bridge correction on the left. -/
theorem starGluedMatching_prod_mul_bridge
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hBi : (q (σ i)).1 ∈ PB)
    (edgeSign : StarEdge A B r ell → ℤˣ) :
    (∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e) *
        edgeSign (Sum.inr (Sum.inr i)) =
      (∏ e ∈ PA, edgeSign (A.starAEdge B r ell p e)) *
        ∏ e ∈ PB, edgeSign (A.starBEdge B r ell q σ e) := by
  classical
  let SA := starASelectedImage A B r ell p PA
  let SB := starBSelectedImage A B r ell q σ PB
  calc
    (∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e) *
        edgeSign (Sum.inr (Sum.inr i)) =
      (∏ e ∈ SA ∪ SB, edgeSign e) * ∏ e ∈ SA ∩ SB, edgeSign e := by
        rw [starSelectedImages_union A B r ell p q σ PA PB i hPA hPB hPi hBi,
          starSelectedImages_inter A B r ell p q σ PA PB i hPA hPi hBi]
        simp
    _ = (∏ e ∈ SA, edgeSign e) * ∏ e ∈ SB, edgeSign e :=
      Finset.prod_union_inter
    _ = (∏ e ∈ PA, edgeSign (A.starAEdge B r ell p e)) *
        ∏ e ∈ PB, edgeSign (A.starBEdge B r ell q σ e) := by
      simp [SA, SB, starASelectedImage, starBSelectedImage,
        Finset.prod_image (A.starAEdge_injective B r ell p).injOn,
        Finset.prod_image (A.starBEdge_injective B r ell q σ).injOn]

/-- If a relative product equation holds for two same-port star matchings with a
common `B` completion, the common `B` product and bridge cancel, leaving the
relative product equation on the varying `A` factor. -/
theorem sourceA_relativeProduct_of_commonStar
    (A : BipartiteMultigraph XA YA EA) (B : BipartiteMultigraph XB YB EB)
    (r : YA) (ell : XB) (p : A.PortEnumeration (.inr r))
    (q : B.PortEnumeration (.inl ell)) (σ : Equiv.Perm (Fin 3))
    (PA QA : Finset EA) (PB : Finset EB) (i : Fin 3)
    (hPA : A.IsPerfectMatching PA) (hQA : A.IsPerfectMatching QA)
    (hPB : B.IsPerfectMatching PB)
    (hPi : (p i).1 ∈ PA) (hQi : (p i).1 ∈ QA)
    (hBi : (q (σ i)).1 ∈ PB)
    (edgeSign : StarEdge A B r ell → ℤˣ) (c : ℤˣ)
    (hstar :
      c * (∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e) =
        ∏ e ∈ A.starGluedMatching B r ell QA PB i, edgeSign e) :
    c * (∏ e ∈ PA, edgeSign (A.starAEdge B r ell p e)) =
      ∏ e ∈ QA, edgeSign (A.starAEdge B r ell p e) := by
  classical
  let commonB := ∏ e ∈ PB, edgeSign (A.starBEdge B r ell q σ e)
  have hprodP := starGluedMatching_prod_mul_bridge
    A B r ell p q σ PA PB i hPA hPB hPi hBi edgeSign
  have hprodQ := starGluedMatching_prod_mul_bridge
    A B r ell p q σ QA PB i hQA hPB hQi hBi edgeSign
  apply mul_right_cancel (b := commonB)
  calc
    (c * (∏ e ∈ PA, edgeSign (A.starAEdge B r ell p e))) * commonB =
        c * ((∏ e ∈ PA, edgeSign (A.starAEdge B r ell p e)) * commonB) := by
          simp [mul_assoc]
    _ = c * ((∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e) *
          edgeSign (Sum.inr (Sum.inr i))) := by
          rw [hprodP]
    _ = (c * (∏ e ∈ A.starGluedMatching B r ell PA PB i, edgeSign e)) *
          edgeSign (Sum.inr (Sum.inr i)) := by
          simp [mul_assoc]
    _ = (∏ e ∈ A.starGluedMatching B r ell QA PB i, edgeSign e) *
          edgeSign (Sum.inr (Sum.inr i)) := by rw [hstar]
    _ = (∏ e ∈ QA, edgeSign (A.starAEdge B r ell p e)) * commonB := hprodQ

end BipartiteMultigraph
end BachThesisLean
