import BachThesisLean.Cubic.Foundations

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]
variable {G : BipartiteMultigraph X Y E}

/-!
# Perfect matchings as shore equivalences

A perfect matching selects one actual edge copy at every left vertex and at
every right vertex.  Choosing the selected copy at each left vertex therefore
produces a bijection from the left shore to the right shore.  This is the
edge-copy-safe bridge needed for determinant/Pfaffian signs: relative to any
fixed reference equivalence between the shores, a perfect matching becomes a
permutation.
-/

/-- The unique matching edge selected at a left vertex. -/
noncomputable def IsPerfectMatching.matchingEdge
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) : E :=
  Classical.choose (hP.existsUnique_incident (.inl x))

/-- The chosen left matching edge belongs to the matching and has the
prescribed left endpoint. -/
theorem IsPerfectMatching.matchingEdge_spec
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) :
    hP.matchingEdge x ∈ P ∧ G.left (hP.matchingEdge x) = x := by
  have hs := (Classical.choose_spec (hP.existsUnique_incident (.inl x))).1
  exact ⟨hs.1, hs.2⟩

@[simp] theorem IsPerfectMatching.matchingEdge_mem
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) :
    hP.matchingEdge x ∈ P :=
  (hP.matchingEdge_spec x).1

@[simp] theorem IsPerfectMatching.matchingEdge_left
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) :
    G.left (hP.matchingEdge x) = x :=
  (hP.matchingEdge_spec x).2

/-- Any selected copy incident with `x` is the chosen matching copy at `x`. -/
theorem IsPerfectMatching.matchingEdge_eq_of_mem_left
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) {e : E}
    (heP : e ∈ P) (heLeft : G.left e = x) :
    hP.matchingEdge x = e := by
  let hu := hP.existsUnique_incident (.inl x)
  have heChosen : hP.matchingEdge x ∈ P ∧
      G.Incident (hP.matchingEdge x) (.inl x) := by
    exact (Classical.choose_spec hu).1
  have he : e ∈ P ∧ G.Incident e (.inl x) := ⟨heP, heLeft⟩
  exact ((Classical.choose_spec hu).2 e he).symm

/-- Right endpoint selected by the perfect matching at a left vertex. -/
noncomputable def IsPerfectMatching.matchingRight
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) : Y :=
  G.right (hP.matchingEdge x)

/-- Distinct left vertices are sent to distinct right vertices. -/
theorem IsPerfectMatching.matchingRight_injective
    {P : Finset E} (hP : G.IsPerfectMatching P) :
    Function.Injective hP.matchingRight := by
  intro x x' hright
  let e := hP.matchingEdge x
  let f := hP.matchingEdge x'
  have heP : e ∈ P := by simpa [e] using hP.matchingEdge_mem x
  have hfP : f ∈ P := by simpa [f] using hP.matchingEdge_mem x'
  have heInc : G.Incident e (.inr (G.right e)) := rfl
  have hfInc : G.Incident f (.inr (G.right e)) := by
    change G.right f = G.right e
    simpa [IsPerfectMatching.matchingRight, e, f] using hright.symm
  have hef : e = f :=
    (G.isMatching_iff P).1 hP.isMatching e heP f hfP
      (.inr (G.right e)) heInc hfInc
  calc
    x = G.left e := by simpa [e] using (hP.matchingEdge_left x).symm
    _ = G.left f := congrArg G.left hef
    _ = x' := by simpa [f] using hP.matchingEdge_left x'

/-- Every right vertex is the matched partner of some left vertex. -/
theorem IsPerfectMatching.matchingRight_surjective
    {P : Finset E} (hP : G.IsPerfectMatching P) :
    Function.Surjective hP.matchingRight := by
  intro y
  obtain ⟨e, ⟨heP, heRight⟩, _hunique⟩ :=
    hP.existsUnique_incident (.inr y)
  let x : X := G.left e
  refine ⟨x, ?_⟩
  have heq : hP.matchingEdge x = e := by
    exact hP.matchingEdge_eq_of_mem_left x heP rfl
  change G.right (hP.matchingEdge x) = y
  rw [heq]
  exact heRight

/-- A perfect matching canonically (up to the harmless choice of its unique
incident copy) gives an equivalence between the two shores. -/
noncomputable def IsPerfectMatching.shoreEquiv
    {P : Finset E} (hP : G.IsPerfectMatching P) : X ≃ Y :=
  Equiv.ofBijective hP.matchingRight
    ⟨hP.matchingRight_injective, hP.matchingRight_surjective⟩

@[simp] theorem IsPerfectMatching.shoreEquiv_apply
    {P : Finset E} (hP : G.IsPerfectMatching P) (x : X) :
    hP.shoreEquiv x = hP.matchingRight x := rfl

/-- Subtype-facing form used by the Pfaffian layer. -/
noncomputable def PerfectMatching.shoreEquiv (P : G.PerfectMatching) : X ≃ Y :=
  P.property.shoreEquiv

@[simp] theorem PerfectMatching.shoreEquiv_apply
    (P : G.PerfectMatching) (x : X) :
    P.shoreEquiv x = P.property.matchingRight x := rfl

end BipartiteMultigraph
end BachThesisLean
