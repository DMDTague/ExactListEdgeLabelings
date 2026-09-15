import BachThesisLean

/-!
# BachThesisLean entry point

This file is intentionally small. The library files contain the definitions
and proved foundational lemmas; unresolved research statements are recorded
as propositions in `BachThesisLean.Conjectures.Status` rather than asserted
with `sorry` or axioms.
-/

namespace BachThesisLean

example {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) (x : X) (e : E) :
    e ∈ G.leftIncident x ↔ G.left e = x := by
  simp [BipartiteMultigraph.leftIncident]

end BachThesisLean
