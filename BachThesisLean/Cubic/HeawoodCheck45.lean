import BachThesisLean.Cubic.HeawoodCore

namespace BachThesisLean
namespace BipartiteMultigraph

private instance decidableForallFintypeTwoHeawood45
    {α β : Type*} [Fintype α] [Fintype β]
    {p : α → β → Prop} [∀ a b, Decidable (p a b)] :
    Decidable (∀ a b, p a b) := by
  letI : DecidablePred (fun a : α => ∀ b : β, p a b) := fun a => by
    letI : DecidablePred (p a) := fun b => inferInstance
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem heawood_chosenMatching_works_left4 :
    ∀ s : Fin 3, ∀ f : HeawoodEdge, (4, s) ≠ f →
      HeawoodMatchingWorks (heawoodChosenMatchingIndex (4, s) f) (4, s) f := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem heawood_chosenMatching_works_left5 :
    ∀ s : Fin 3, ∀ f : HeawoodEdge, (5, s) ≠ f →
      HeawoodMatchingWorks (heawoodChosenMatchingIndex (5, s) f) (5, s) f := by
  decide

end BipartiteMultigraph
end BachThesisLean
