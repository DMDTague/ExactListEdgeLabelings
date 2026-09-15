import BachThesisLean.Cubic.HeawoodCore

namespace BachThesisLean
namespace BipartiteMultigraph

private instance decidableForallFintypeTwoHeawood23
    {α β : Type*} [Fintype α] [Fintype β]
    {p : α → β → Prop} [∀ a b, Decidable (p a b)] :
    Decidable (∀ a b, p a b) := by
  letI : DecidablePred (fun a : α => ∀ b : β, p a b) := fun a => by
    letI : DecidablePred (p a) := fun b => inferInstance
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem heawood_chosenMatching_works_left2 :
    ∀ s : Fin 3, ∀ f : HeawoodEdge, (2, s) ≠ f →
      HeawoodMatchingWorks (heawoodChosenMatchingIndex (2, s) f) (2, s) f := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem heawood_chosenMatching_works_left3 :
    ∀ s : Fin 3, ∀ f : HeawoodEdge, (3, s) ≠ f →
      HeawoodMatchingWorks (heawoodChosenMatchingIndex (3, s) f) (3, s) f := by
  decide

end BipartiteMultigraph
end BachThesisLean
