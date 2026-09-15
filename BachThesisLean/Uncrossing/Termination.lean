import BachThesisLean.Uncrossing.Support
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Relation

namespace BachThesisLean

universe u v w z

variable {X : Type u} {Λ : Type z}
variable [Fintype X] [Fintype Λ] [DecidableEq X] [DecidableEq Λ]

/-- One legal strict-potential uncrossing, with both indexed slots retained. -/
def UncrossStep (S T : SupportFamily X Λ) : Prop :=
  ∃ a b, IsIncomparable (S a) (S b) ∧ T = uncross S a b

/-- Supports are nested without choosing an ordering of the label type. -/
def IsNested (S : SupportFamily X Λ) : Prop :=
  ∀ a b, S a ⊆ S b ∨ S b ⊆ S a

/-- A finite sequence of uncrossings preserves the exact incidence constraints. -/
theorem exactSupportIncidence_reachable
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) {S T : SupportFamily X Λ}
    (hS : ExactSupportIncidence G S)
    (hST : Relation.ReflTransGen UncrossStep S T) :
    ExactSupportIncidence G T := by
  induction hST with
  | refl => exact hS
  | @tail T U _ hstep ih =>
    obtain ⟨a, b, hab, rfl⟩ := hstep
    have hne : a ≠ b := by
      intro h
      subst b
      exact hab.1 (Finset.Subset.refl _)
    exact exactSupportIncidence_uncross G T a b hne ih

/-- Finite termination in existence form: a reachable potential maximizer
cannot contain an incomparable pair. This does not assume count monotonicity. -/
theorem exists_nested_uncrossing (S : SupportFamily X Λ) :
    ∃ T, Relation.ReflTransGen UncrossStep S T ∧ IsNested T := by
  classical
  let reachable : Finset (SupportFamily X Λ) :=
    Finset.univ.filter (Relation.ReflTransGen UncrossStep S)
  have hnonempty : reachable.Nonempty := by
    refine ⟨S, ?_⟩
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image reachable supportPotential hnonempty
  have hST : Relation.ReflTransGen UncrossStep S T :=
    (Finset.mem_filter.mp hT).2
  refine ⟨T, hST, ?_⟩
  intro a b
  by_contra h
  have hab : IsIncomparable (T a) (T b) := not_or.mp h
  have hnext : uncross T a b ∈ reachable := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hST.tail ⟨a, b, hab, rfl⟩⟩
  exact (not_lt_of_ge (hmax _ hnext)) (supportPotential_uncross_gt T hab)

/-- The terminal family is an exact-list system on the original graph. -/
theorem exists_nested_exact_uncrossing
    {Y : Type v} {E : Type w} [Fintype Y] [Fintype E]
    (G : BipartiteMultigraph X Y E) (S : SupportFamily X Λ)
    (hS : ExactSupportIncidence G S) :
    ∃ T, Relation.ReflTransGen UncrossStep S T ∧
      ExactSupportIncidence G T ∧ IsNested T := by
  obtain ⟨T, hST, hnested⟩ := exists_nested_uncrossing S
  exact ⟨T, hST, exactSupportIncidence_reachable G hS hST, hnested⟩

end BachThesisLean
