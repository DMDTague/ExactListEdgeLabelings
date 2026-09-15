import BachThesisLean.Cubic.Foundations
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Finite certificates for cubic edge-copy conventions

All finite enumerations below use kernel evaluation by `decide`. The examples
retain parallel copies and test incidence, complementary factors, and ports.
-/

namespace BachThesisLean
namespace CubicRegression

open BipartiteMultigraph

/-- Two vertices joined by three distinct edge copies. -/
def tripleParallel : BipartiteMultigraph (Fin 1) (Fin 1) (Fin 3) where
  left := fun _ => 0
  right := fun _ => 0

theorem tripleParallel_cubic : tripleParallel.IsCubic := by decide

theorem tripleParallel_perfectMatchings :
    Finset.univ.filter tripleParallel.IsPerfectMatching =
      ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) := by decide

theorem tripleParallel_twoFactors :
    Finset.univ.filter tripleParallel.IsTwoFactor =
      ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by decide

theorem tripleParallel_matching_count : Fintype.card tripleParallel.PerfectMatching = 3 := by
  decide

theorem tripleParallel_twoFactor_count : Fintype.card tripleParallel.TwoFactor = 3 := by
  rw [← tripleParallel.card_perfectMatching_eq_card_twoFactor tripleParallel_cubic]
  exact tripleParallel_matching_count

theorem tripleParallel_parallelPair_not_matching :
    ¬ tripleParallel.IsMatching {1, 2} := by decide

/-- The two remaining parallel edges form one component of a spanning two-factor. -/
theorem tripleParallel_complement_component :
    tripleParallel.IsTwoFactor {1, 2} ∧
      tripleParallel.ComponentCarries {1, 2} (.inl 0) 1 ∧
      tripleParallel.ComponentCarries {1, 2} (.inl 0) 2 ∧
      tripleParallel.FactorReachable {1, 2} (.inl 0) (.inr 0) := by
  refine ⟨by decide, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩, ?_⟩
  · exact tripleParallel.factorReachable_refl _ _
  · exact tripleParallel.factorReachable_refl _ _
  · exact tripleParallel.factorReachable_endpoints (e := 1) (by decide)

/-- An omitted matching edge is not carried even though its endpoints remain connected. -/
theorem tripleParallel_selected_edge_guard :
    ¬ tripleParallel.ComponentCarries ({0} : Finset (Fin 3))ᶜ (.inl 0) 0 := by
  exact tripleParallel.not_componentCarries_of_mem_matching {0} (.inl 0) (by decide)

theorem tripleParallel_hasEEP : tripleParallel.HasEEP := by
  intro e f hef
  have hfactor : tripleParallel.IsTwoFactor {e, f} := by
    fin_cases e <;> fin_cases f <;> first | contradiction | decide
  refine ⟨{e, f}ᶜ, .inl 0, ?_, ?_, ?_⟩
  · exact (tripleParallel.perfectMatching_compl_iff_twoFactor
      tripleParallel_cubic {e, f}ᶜ).2 (by simpa using hfactor)
  · exact ⟨by simp, tripleParallel.factorReachable_refl _ _⟩
  · exact ⟨by simp, tripleParallel.factorReachable_refl _ _⟩

theorem tripleParallel_hasEVP : tripleParallel.HasEVP :=
  tripleParallel_hasEEP.hasEVP tripleParallel_cubic

theorem tripleParallel_hasTwoEP : tripleParallel.HasTwoEP :=
  (tripleParallel.hasEEP_iff_hasTwoEP tripleParallel_cubic).1 tripleParallel_hasEEP

theorem tripleParallel_singleton_cut :
    tripleParallel.edgeCut ({.inl 0} : Finset (Fin 1 ⊕ Fin 1)) = Finset.univ := by
  decide

/-- The six-edge, four-vertex graph in Lemma `lem:four-vertex-amplifier`. -/
def amplifier : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 6) where
  left := ![0, 0, 0, 1, 1, 1]
  right := ![0, 0, 1, 0, 1, 1]

/-- Edge multiplicities agree with the manuscript matrix, including both double edges. -/
theorem amplifier_multiplicity_matrix :
    ∀ x y : Fin 2,
      (Finset.univ.filter (fun e : Fin 6 => amplifier.left e = x ∧
        amplifier.right e = y)).card = (![![2, 1], ![1, 2]] : Matrix (Fin 2) (Fin 2) ℕ) x y := by
  decide

theorem amplifier_cubic : amplifier.IsCubic := by decide

theorem amplifier_perfectMatchings :
    Finset.univ.filter amplifier.IsPerfectMatching =
      ({{0, 4}, {0, 5}, {1, 4}, {1, 5}, {2, 3}} : Finset (Finset (Fin 6))) := by decide

theorem amplifier_matching_count : Fintype.card amplifier.PerfectMatching = 5 := by decide

theorem amplifier_twoFactor_count : Fintype.card amplifier.TwoFactor = 5 := by
  rw [← amplifier.card_perfectMatching_eq_card_twoFactor amplifier_cubic]
  exact amplifier_matching_count

/-- The parallel ports are edge copies 0 and 1; the third port is edge copy 2. -/
def amplifierPorts : amplifier.PortEnumeration (.inl 0) where
  toFun i := ⟨i.castLE (by decide), by
    fin_cases i <;> decide⟩
  invFun := fun ⟨e, he⟩ => ⟨e.val, by
    fin_cases e <;> simp_all [incidentEdges, selectedIncident, Incident, amplifier]⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv e := by apply Subtype.ext; apply Fin.ext; rfl

theorem amplifierPorts_values :
    ∀ i : Fin 3, (amplifierPorts i).val = (![0, 1, 2] : Fin 3 → Fin 6) i := by decide

theorem amplifier_ports_same_neighbour :
    (amplifierPorts 0).val ≠ (amplifierPorts 1).val ∧
      amplifier.right (amplifierPorts 0).val = amplifier.right (amplifierPorts 1).val := by decide

theorem amplifier_parallel_complement :
    ({2, 3} : Finset (Fin 6))ᶜ = {0, 1, 4, 5} := by decide

theorem amplifier_third_port_matching :
    ∀ P : Finset (Fin 6), amplifier.IsPerfectMatching P → 2 ∈ P → P = {2, 3} := by
  decide

theorem amplifier_first_port_connects :
    amplifier.FactorReachable ({0, 4} : Finset (Fin 6))ᶜ (.inl 0) (.inl 1) := by
  exact (amplifier.factorReachable_endpoints (e := 2) (by decide)).trans
    (amplifier.factorReachable_endpoints (e := 5) (by decide)).symm

theorem amplifier_second_port_connects :
    amplifier.FactorReachable ({1, 4} : Finset (Fin 6))ᶜ (.inl 0) (.inl 1) := by
  exact (amplifier.factorReachable_endpoints (e := 2) (by decide)).trans
    (amplifier.factorReachable_endpoints (e := 5) (by decide)).symm

/-- The third port leaves two disjoint parallel-edge components. -/
theorem amplifier_third_port_separates :
    ¬ amplifier.FactorReachable ({2, 3} : Finset (Fin 6))ᶜ (.inl 0) (.inl 1) := by
  intro h
  have hi : ∀ e ∈ ({2, 3} : Finset (Fin 6))ᶜ,
      amplifier.left e = amplifier.right e := by decide
  have h01 : (0 : Fin 2) = 1 := h.map_eq (Sum.elim id id) (by
    rintro a b ⟨e, he, hab | hab⟩
    · rcases hab with ⟨rfl, rfl⟩
      exact hi e he
    · rcases hab with ⟨rfl, rfl⟩
      exact (hi e he).symm)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- The exact two-port mask in the finite part of `lem:four-vertex-amplifier`.
The manuscript's ports 1,2,3 correspond to Lean indices 0,1,2. -/
theorem amplifier_vertexRootMask :
    amplifier.vertexRootMask (.inl 0) amplifierPorts (.inl 1) = {0, 1} := by
  ext i
  fin_cases i
  · constructor
    · intro _; decide
    · intro _
      apply (amplifier.mem_vertexRootMask (.inl 0) amplifierPorts (.inl 1) 0).2
      exact ⟨{0, 4}, by decide, by decide, amplifier_first_port_connects⟩
  · constructor
    · intro _; decide
    · intro _
      apply (amplifier.mem_vertexRootMask (.inl 0) amplifierPorts (.inl 1) 1).2
      exact ⟨{1, 4}, by decide, by decide, amplifier_second_port_connects⟩
  · constructor
    · intro h
      obtain ⟨P, hP, hport, hreach⟩ :=
        (amplifier.mem_vertexRootMask (.inl 0) amplifierPorts (.inl 1) 2).1 h
      have he : (2 : Fin 6) ∈ P := hport
      rw [amplifier_third_port_matching P hP he] at hreach
      exact False.elim (amplifier_third_port_separates hreach)
    · intro h
      simp at h

end CubicRegression
end BachThesisLean
