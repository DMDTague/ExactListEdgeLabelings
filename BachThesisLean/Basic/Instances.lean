import BachThesisLean.Basic.Counting
import BachThesisLean.Uncrossing.Support
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace BachThesisLean

open BipartiteMultigraph

/-!
# Decidable regression instances

The foundational definitions retain classical wrappers so that they can be
used with arbitrary finite types.  For small concrete examples we expose the
same incidence and admissibility calculation with explicit decidability
instances.  This makes the `K22` regression a genuine `decide` check rather
than a stored numerical assertion.
-/

def leftIncidentDecidable
    {X : Type*} {Y : Type*} {E : Type*}
    [Fintype E] [DecidableEq X]
    (G : BipartiteMultigraph X Y E) (x : X) : Finset E :=
  Finset.univ.filter (fun e => G.left e = x)

def rightIncidentDecidable
    {X : Type*} {Y : Type*} {E : Type*}
    [Fintype E] [DecidableEq Y]
    (G : BipartiteMultigraph X Y E) (y : Y) : Finset E :=
  Finset.univ.filter (fun e => G.right e = y)

def labelsUsedAtLeftDecidable
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype E] [DecidableEq X] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (x : X) : Finset Λ :=
  (leftIncidentDecidable G x).image σ

def labelsUsedAtRightDecidable
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype E] [DecidableEq Y] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (y : Y) : Finset Λ :=
  (rightIncidentDecidable G y).image σ

def IsAdmissibleDecidable
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (labels : X → Finset Λ)
    (σ : E → Λ) : Prop :=
  (∀ x, labelsUsedAtLeftDecidable G σ x = labels x) ∧
  (∀ y,
    (rightIncidentDecidable G y).card =
      (labelsUsedAtRightDecidable G σ y).card)

def admissibleDecision
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (labels : X → Finset Λ)
    (σ : E → Λ) : Decidable (IsAdmissibleDecidable G labels σ) := by
  unfold IsAdmissibleDecidable
  letI : DecidablePred
      (fun x : X => labelsUsedAtLeftDecidable G σ x = labels x) :=
    fun x => inferInstance
  letI : DecidablePred
      (fun y : Y =>
        (rightIncidentDecidable G y).card =
          (labelsUsedAtRightDecidable G σ y).card) :=
    fun y => inferInstance
  exact inferInstance

@[simp] theorem leftIncidentDecidable_eq
    {X : Type*} {Y : Type*} {E : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X]
    (G : BipartiteMultigraph X Y E) (x : X) :
    leftIncidentDecidable G x = G.leftIncident x := by
  classical
  ext e
  simp [leftIncidentDecidable]

@[simp] theorem rightIncidentDecidable_eq
    {X : Type*} {Y : Type*} {E : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [DecidableEq Y]
    (G : BipartiteMultigraph X Y E) (y : Y) :
    rightIncidentDecidable G y = G.rightIncident y := by
  classical
  ext e
  simp [rightIncidentDecidable]

@[simp] theorem labelsUsedAtLeftDecidable_eq
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [DecidableEq X] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (x : X) :
    labelsUsedAtLeftDecidable G σ x = ExactLeftLists.labelsUsedAtLeft G σ x := by
  classical
  ext c
  simp [labelsUsedAtLeftDecidable, ExactLeftLists.labelsUsedAtLeft]

@[simp] theorem labelsUsedAtRightDecidable_eq
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [DecidableEq Y] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (σ : E → Λ) (y : Y) :
    labelsUsedAtRightDecidable G σ y = ExactLeftLists.labelsUsedAtRight G σ y := by
  classical
  ext c
  simp [labelsUsedAtRightDecidable, ExactLeftLists.labelsUsedAtRight]

theorem isAdmissibleDecidable_iff
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ) (σ : E → Λ) :
    IsAdmissibleDecidable G L.labels σ ↔ L.IsAdmissible σ := by
  simp [IsAdmissibleDecidable, ExactLeftLists.IsAdmissible]

/-- A computable decision procedure for the foundational predicate itself. -/
instance decidableIsAdmissible
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ) (σ : E → Λ) :
    Decidable (L.IsAdmissible σ) := by
  letI := admissibleDecision G L.labels σ
  exact decidable_of_iff (IsAdmissibleDecidable G L.labels σ)
    (isAdmissibleDecidable_iff L σ)

def admissibleLabelingsDecidable
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [Fintype (E → Λ)] [DecidableEq E]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (labels : X → Finset Λ) : Finset (E → Λ) :=
  letI : DecidablePred
      (fun σ : E → Λ => IsAdmissibleDecidable G labels σ) :=
    fun σ => admissibleDecision G labels σ
  Finset.univ.filter (fun σ : E → Λ => IsAdmissibleDecidable G labels σ)

def computableCount
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [Fintype (E → Λ)] [DecidableEq E]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    (G : BipartiteMultigraph X Y E) (labels : X → Finset Λ) : ℕ :=
  (admissibleLabelingsDecidable G labels).card

theorem admissibleLabelingsDecidable_eq
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [Fintype (E → Λ)] [DecidableEq E]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ) :
    admissibleLabelingsDecidable G L.labels = L.admissibleLabelings := by
  classical
  ext σ
  simp [admissibleLabelingsDecidable, ExactLeftLists.mem_admissibleLabelings,
    isAdmissibleDecidable_iff]

theorem computableCount_eq_count
    {X : Type*} {Y : Type*} {E : Type*} {Λ : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ]
    [Fintype (E → Λ)] [DecidableEq E]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Λ]
    {G : BipartiteMultigraph X Y E} (L : ExactLeftLists G Λ) :
    computableCount G L.labels = L.count := by
  rw [computableCount, admissibleLabelingsDecidable_eq]
  rfl

def K22 : BipartiteMultigraph (Fin 2) (Fin 2) (Fin 4) where
  left := ![0, 0, 1, 1]
  right := ![0, 1, 0, 1]

def someExactLists (x : Fin 2) : Finset (Fin 4) :=
  if x = 0 then {0, 1} else {2, 3}

def uncrossedLists (x : Fin 2) : Finset (Fin 4) :=
  if x = 0 then {0, 1} else {1, 3}

theorem k22_disjoint_exact : ∀ x, (someExactLists x).card =
    (leftIncidentDecidable K22 x).card := by decide

theorem k22_commonCore_exact : ∀ x, (uncrossedLists x).card =
    (leftIncidentDecidable K22 x).card := by decide

theorem k22_disjoint_enumeration :
    admissibleLabelingsDecidable K22 someExactLists =
      {![0, 1, 2, 3], ![0, 1, 3, 2], ![1, 0, 2, 3], ![1, 0, 3, 2]} := by decide

theorem k22_commonCore_enumeration :
    admissibleLabelingsDecidable K22 uncrossedLists =
      {![0, 1, 1, 3], ![1, 0, 3, 1]} := by decide

def k22UniformLists (_ : Fin 2) : Finset (Fin 4) := {0, 1}

theorem k22_uniform_exact : ∀ x, (k22UniformLists x).card =
    (leftIncidentDecidable K22 x).card := by decide

theorem k22_uniform_enumeration :
    admissibleLabelingsDecidable K22 k22UniformLists =
      {![0, 1, 1, 0], ![1, 0, 0, 1]} := by decide

def k22Disjoint : ExactLeftLists K22 (Fin 4) where
  labels := someExactLists
  card_labels := by simpa [leftDegree] using k22_disjoint_exact

def k22CommonCore : ExactLeftLists K22 (Fin 4) where
  labels := uncrossedLists
  card_labels := by simpa [leftDegree] using k22_commonCore_exact

def k22Uniform : ExactLeftLists K22 (Fin 4) where
  labels := k22UniformLists
  card_labels := by simpa [leftDegree] using k22_uniform_exact

theorem k22_disjoint_count : k22Disjoint.count = 4 := by
  rw [← computableCount_eq_count, computableCount]
  change (admissibleLabelingsDecidable K22 someExactLists).card = 4
  rw [k22_disjoint_enumeration]
  decide

theorem k22_commonCore_count : k22CommonCore.count = 2 := by
  rw [← computableCount_eq_count, computableCount]
  change (admissibleLabelingsDecidable K22 uncrossedLists).card = 2
  rw [k22_commonCore_enumeration]
  decide

theorem k22_uniform_count : k22Uniform.count = 2 := by
  rw [← computableCount_eq_count, computableCount]
  change (admissibleLabelingsDecidable K22 k22UniformLists).card = 2
  rw [k22_uniform_enumeration]
  decide

theorem k22_left_regular : K22.IsLeftRegular 2 := by
  have h : ∀ x, (leftIncidentDecidable K22 x).card = 2 := by decide
  simpa [IsLeftRegular, leftDegree] using h

theorem k22_right_regular : K22.IsRightRegular 2 := by
  have h : ∀ y, (rightIncidentDecidable K22 y).card = 2 := by decide
  simpa [IsRightRegular, rightDegree] using h

theorem k22_ordinary_count : ExactLeftLists.ordinaryCount K22 2 k22_left_regular = 2 := by
  unfold ExactLeftLists.ordinaryCount
  rw [← computableCount_eq_count]
  decide

/-- The manuscript's nonidentical-list equality example, with its ordinary
count computed independently over the fixed two-element palette. -/
theorem k22_commonCore_attains_ordinary :
    k22CommonCore.count = ExactLeftLists.ordinaryCount K22 2 k22_left_regular := by
  rw [k22_commonCore_count, k22_ordinary_count]

/-- The original regression really is one support uncrossing, at slots 1 and 2. -/
theorem k22_first_uncross :
    uncross (supportFamilyOfLists k22Disjoint) 1 2 =
      supportFamilyOfLists k22CommonCore := by
  funext c
  ext x
  fin_cases c <;> fin_cases x <;>
    simp [uncross, supportFamilyOfLists, supportOfLists,
      k22Disjoint, k22CommonCore, someExactLists, uncrossedLists]

/-- A second uncrossing yields two full supports and two retained empty slots. -/
theorem k22_second_uncross :
    uncross (supportFamilyOfLists k22CommonCore) 0 3 =
      supportFamilyOfLists k22Uniform := by
  funext c
  ext x
  fin_cases c <;> fin_cases x <;>
    simp [uncross, supportFamilyOfLists, supportOfLists,
      k22CommonCore, k22Uniform, uncrossedLists, k22UniformLists]

theorem k22_uniform_supports (c : Fin 4) :
    supportFamilyOfLists k22Uniform c =
      if c = 0 ∨ c = 1 then Finset.univ else ∅ := by
  ext x
  fin_cases c <;> fin_cases x <;>
    simp [supportFamilyOfLists, supportOfLists, k22Uniform, k22UniformLists]

theorem k22_first_uncross_strict : k22CommonCore.count < k22Disjoint.count := by
  rw [k22_commonCore_count, k22_disjoint_count]
  decide

theorem k22_second_uncross_equality : k22Uniform.count = k22CommonCore.count := by
  rw [k22_uniform_count, k22_commonCore_count]

theorem k22_commonCore_lists_distinct : k22CommonCore.labels 0 ≠ k22CommonCore.labels 1 := by
  decide

/-- A direct regression of the decision procedure for the original predicate. -/
example : k22CommonCore.IsAdmissible ![0, 1, 1, 3] := by decide

example : ¬ k22CommonCore.IsAdmissible ![1, 0, 1, 3] := by decide

end BachThesisLean
