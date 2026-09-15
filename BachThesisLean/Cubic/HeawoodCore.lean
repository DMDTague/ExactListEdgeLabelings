import BachThesisLean.Cubic.FourVertexCube
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.Pi

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# Heawood base-case data

This file contains the explicit Heawood graph, its eight certificate matchings,
and the computable predicate used by the finite base-case verification.  The
expensive closed verification is split across `HeawoodCheck*` modules so each
piece can be compiled and cached independently.
-/

/-- The three Fano-line incidences at each of the seven left vertices. -/
def heawoodRight : Fin 7 → Fin 3 → Fin 7 :=
  ![![0, 1, 3],
    ![1, 2, 4],
    ![2, 3, 5],
    ![3, 4, 6],
    ![4, 5, 0],
    ![5, 6, 1],
    ![6, 0, 2]]

abbrev HeawoodEdge := Fin 7 × Fin 3

/-- Standard bipartite incidence model of the Heawood graph. -/
def heawoodGraph : BipartiteMultigraph (Fin 7) (Fin 7) HeawoodEdge where
  left e := e.1
  right e := heawoodRight e.1 e.2

@[simp] theorem heawoodGraph_left (e : HeawoodEdge) :
    heawoodGraph.left e = e.1 := rfl

@[simp] theorem heawoodGraph_right (e : HeawoodEdge) :
    heawoodGraph.right e = heawoodRight e.1 e.2 := rfl

/-- Eight perfect matchings sufficient for all prescribed edge-pair
certificates.  The first three are the three constant slot choices. -/
def heawoodCertificateMatchingSlots : Fin 8 → Fin 7 → Fin 3 :=
  ![![0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1],
    ![2, 2, 2, 2, 2, 2, 2],
    ![0, 0, 1, 1, 1, 1, 2],
    ![1, 2, 0, 0, 2, 0, 0],
    ![2, 1, 2, 2, 0, 2, 1],
    ![0, 1, 1, 1, 1, 2, 0],
    ![2, 0, 0, 2, 0, 0, 1]]

/-- The indexed seven-edge perfect matching. -/
def heawoodCertificateMatching (k : Fin 8) : Finset HeawoodEdge :=
  {(0, heawoodCertificateMatchingSlots k 0),
    (1, heawoodCertificateMatchingSlots k 1),
    (2, heawoodCertificateMatchingSlots k 2),
    (3, heawoodCertificateMatchingSlots k 3),
    (4, heawoodCertificateMatchingSlots k 4),
    (5, heawoodCertificateMatchingSlots k 5),
    (6, heawoodCertificateMatchingSlots k 6)}

/-- Every listed certificate row is a genuine perfect matching. -/
theorem heawoodCertificateMatching_isPerfectMatching (k : Fin 8) :
    heawoodGraph.IsPerfectMatching (heawoodCertificateMatching k) := by
  fin_cases k <;> decide

/-- Finite condition sufficient for the generic four-edge bridge certificate. -/
def HeawoodMatchingWorks (k : Fin 8) (e f : HeawoodEdge) : Prop :=
  let P := heawoodCertificateMatching k
  e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 7, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        heawoodRight e.1 s0 = heawoodRight x s1 ∧
        heawoodRight x s2 = heawoodRight f.1 s3)

instance (k : Fin 8) (e f : HeawoodEdge) :
    Decidable (HeawoodMatchingWorks k e f) := by
  unfold HeawoodMatchingWorks
  infer_instance

/-- Deterministically choose the first of the eight certificate matchings that
supplies the bounded complementary bridge. -/
def heawoodChosenMatchingIndex (e f : HeawoodEdge) : Fin 8 :=
  if HeawoodMatchingWorks 0 e f then 0
  else if HeawoodMatchingWorks 1 e f then 1
  else if HeawoodMatchingWorks 2 e f then 2
  else if HeawoodMatchingWorks 3 e f then 3
  else if HeawoodMatchingWorks 4 e f then 4
  else if HeawoodMatchingWorks 5 e f then 5
  else if HeawoodMatchingWorks 6 e f then 6
  else 7

end BipartiteMultigraph
end BachThesisLean
