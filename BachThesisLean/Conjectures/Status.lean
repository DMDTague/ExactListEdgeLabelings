import BachThesisLean.Basic.ExactLists

namespace BachThesisLean

open BipartiteMultigraph
open ExactLeftLists

/-!
## Research-status propositions

These are intentionally definitions of propositions rather than axioms. They
make it possible for later files to state reductions without silently turning
an open research problem into an available theorem. A proposition target may
remain here after it is proved so downstream statements can use a stable name;
its proof status is recorded separately below.
-/

def ExactListLowerBound : Prop :=
  ∀ {X Y E Λ : Type*} [Fintype X] [Fintype Y] [Fintype E] [Fintype Λ],
    ∀ (G : BipartiteMultigraph X Y E) (k : ℕ)
      (h : G.IsLeftRegular k) (L : ExactLeftLists G Λ),
      ExactLeftLists.count L ≥ ExactLeftLists.ordinaryCount G k h

/-!
The remaining research targets are recorded as names and status entries until
their graph-theoretic definitions have been implemented. They are not
declared as propositions with placeholder proofs, and no axiom is introduced
for any of them.
-/

/-!
`FormalizationStatus` is a human-readable classification used by the
repository documentation. It is not part of the mathematical theory.
-/

inductive FormalizationStatus
  | machineChecked
  | manuscriptProof
  | finiteEvidence
  | openProblem
  | refutedOrIncomplete
deriving DecidableEq, Repr

structure ClaimStatus where
  name : String
  status : FormalizationStatus
  note : String
deriving Repr

def auditedClaimStatuses : List ClaimStatus := [
  { name := "Exact-list lower bound"
    status := .machineChecked
    note := "Proved by exactListLowerBound_machineChecked from the explicit local/global uncrossing injection, termination, nested regular normal form, and common-palette equivalence." },
  { name := "Degree-sequence nested minimizer"
    status := .machineChecked
    note := "Proved by nested_minimizer after canonical label sorting, support normal form, and deletion of forced empty prefix labels." },
  { name := "Common-core equality converse"
    status := .openProblem
    note := "Reduced to TF_k; not imported as an axiom." },
  { name := "Universal cubic TF3"
    status := .openProblem
    note := "No valid global disproof or proof certificate in the archive." },
  { name := "Explicit graph statistic"
    status := .finiteEvidence
    note := "Independent check gives 8/12 = 2/3, not 1/17." },
  { name := "Proposed TF3 disproof"
    status := .refutedOrIncomplete
    note := "No validated graph-and-certificate witness supplied." }
]

end BachThesisLean
