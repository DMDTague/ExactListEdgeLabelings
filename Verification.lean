import BachThesisLean
import Lean.Util.CollectAxioms

/-!
Audit the transitive axioms of the public theorem and definition layer after
elaboration. Only Lean's standard logical axioms are permitted.

Source-level `axiom`, `opaque`, placeholder, and trust-bypass declarations are
rejected separately by `scripts/check_formalization.py`. The elaborated
environment also contains compiler/elaborator-generated implementation details
(`_closed`, `_proof`, `match_N`, equation helpers, and similar names). Lean marks
these with `Name.isInternalDetail`; they are not independent source declarations
and may themselves reference code-generation helper constants represented as
`axiomInfo`.

Accordingly this kernel check audits every non-internal `BachThesisLean`
theorem, definition/abbreviation, and opaque definition. `collectAxioms` is
transitive, so a forbidden axiom hidden behind any generated helper that is
actually reachable from a source-visible declaration is still rejected.

Two non-vacuity guards are maintained. The complete elaborated namespace must
still contain at least 2000 theorem constants, preserving the original
anti-truncation guard. Independently, at least 1200 non-internal theorem
constants must actually receive the source-visible transitive axiom audit. The
certified tree had 1312 such theorem constants when this distinction was added,
so the latter floor leaves modest room for refactoring without allowing the
visible audited layer to collapse silently.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut totalTheoremCount := 0
  let mut auditedTheoremCount := 0
  let mut definitionCount := 0
  let mut opaqueCount := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "BachThesisLean." then
      match info with
      | .thmInfo _ =>
        totalTheoremCount := totalTheoremCount + 1
        unless name.isInternalDetail do
          auditedTheoremCount := auditedTheoremCount + 1
          let axioms ← collectAxioms name
          for ax in axioms do
            unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
              throwError "Unexpected axiom {ax} in theorem {name}"
      | .defnInfo _ =>
        unless name.isInternalDetail do
          definitionCount := definitionCount + 1
          let axioms ← collectAxioms name
          for ax in axioms do
            unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
              throwError "Unexpected axiom {ax} in definition {name}"
      | .opaqueInfo _ =>
        unless name.isInternalDetail do
          opaqueCount := opaqueCount + 1
          let axioms ← collectAxioms name
          for ax in axioms do
            unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
              throwError "Unexpected axiom {ax} in opaque definition {name}"
      | _ => pure ()
  unless 2000 ≤ totalTheoremCount do
    throwError "Elaborated BachThesisLean namespace contains only {totalTheoremCount} theorem constants; expected at least 2000"
  unless 1200 ≤ auditedTheoremCount do
    throwError "Axiom audit covered only {auditedTheoremCount} public source-visible theorem constants; expected at least 1200"
  logInfo m!"Axiom audit passed for {auditedTheoremCount} public source-visible theorem constants and {definitionCount + opaqueCount} public source-visible definition/opaque constants ({totalTheoremCount} theorem constants total)."
