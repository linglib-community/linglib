/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype

/-!
# Control diagnostics

The diagnostics of control are the antecedence and reading tests every account of a control
construction answers to: whether the controlled element may be read freely, take a non-local or a
non-c-commanding antecedent, or be read strictly under ellipsis or *only*. Which clause of an
analysis each of them refutes varies by theory, so an analysis supplies that as a function on
`Diagnostic` and the clauses a set `A` of attested diagnostics refutes are its image of `A`.
Landau's signature of obligatory control does so with two clauses (`Studies/Landau2013.lean`).

## References

* [landau-2013]
-/

@[expose] public section

namespace Control

/-- The observable diagnostics of control, the antecedence and reading tests any account of a
control construction answers to. -/
inductive Diagnostic where
  /-- A free reading of the controlled element, arbitrary control. -/
  | arbitraryControl
  /-- A non-local antecedent, long-distance control. -/
  | longDistanceControl
  /-- A non-c-commanding antecedent. -/
  | nonCCommandingControl
  /-- A strict reading under VP-ellipsis. -/
  | strictEllipsis
  /-- A strict (non-bound-variable) reading under *only*. -/
  | strictUnderOnly
  deriving DecidableEq, Repr, Fintype

end Control
