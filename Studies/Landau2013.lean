/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers

/-!
# Landau (2013): Control in Generative Grammar: A Research Companion

Landau's signature of obligatory control has two clauses: the controller must
be a co-dependent of the clause, and the controlled element, or part of it, is interpreted as a
bound variable. The familiar criteria follow from the two clauses: co-dependence excludes
arbitrary, long-distance, and non-c-commanding control and forces the sloppy reading under
ellipsis, and variable binding excludes the strict reading under *only*. `Diagnostic` lists these
five configurations, which are the book's own and not a battery other accounts share: Williams's
five criteria and Hornstein's seven are different lists. `refutes` records this
derivation as the clause each diagnostic refutes, so the clauses a construction fails are the image
of the diagnostics it shows, and a construction is obligatory control when that image is empty.
`attests` reads a row of example data as the diagnostics it attests; the studies of controlled
subjects consume both.

## Implementation notes

The derivation of the criteria is the book's discussion following the signature in the first
chapter. Obligatory *de se* is not criterial for obligatory control, being a property of the
attitude tier, and the lexical-subject diagnostic is a criterion of obligatory nullness rather
than of obligatory control, the separation the overt-subject studies turn on; the positive
human-reference clause of the non-obligatory signature is not modelled.

## References

* [landau-2013]
-/

@[expose] public section

namespace Landau2013

/-- (75)–(79): the configurations the signature of obligatory control excludes, three of
antecedence and two readings. -/
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

/-- (74): the two clauses of the signature of obligatory control. The co-dependence clause admits
implicit and split control, and the bound-variable clause, through "part of it", partial
control. -/
inductive Clause74 where
  /-- The controller or controllers must be co-dependents of the clause. -/
  | codependent
  /-- The controlled element is interpreted as a bound variable. -/
  | boundVariable
  deriving DecidableEq, Repr, Fintype

/-- (75)–(79): the clause of the signature a diagnostic refutes. Co-dependence excludes the three
antecedence configurations and the strict ellipsis reading, and variable binding the strict
reading under *only*. -/
def refutes : Diagnostic → Clause74
  | .strictUnderOnly => .boundVariable
  | _ => .codependent

/-- The diagnostic a row of example data attests. A free reading of the embedded subject is
arbitrary control; a strict reading is the strict reading of the row's test, ellipsis or *only*;
and an acceptable row whose antecedent the paper marks non-c-commanding or long-distance attests
that antecedence. -/
def attests (row : Datum) : Diagnostic → Prop
  | .arbitraryControl => ("free", .acceptable) ∈ row.readings
  | .strictEllipsis =>
    row.feature? "diagnostic" = some "ellipsis" ∧ ("strict", .acceptable) ∈ row.readings
  | .strictUnderOnly =>
    row.feature? "diagnostic" = some "only" ∧ ("strict", .acceptable) ∈ row.readings
  | .nonCCommandingControl =>
    row.feature? "antecedent" = some "nonCCommanding" ∧ row.judgment = .acceptable
  | .longDistanceControl =>
    row.feature? "antecedent" = some "longDistance" ∧ row.judgment = .acceptable

instance (row : Datum) : DecidablePred (attests row) := fun d ↦ by
  cases d <;> unfold attests <;> infer_instance

end Landau2013
