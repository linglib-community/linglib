/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Control.Diagnostics
public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers

/-!
# Landau (2013): Control in Generative Grammar: A Research Companion

Landau's signature of obligatory control has two clauses: the controller must
be a co-dependent of the clause, and the controlled element, or part of it, is interpreted as a
bound variable. The familiar criteria follow from the two clauses: co-dependence excludes
arbitrary, long-distance, and non-c-commanding control and forces the sloppy reading under
ellipsis, and variable binding excludes the strict reading under *only*. The `Control.Excludes`
instance records this derivation, so that the library's `Control.admits` returns the book's
characterizations: a profile satisfying both clauses admits no criterial configuration and one
satisfying neither admits them all. `ofNoncoreferential` reads such a profile off whether a
clause type licenses a noncoreferential subject, a free reading of the controlled position
refuting co-dependence, and `attests` reads a row of example data as the diagnostics it attests;
the studies of controlled subjects consume both.

## Implementation notes

The signature is the book's (74), in the section on the obligatory-control signature of the
first chapter, and the derivation of the criteria from it runs through (75)–(79). Obligatory
*de se* is not criterial for obligatory control, being a property of the attitude tier, and the
lexical-subject diagnostic is a criterion of obligatory nullness rather than of obligatory
control, the separation the overt-subject studies turn on; the positive human-reference clause of
the non-obligatory signature is not modelled.

## References

* [landau-2013]
-/

@[expose] public section

namespace Landau2013

open Control

/-- The two clauses of the signature of obligatory control. The co-dependence clause admits
implicit, split, and, through "part of it", partial control. -/
inductive Clause74 where
  /-- The controller or controllers must be co-dependents of the clause. -/
  | codependent
  /-- The controlled element is interpreted as a bound variable. -/
  | boundVariable
  deriving DecidableEq, Repr, Fintype

/-- The signature derives the criteria. Co-dependence excludes the three antecedence
configurations and the strict ellipsis reading, and variable binding the strict reading under
*only*. -/
instance : Excludes Clause74 where
  excludedBy
    | .strictUnderOnly => .boundVariable
    | _                => .codependent
  surjective := by
    rintro (_ | _)
    exacts [⟨.arbitraryControl, rfl⟩, ⟨.strictUnderOnly, rfl⟩]

/-- The profile determined by whether a clause type licenses noncoreferential subjects. Free
reference attests a free reading of the controlled position, refuting co-dependence, and
obligatory coreference attests nothing. -/
def ofNoncoreferential (noncoreferential : Bool) : Set Clause74 :=
  ofAttested {d | noncoreferential = true ∧ d = .arbitraryControl}

@[simp] theorem ofNoncoreferential_eq_univ_iff {b : Bool} :
    ofNoncoreferential b = Set.univ ↔ b = false := by
  rw [ofNoncoreferential, ofAttested_eq_univ_iff]
  cases b <;> simp [Set.eq_empty_iff_forall_notMem]

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
