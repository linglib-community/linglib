/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.UD.UPOS
public import Linglib.Syntax.Minimalist.Clause.Spine

/-!
# Verbal spines

A verbal spine is what the placement of a verb and of its inflection reads off a clause: the verb
at its foot, lexical or auxiliary as its word is tagged, the heads above it that the verb is
related to, the heads among them whose specifier is pronounced, and whether the verb phrase is
pronounced in place, elided, or pronounced in a fronted copy. Accounts of *do*-support differ in
what breaks the relation of the verb to Tense, a head between them such as Laka's Σ or
[a pronounced specifier between them](##Minimalist.VerbalSpine.Intervenes) such as an inverted
subject, and the spine records both, so that each account is a predicate on it.

## Implementation notes

The specifier of the highest head does not intervene, since that head does not c-command it, so
the pronounced subject of a declarative in the specifier of T is recorded and intervenes only
once T is related to C.

## References

* [laka-1990]
* [arregi-pietraszko-2021]
-/

@[expose] public section

namespace Minimalist

/-- The verb phrase is pronounced in place, elided, or pronounced in a fronted copy. -/
inductive VPStatus
  | inSitu | elided | fronted
  deriving DecidableEq, Repr

/-- A verbal spine: the tag of the verb at its foot, the heads above it that the verb is related
to, lowest first, the heads among them whose specifier is pronounced, and the status of the verb
phrase. -/
structure VerbalSpine where
  verb : UD.UPOS := .VERB
  above : List Cat
  specifiers : Finset Cat := ∅
  vp : VPStatus := .inSitu
  deriving DecidableEq

namespace VerbalSpine

variable (x : VerbalSpine)

/-- The clause spine of the verb and the heads above it. -/
def toClauseSpine : ClauseSpine := ⟨.V :: x.above⟩

/-- The verb is an auxiliary. -/
def IsAuxiliary : Prop := x.verb = .AUX

instance : Decidable x.IsAuxiliary := inferInstanceAs (Decidable (_ = _))

/-- The verb is related to Laka's Σ. -/
def HasPol : Prop := .Pol ∈ x.above

instance : Decidable x.HasPol := inferInstanceAs (Decidable (_ ∈ _))

/-- A pronounced specifier stands between the highest head and the verb: the specifier of a head
below the highest. -/
def Intervenes : Prop := ∃ c ∈ x.above.dropLast, c ∈ x.specifiers

instance : Decidable x.Intervenes := inferInstanceAs (Decidable (∃ _ ∈ _, _))

end VerbalSpine

end Minimalist
