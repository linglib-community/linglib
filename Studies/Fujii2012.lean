/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Landau2004

/-!
# Fujii (2012): On the Calculus of Control and Lack of Overt Agreement Morphology

Fujii asks what a calculus of control built on semantic tense and agreement can say about a
language with no agreement morphology, as Japanese is. He takes the calculus in the form that
reads the inflectional head alone: a head positive for both features licenses a lexical subject,
and [any negative value gives obligatory control](##Fujii2012.hasOC_iff). The question is then
what value of agreement a Japanese clause has, and he considers three answers. Reading the value
off whether the clause is controlled would leave the calculus predicting nothing. Saying that the
language has no agreement feature fails in both versions of the calculus: where nominative case
needs both features positive, [no clause assigns it](##Fujii2012.not_assignsNominative) and
every clause is controlled, and under Landau's rule a head without the feature [is assigned no
value](##Fujii2012.r_eq_none), so that [neither kind of subject is
licensed](##Fujii2012.not_licenses) and controlled clauses are not told from uncontrolled ones.
His own answer replaces agreement by a feature that also registers tense morphology, negative
where one of the two tense markers is blocked.

## Implementation notes

The calculus on the inflectional head is stated on [landau-2004]'s rule, whose value at a head
with both features is their conjunction. Nominative assignment is the condition of the variant of
the calculus the paper attributes to Nunes and to Boeckx, Hornstein and Nunes.

## TODO

The Japanese data are not formalized: the generalization that complements with untensed or
dependent tense allow obligatory control and those with independent tense do not, the criterion
that a head is negative for the revised feature when one of the tense markers *-ru* and *-ta* is
blocked, and the classification of the six complement types by it.

## References

* [fujii-2012]
* [landau-2004]
-/

@[expose] public section

namespace Fujii2012

open Landau2004

/-- The calculus on the inflectional head: obligatory control is licensed by a head with both
features unless both are positive. -/
def HasOC (h : Finiteness.Head) : Prop := h.r = some false

instance (h : Finiteness.Head) : Decidable (HasOC h) := inferInstanceAs (Decidable (_ = _))

/-- A head with both features gives obligatory control exactly when one of them is negative. -/
theorem hasOC_iff (t agr : Bool) : HasOC ⟨some t, some agr⟩ ↔ ¬ (t = true ∧ agr = true) := by
  cases t <;> cases agr <;> decide

/-- Nominative case is assigned by a head positive for both features. -/
def AssignsNominative (h : Finiteness.Head) : Prop := h.tense = some true ∧ h.agr = some true

/-- A head with no agreement feature assigns no nominative case, whatever its tense, so that
every clause of a language without the feature would be controlled. -/
theorem not_assignsNominative (t : Option Bool) : ¬ AssignsNominative ⟨t, none⟩ :=
  fun h ↦ nomatch h.2

/-- Landau's rule assigns no value to a head with no agreement feature. -/
theorem r_eq_none (t : Option Bool) : (⟨t, none⟩ : Finiteness.Head).r = none :=
  Finiteness.Head.r_eq_none_iff.2 (.inr rfl)

/-- A clause whose inflectional head has no agreement feature licenses neither PRO nor a
referential subject by Landau's rule, whatever its tense and its complementizer. -/
theorem not_licenses (t : Option Bool) (c : Finiteness.Head) :
    ¬ (⟨⟨t, none⟩, c⟩ : Finiteness).LicensesPRO ∧
      ¬ (⟨⟨t, none⟩, c⟩ : Finiteness).LicensesReferential :=
  ⟨Finiteness.not_licensesPRO_of_r_eq_none (r_eq_none t), by
    simp [Finiteness.LicensesReferential, r_eq_none]⟩

end Fujii2012
