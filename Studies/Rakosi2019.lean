/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Restrict
public import Linglib.Syntax.Agreement.Phi
public import Linglib.Fragments.Hungarian.Pronouns
public import Linglib.Fragments.Hungarian.Reciprocals
public import Linglib.Data.Examples.Rakosi2019

/-!
# Rákosi (2019): Reciprocal anaphors in singular constructions in Hungarian

An antecedent has a grammatical number, which the verb agrees in, and a semantic number, that of
the individuals it denotes. Quantified, coordinate and collective antecedents and bound singular
variables can be grammatically singular and semantically plural. A Hungarian plural reflexive
needs the plural verb, the reciprocal *egymás* only the semantic plural. Over the paper's
examples this file proves the two licensing conditions and the double dissociation between them:
a bound reflexive's judgment is a function of its agreement with the verb and not of the
antecedent's semantic number, the reciprocal's a function of the semantic number and not of the
agreement.

## Main definitions

* `Rakosi2019.HasAnaphor`: the anaphor of a row is a given pronoun of the fragment.
* `Rakosi2019.verbAgr?`, `Rakosi2019.semanticNumber?`: the person and number the verb agrees in,
  and the semantic number of the antecedent.

## Main results

* `Rakosi2019.reflexive_acceptable_iff_agree`, `Rakosi2019.not_factorsThrough_semanticNumber`: a
  bound reflexive is acceptable exactly when it agrees with the verb, whatever its antecedent
  denotes.
* `Rakosi2019.reciprocal_acceptable_iff`, `Rakosi2019.not_factorsThrough_verbAgr`: the reciprocal
  is acceptable exactly when its antecedent is semantically plural, whatever the verb agrees in.
* `Rakosi2019.reciprocal_with_singular_verb`: in each of §§3–6 the reciprocal is accepted with a
  singular verb and a semantically plural antecedent.
* `Rakosi2019.inclusive_not_bound`: the inclusive reflexive of §2 is not a bound variable.

## References

* [rakosi-2019]
-/

@[expose] public section

namespace Rakosi2019

open Hungarian.Pronouns Hungarian.Reciprocals
open Examples (all)

/-! ### The rows -/

/-- The anaphor of the row is the pronoun `p`. -/
def HasAnaphor (e : Datum) (p : Pronoun) : Prop := e.feature? "anaphor" = some p.form

instance (e : Datum) (p : Pronoun) : Decidable (HasAnaphor e p) :=
  inferInstanceAs (Decidable (_ = _))

/-- The rows whose anaphor is the pronoun `p`. -/
def rowsWith (p : Pronoun) : Set Datum := {e | e ∈ all ∧ HasAnaphor e p}

instance (p : Pronoun) : DecidablePred (· ∈ rowsWith p) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every anaphor a row names is *egymás* or a reflexive of the paradigm. -/
theorem hasAnaphor_of_feature :
    ∀ e ∈ all, ∀ f ∈ e.feature? "anaphor",
      HasAnaphor e egymas.toPronoun ∨ ∃ r ∈ reflexives, HasAnaphor e r.toPronoun := by
  decide

/-- The person and number the verb agrees in. -/
def verbAgr? (e : Datum) : Option (Person × Number) :=
  e.parse? "verb" [("1sg", (.first, .singular)), ("1pl", (.first, .plural)),
    ("3sg", (.third, .singular)), ("3pl", (.third, .plural))]

/-- The semantic number of the antecedent: singular if it denotes one individual, plural if it
denotes a plurality or, as the bound singular variable of §6, ranges over one. -/
def semanticNumber? (e : Datum) : Option Number :=
  e.parse? "semanticNumber" [("singular", .singular), ("plural", .plural)]

/-- The row is the inclusive reference of §2, a singular subject included in the reference of a
plural reflexive. -/
def InclusiveReference (e : Datum) : Prop := e.feature? "antecedent" = some "inclusive"

instance (e : Datum) : Decidable (InclusiveReference e) := inferInstanceAs (Decidable (_ = _))

/-! ### The reflexive -/

/-- A bound reflexive, one outside the inclusive reference of §2, is acceptable exactly when it
agrees with the verb in person and number. -/
theorem reflexive_acceptable_iff_agree :
    ∀ e ∈ all, ¬ InclusiveReference e → ∀ r ∈ reflexives, HasAnaphor e r.toPronoun →
      ∀ v ∈ verbAgr? e, (e.judgment = .acceptable ↔
        HasPhi.Agree r.toPronoun (Agreement.Bundle.personNumber v.1 v.2)) := by
  decide

/-- The reflexive's judgment is no function of the antecedent's semantic number: in (11a) and
(11b') *magát* is bound by *Kati és Éva*, accepted with the singular verb and rejected with the
plural. -/
theorem not_factorsThrough_semanticNumber :
    ¬ ((rowsWith maga.toPronoun).domRestrict Datum.judgment).FactorsThrough
      ((rowsWith maga.toPronoun).domRestrict semanticNumber?) := fun h ↦
  absurd (@h ⟨Examples.ex_11a, by decide⟩ ⟨Examples.ex_11b_, by decide⟩ rfl) (by decide)

/-! ### The reciprocal -/

/-- The reciprocal is acceptable exactly when its antecedent is semantically plural. -/
theorem reciprocal_acceptable_iff :
    ∀ e ∈ all, HasAnaphor e egymas.toPronoun →
      (e.judgment = .acceptable ↔ semanticNumber? e = some .plural) := by
  decide

/-- The reciprocal's judgment is no function of the verb's agreement: the verb agrees in the
third person singular in both (2a) and (12), and the reciprocal is rejected in (2a) and accepted
in (12). -/
theorem not_factorsThrough_verbAgr :
    ¬ ((rowsWith egymas.toPronoun).domRestrict Datum.judgment).FactorsThrough
      ((rowsWith egymas.toPronoun).domRestrict verbAgr?) := fun h ↦
  absurd (@h ⟨Examples.ex_2a, by decide⟩ ⟨Examples.ex_12, by decide⟩ rfl) (by decide)

/-- In each of §§3–6, quantified, coordinate and collective antecedents and bound singular
variables, the reciprocal is accepted with a singular verb and a semantically plural
antecedent. -/
theorem reciprocal_with_singular_verb :
    ∀ n ∈ [3, 4, 5, 6], ∃ e ∈ all, e.nat? "section" = some n ∧ HasAnaphor e egymas.toPronoun ∧
      (∀ v ∈ verbAgr? e, v.2 = .singular) ∧ semanticNumber? e = some .plural ∧
        e.judgment = .acceptable := by
  decide

/-! ### Inclusive reference -/

/-- The inclusive reflexive of §2 is never read as a bound variable, so its disagreement with the
verb is no counterexample to `reflexive_acceptable_iff_agree`. -/
theorem inclusive_not_bound :
    ∀ e ∈ all, InclusiveReference e → ∀ r ∈ reflexives, HasAnaphor e r.toPronoun →
      e.readings.lookup "bound variable" ≠ some .acceptable := by
  decide

end Rakosi2019
