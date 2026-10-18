module

public import Linglib.Syntax.Agreement.Bundle

/-!
# Agreement paradigms

This file defines the descriptive agreement paradigm, the table from feature bundles to the
exponents that realize them, and the person–number bundles such a table ranges over.

A paradigm records which forms realize which cells, as a reference grammar lists them, and
commits to no account of how the table arises: syncretism is a non-injective table and
defectiveness a partial one. The cells are the bundles of `Syntax/Agreement/Bundle.lean`,
the feature space a pronoun or a word token already carries, so a controller's `HasPhi.phi`
indexes a paradigm directly, as in Corbett's account of agreement.

## Main definitions

* `Agreement.Bundle.personNumberCells`: the six person–number bundles.
* `Agreement.Bundle.IsSAP`, `Agreement.Bundle.IsPlural`, `Agreement.Bundle.person`: the
  speech-act-participant and plural cells, and the person a cell bears.
* `Agreement.Paradigm`: a table from bundles to exponents, with `Paradigm.realize`.

## References

* [corbett-1998] — agreement paradigms and the shared feature space of pronouns and targets
* [scott-2023] — Set A and Set B person–number inflection as descriptive tables
-/

@[expose] public section

namespace Agreement

namespace Bundle

/-- The person a cell bears, third where it bears none. -/
def person (b : Bundle) : Person := (b .person).unbotD .third

@[simp] theorem person_personNumber (p : Person) (n : Number) : (personNumber p n).person = p :=
  rfl

/-- A cell is a speech-act participant's when the person it bears is. -/
def IsSAP (b : Bundle) : Prop := b.person.IsSAP

instance (b : Bundle) : Decidable b.IsSAP := inferInstanceAs (Decidable b.person.IsSAP)

/-- A cell is plural when its number is. -/
def IsPlural (b : Bundle) : Prop := b .number = ↑Number.plural

instance (b : Bundle) : Decidable b.IsPlural := inferInstanceAs (Decidable (_ = _))

/-- The six person–number cells a person–number paradigm ranges over. -/
def personNumberCells : List Bundle :=
  [.personNumber .first .singular, .personNumber .second .singular,
    .personNumber .third .singular, .personNumber .first .plural,
    .personNumber .second .plural, .personNumber .third .plural]

end Bundle

/-- An agreement paradigm, the descriptive table of cells and their exponents. -/
abbrev Paradigm (Exp : Type*) := List (Bundle × Exp)

namespace Paradigm

variable {Exp : Type*}

/-- The exponent realizing a cell, that of the first entry whose cell it is. -/
def realize (p : Paradigm Exp) (c : Bundle) : Option Exp := p.lookup c

/-- The cells the paradigm distinguishes, in declaration order. -/
def cells (p : Paradigm Exp) : List Bundle := p.map (·.1)

end Paradigm

end Agreement
