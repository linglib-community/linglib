/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Flat.Finset
public import Linglib.Fragments.Ga.Case
public import Linglib.Morphology.Paradigm.Morphome
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Gã personal pronouns

The pronoun paradigm of [allotey-2021]'s Table 3 (Gã, ISO 639-3 `gaa`; Kwa, Ghana), a table of
forms by person and number and by case, and the `PersonalPronoun` entries it yields. Gã has no
clusivity and no gender.

## Implementation notes

* A cell is a row and a case, and holds a finset of forms: the first person singular subjective
  has two, *mi* and the past-tense *ĩ*, and the impersonal *a* has neither objective nor
  possessive form. Table 3 also gives the third person singular objective as null, the form of an
  inanimate object (§4.2); the table records forms only.
* The entry of a form has the cases of the cells it fills, and the flat value of their person and
  number (`Flat.finsetInf`). *o* fills the second person singular subjective and possessive, so its
  cases are the nominative and the genitive and its flat case (`Pronoun.case`) is `⊥`, which admits
  the objective too: no flat case admits two cases and not a third.
* The paper does not classify the subject pronouns by structural deficiency: [campbell-2017]
  writes them as clitics prefixed to the verb, which the paper rejects on the strength of the
  negation that intervenes between the embedded subject and its verb, so `strength` stays `none`.
* Lean does not accept `ɛ` or `ŋ` in plain identifiers, so names use Latin letters (`le`, `wo`,
  `nye`, `ame`) and the orthography lives in `form`.

## References

* [allotey-2021]
* [campbell-2017]
-/

@[expose] public section

namespace Ga.Pronouns

open Morphology

/-- The rows of Table 3: a person and number each, and the third person impersonal. -/
inductive Row where
  | sg1 | sg2 | sg3 | imp | pl1 | pl2 | pl3
  deriving DecidableEq, Fintype, Repr

/-- The person of a row. -/
def Row.person : Row → Person
  | .sg1 | .pl1 => .first
  | .sg2 | .pl2 => .second
  | .sg3 | .imp | .pl3 => .third

/-- The number of a row, none for the impersonal. -/
def Row.number : Row → Option Number
  | .sg1 | .sg2 | .sg3 => some .singular
  | .imp => none
  | .pl1 | .pl2 | .pl3 => some .plural

/-- Table 3 ([allotey-2021] p. 25), the forms of each cell. *ĩ* is the first person singular
subject in the past tense (p. 27, (74)). -/
def table : Row × Case → Finset String
  | (.sg1, .subjective) => {"mi", "ĩ"}
  | (.sg1, _) => {"mi"}
  | (.sg2, .objective) => {"bo"}
  | (.sg2, _) => {"o"}
  | (.sg3, .objective) => {"lɛ"}
  | (.sg3, _) => {"e"}
  | (.imp, .subjective) => {"a"}
  | (.imp, _) => ∅
  | (.pl1, _) => {"wɔ"}
  | (.pl2, _) => {"nyɛ"}
  | (.pl3, _) => {"amɛ"}

/-- The pronoun `f`, with the cases of the cells it fills and their flat person and number. -/
def entry (f : String) : PersonalPronoun :=
  { form := f,
    person := Flat.finsetInf (formCellsOf table f) fun c ↦ (c.1.person : Flat Person),
    number := Flat.finsetInf (formCellsOf table f) fun c ↦ (c.1.number : Flat Number),
    cases := (formCellsOf table f).image (·.2.label) }

/-- The personal pronoun inventory: the entry of every form of the table. -/
def pronouns : Finset PersonalPronoun := (Finset.univ.biUnion table).image entry

/-- *mi* — first person singular, the form of all three cases. -/
def mi : PersonalPronoun := entry "mi"

/-- *o* — second person singular subjective and possessive. -/
def o : PersonalPronoun := entry "o"

/-- *bo* — second person singular objective. -/
def bo : PersonalPronoun := entry "bo"

/-- *e* — third person singular subjective and possessive. -/
def e : PersonalPronoun := entry "e"

/-- *lɛ* — third person singular objective. -/
def le : PersonalPronoun := entry "lɛ"

/-- *wɔ* — first person plural, the form of all three cases. -/
def wo : PersonalPronoun := entry "wɔ"

/-- *nyɛ* — second person plural, the form of all three cases. -/
def nye : PersonalPronoun := entry "nyɛ"

/-- *amɛ* — third person plural, the form of all three cases. -/
def ame : PersonalPronoun := entry "amɛ"

/-- The forms of each referential category. -/
def paradigm : Person.Category → Finset String := PersonalPronoun.paradigm pronouns

end Ga.Pronouns
