module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Bayso noun number

Bayso nouns have a general form outside the number system, non-committal as to how many,
and within the system a singular, a paucal for two to about six, and a plural, each with its
own suffix; nouns fall into two genders. An agreeing verb has three forms only, labelled
from the pronouns, which distinguish a masculine and a feminine singular and one plural:
general and singular nouns take their gender's form, paucal nouns the plural form, and
plural nouns the masculine one, as Hayward, Corbett and Hayward, and Corbett describe.

## References

* [R. J. Hayward, *Bayso revisited: some preliminary linguistic observations, II*
  (1979)][hayward-1979]
* [G. G. Corbett, R. J. Hayward, *Gender and number in Bayso* (1987)][corbett-hayward-1987]
* [G. G. Corbett, *Number* (2000)][corbett-2000]
-/

@[expose] public section

namespace Bayso

/-- The two genders. -/
inductive Gender where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- Bayso nouns have a singular, a paucal and a plural, and a general number outside the
system. -/
def numberSystem : Number.System :=
  { values := {.singular, .paucal, .plural}, hasGeneral := true }

/-- The numbers a noun has a form for, the general and the values of the system. -/
def nounNumbers : Finset Number := insert .general numberSystem.values

/-- Pronouns distinguish the singular and the plural. -/
def pronounNumberSystem : Number.System := { values := {.singular, .plural} }

/-- The three forms of an agreeing verb, labelled from the pronouns that take them:
*hudure* 'slept' masculine, *hudurte* feminine, *hudureene* plural. -/
inductive Concord where
  | masc
  | fem
  | plural
  deriving DecidableEq, Repr, Fintype

/-- A pronoun takes its gender's concord in the singular and the plural concord in the plural. -/
def Gender.pronounConcord (g : Gender) : pronounNumberSystem.values → Concord :=
  pronounNumberSystem.elim (match g with | .masc => .masc | .fem => .fem) .plural

/-- A noun takes its gender's concord in the general and the singular, the plural concord in the
paucal, and the masculine concord in the plural. -/
def Gender.concord : Gender → nounNumbers → Concord
  | .masc, ⟨.general, _⟩ | .masc, ⟨.singular, _⟩ => .masc
  | .fem, ⟨.general, _⟩ | .fem, ⟨.singular, _⟩ => .fem
  | _, ⟨.paucal, _⟩ => .plural
  | _, ⟨.plural, _⟩ => .masc
  | _, ⟨.dual, h⟩ | _, ⟨.trial, h⟩ | _, ⟨.greaterPaucal, h⟩ | _, ⟨.greaterPlural, h⟩
  | _, ⟨.minimal, h⟩ | _, ⟨.augmented, h⟩ | _, ⟨.unitAugmented, h⟩ | _, ⟨.globalPlural, h⟩ =>
    absurd h (by decide)

/-- General and singular nouns take their gender's concord. -/
@[simp] theorem Gender.concord_general (g : Gender) :
    g.concord ⟨.general, by decide⟩ = g.concord ⟨.singular, by decide⟩ := by
  cases g <;> rfl

/-- Paucal nouns take the plural concord. -/
@[simp] theorem Gender.concord_paucal (g : Gender) : g.concord ⟨.paucal, by decide⟩ = .plural := by
  cases g <;> rfl

/-- Plural nouns take the masculine concord. -/
@[simp] theorem Gender.concord_plural (g : Gender) : g.concord ⟨.plural, by decide⟩ = .masc := by
  cases g <;> rfl

/-- A noun with its four number forms; the citation form is the general one. -/
structure Noun extends GenderedNoun Gender where
  /-- The singular form. -/
  singular : String
  /-- The paucal form. -/
  paucal : String
  /-- The plural form. -/
  plural : String
  deriving DecidableEq, Repr

/-- *lúban* 'lion'. -/
def luban : Noun :=
  { form := "lúban", gloss := "lion", gender := .masc, singular := "lubántiti",
    paucal := "lubanjaa", plural := "lubanjool" }

/-- *kimbír* 'bird'. -/
def kimbir : Noun :=
  { form := "kimbír", gloss := "bird", gender := .fem, singular := "kimbírtiti",
    paucal := "kimbirjaa", plural := "kimbirjool" }

/-- The nouns the sources cite. -/
def allNouns : List Noun := [luban, kimbir]

/-- The form of a noun in each number. -/
def Noun.formAt (n : Noun) : nounNumbers → String
  | ⟨.general, _⟩ => n.form
  | ⟨.singular, _⟩ => n.singular
  | ⟨.paucal, _⟩ => n.paucal
  | ⟨.plural, _⟩ => n.plural
  | ⟨.dual, h⟩ | ⟨.trial, h⟩ | ⟨.greaterPaucal, h⟩ | ⟨.greaterPlural, h⟩ | ⟨.minimal, h⟩
  | ⟨.augmented, h⟩ | ⟨.unitAugmented, h⟩ | ⟨.globalPlural, h⟩ => absurd h (by decide)

end Bayso
