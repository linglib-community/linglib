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
plural nouns the masculine one ([hayward-1979]; [corbett-hayward-1987]; [corbett-2000]).

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
abbrev pronounNumberSystem : Number.System := .singularPlural

/-- The three forms of an agreeing verb, labelled from the pronouns that take them:
*hudure* 'slept' masculine, *hudurte* feminine, *hudureene* plural. -/
inductive Concord where
  | masc
  | fem
  | plural
  deriving DecidableEq, Repr, Fintype

/-- The concord a pronoun takes: its gender in the singular, the plural form in the plural. -/
def Gender.pronounConcord (g : Gender) (n : pronounNumberSystem.values) : Concord :=
  match g, n.1 with
  | .masc, .singular => .masc
  | .fem, .singular => .fem
  | _, _ => .plural

/-- The concord a noun takes, by gender and number: its gender's form for the general and
the singular, the plural form for the paucal, the masculine form for the plural. -/
def Gender.concord (g : Gender) (n : nounNumbers) : Concord :=
  match g, n.1 with
  | .masc, .general | .masc, .singular => .masc
  | .fem, .general | .fem, .singular => .fem
  | _, .paucal => .plural
  | _, _ => .masc

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
def Noun.formAt (n : Noun) (v : nounNumbers) : String :=
  match v.1 with
  | .general => n.form
  | .singular => n.singular
  | .paucal => n.paucal
  | _ => n.plural

end Bayso
