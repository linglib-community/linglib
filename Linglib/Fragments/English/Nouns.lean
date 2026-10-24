module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Morphology.Word.Basic
public import Linglib.Fragments.English.Inflection

/-!
# English nouns

The English noun as a lexical entry is a `ClassifiedNoun` over no classifiers, which a numeral
counts directly or not at all, with the sex it restricts its referents to and its plural where it
has them; a regular
plural is the noun with the suffix `English.Inflection.s`. Names are the root `ProperName`. English
nouns have no grammatical gender; *man*, *woman* and the names restrict their referents' sex,
which their pronouns agree with. Bare plurals and bare mass nouns are arguments and a bare singular
count noun is not, which Chierchia derives from the Nominal Mapping Parameter
(`Studies/Chierchia1998.lean`).

## Main definitions

* `numberSystem`: the singular and the plural.
* `Noun`: the entry, with `Noun.realize` giving its form at a number.
* `Noun.toWordSg`, `Noun.toWord`: the entry as a `Word` token.

## Implementation notes

Whether a numeral counts a noun and whether the noun has a plural are separate fields, since
*oats* has a plural and no numeral counts it. A noun with a plural and no singular, such as
*oats*, is not yet recorded: `Noun.realize` gives every entry its citation form as the singular.

## References

* [chierchia-1998]
-/

@[expose] public section

namespace English.Nouns

open Morphology

/-- An English noun is a classified noun over no classifiers, with the sex it restricts its
referents to and its plural where it has them. -/
structure Noun extends ClassifiedNoun Empty where
  /-- The sex the noun restricts its referents to, which its pronouns agree with, where it does. -/
  sex : Option Sex := none
  /-- The plural, where the noun has one. -/
  plural : Option String := none
  deriving DecidableEq

/-- A common count noun, counted directly and with the regular *-s* plural; English is the
metalanguage, so the gloss is the form. -/
def Noun.common (form : String) : Noun :=
  { form, gloss := form, counters := {none}
    plural := some (Inflection.spell [.root form, Inflection.s]) }

/-- A mass noun, which no numeral counts and which has no plural. -/
def Noun.mass (form : String) : Noun := { form, gloss := form, counters := ∅ }

/-- English nouns distinguish two numbers, the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- The form at a number is the citation form in the singular and the plural where the noun has
one. -/
def Noun.realize (n : Noun) : Number → Option String
  | .singular => some n.form
  | .plural => n.plural
  | _ => none

theorem Noun.realize_eq_none (n : Noun) {m : Number} (hm : m ∉ numberSystem.values) :
    n.realize m = none := by
  cases m <;> simp_all [numberSystem, Noun.realize]

/-- The singular word token is a `NOUN`, gendered by the sex the entry restricts where it does. -/
def Noun.toWordSg (n : Noun) : Word :=
  { form := n.form, cat := .NOUN
    features := Features.of (number := some .singular) (gender := n.sex.map Sex.toUD) }

/-- The entry as a word token at a number, where it has a form there. -/
def Noun.toWord (n : Noun) (num : Number) : Option Word :=
  (n.realize num).map fun form ↦
    { n.toWordSg with
      form, features := Features.of (number := some num) (gender := n.sex.map Sex.toUD) }

theorem Noun.toWord_singular (n : Noun) : n.toWord .singular = some n.toWordSg := rfl

/-! ### Count nouns -/

def pizza : Noun := .common "pizza"
def year : Noun := .common "year"
def book : Noun := .common "book"
def cat : Noun := .common "cat"
def dog : Noun := .common "dog"
def girl : Noun := .common "girl"
def boy : Noun := .common "boy"
def ball : Noun := .common "ball"
def table : Noun := .common "table"
def squirrel : Noun := .common "squirrel"
def kitchen : Noun := .common "kitchen"
def story : Noun := .common "story"
def lawyer : Noun := .common "lawyer"
def student : Noun := .common "student"
def teacher : Noun := .common "teacher"
def soldier : Noun := .common "soldier"
def horse : Noun := .common "horse"
def brother : Noun := .common "brother"
def spy : Noun := .common "spy"
def idea : Noun := .common "idea"
def lot : Noun := .common "lot"
def bean : Noun := .common "bean"
def lentil : Noun := .common "lentil"
def spider : Noun := .common "spider"
def pollenGrain : Noun := .common "pollen grain"
def father : Noun := { Noun.common "father" with sex := some .male }
def mother : Noun := { Noun.common "mother" with sex := some .female }
def man : Noun := { Noun.common "man" with sex := some .male, plural := "men" }
def woman : Noun := { Noun.common "woman" with sex := some .female, plural := "women" }
def fireman : Noun := { Noun.common "fireman" with plural := "firemen" }
def person : Noun := { Noun.common "person" with plural := "people" }
def child : Noun := { Noun.common "child" with plural := "children" }

/-! ### Mass nouns -/

def water : Noun := .mass "water"
def sand : Noun := .mass "sand"
def trash : Noun := .mass "trash"
def furniture : Noun := .mass "furniture"
def rice : Noun := .mass "rice"
def gold : Noun := .mass "gold"
def air : Noun := .mass "air"
def wine : Noun := .mass "wine"
def coffee : Noun := .mass "coffee"
def beer : Noun := .mass "beer"
def milk : Noun := .mass "milk"
def tea : Noun := .mass "tea"
def pollen : Noun := .mass "pollen"
def mold : Noun := .mass "mold"

/-! ### Proper names -/

/-- A name glossed by itself. -/
def name (form : String) (sex : Option Sex := none) : ProperName := { form, gloss := form, sex }

def john : ProperName := name "John" (some .male)
def mary : ProperName := name "Mary" (some .female)
def bill : ProperName := name "Bill" (some .male)
def sue : ProperName := name "Sue" (some .female)
def fred : ProperName := name "Fred" (some .male)
def sam : ProperName := name "Sam"
def pat : ProperName := name "Pat"

end English.Nouns
