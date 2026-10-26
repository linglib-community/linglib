module

public import Mathlib.Data.Finset.Union
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Clause.Chaining

/-!
# Nungon medial clauses

Nungon (Finisterre, Trans-New Guinea; Morobe Province, Papua New Guinea) chains medial
clauses before a single final verb, and a medial verb consists of a dependent stem, the verb
root with *-ŋ* after a vowel, and the medial suffix *-a*. A same-subject medial verb carries
nothing else, *wii-ŋ-a* 'combing' and *eer-a* 'inserting'. A different-subject medial verb
carries, between the root and *-a*, a subject desinence from a set distinct from the tensed
final-verb desinences and similar to those of the contrafactual and the imperative: *-wa*,
*-i*, *-un* in the singular, *-ra* and *-uny* in the dual and *-na* and *-u* in the plural,
second and third person falling together outside the singular, so *tɔ-wa-ya* 'I doing'. The
medial verb itself does not distinguish sequence from simultaneity; an ongoing event is
expressed by the same-subject medial verb followed by *it-* 'be' in a progressive
construction, and completion before the next event by the perfect, the same-subject medial
verb followed by a second word inflected for person and number, *mɔraina*, *mina*, *muna*
in the singular, which is used whether or not the subject changes. Medial clauses carry no
tense, mood or aspect of their own. Medial clauses occur on their own, and chains are
bridged by recapitulative and by summary linkage.

## Main definitions

* `Nungon.medialSuffix`, `Nungon.dependentStemSuffix`, `Nungon.dsDesinence`,
  `Nungon.perfect` — the medial suffix, the stem-forming *-ŋ*, the different-subject
  desinences and the perfect forms by person and number
* `Nungon.Medial` — the three medial forms, same-subject, different-subject and perfect,
  with their morphs by person and number (`morphs`), the switch-reference value they carry
  (`sr`), the relations they encode (`relations`) and whether they index the subject
  (`IndexesSubject`), which make them an instance of `MedialForm`

## Implementation notes

The clause-chaining typology over these forms is in `Studies/SarvasyAikhenvald2025.lean`.

## References

* [sarvasy-2017]
* [sarvasy-2015]
* [sarvasy-aikhenvald-2025]
-/

@[expose] public section

namespace Nungon

open Morphology (Morph)

/-- *-a*, the medial verb suffix, *-ya* after a vowel. -/
def medialSuffix : Morph := .suff "a"

/-- *-ŋ*, which a vowel-final root takes to form the dependent stem. -/
def dependentStemSuffix : Morph := .suff "ŋ"

/-- The different-subject desinences after a vowel-final root, second and third person
syncretic in the dual and the plural. -/
def dsDesinence : Person → Number → Option Morph
  | .first, .singular => some (.suff "wa")
  | .second, .singular => some (.suff "i")
  | .third, .singular => some (.suff "un")
  | .first, .dual => some (.suff "ra")
  | .second, .dual | .third, .dual => some (.suff "uny")
  | .first, .plural => some (.suff "na")
  | .second, .plural | .third, .plural => some (.suff "u")
  | _, _ => none

/-- The perfect forms, the second word of the perfect construction, second and third person
syncretic in the dual and the plural. -/
def perfect : Person → Number → Option Morph
  | .first, .singular => some (.free "mɔraina")
  | .second, .singular => some (.free "mina")
  | .third, .singular => some (.free "muna")
  | .first, .dual => some (.free "mɔtdaina")
  | .second, .dual | .third, .dual => some (.free "munya")
  | .first, .plural => some (.free "mɔtnaina")
  | .second, .plural | .third, .plural => some (.free "muya")
  | _, _ => none

/-- The medial forms. -/
inductive Medial where
  /-- The same-subject medial verb, the dependent stem with *-a*. -/
  | ss
  /-- The different-subject medial verb, a subject desinence before *-a*. -/
  | ds
  /-- The perfect, the same-subject medial verb followed by a perfect form, used with the
  same or a different subject. -/
  | perfect
  deriving DecidableEq, Repr, Fintype

namespace Medial

/-- The morphs after the dependent stem for a subject of the given person and number; the
same-subject form does not vary. -/
def morphs : Medial → Person → Number → List Morph
  | ss, _, _ => [medialSuffix]
  | ds, p, n => (dsDesinence p n).toList ++ [medialSuffix]
  | perfect, p, n => medialSuffix :: (Nungon.perfect p n).toList

/-- The switch-reference value a form carries; `none` for the perfect. -/
def sr : Medial → Option SwitchReference
  | ss => some .ss
  | ds => some .ds
  | perfect => none

/-- The interclausal relations a form encodes, which for the perfect is completion before the
next event and for the other two none. -/
def relations : Medial → Finset InterclauseRelation
  | ss | ds => ∅
  | perfect => {.sequential}

/-- The form carries a subject desinence. -/
def IndexesSubject (m : Medial) : Prop := m ≠ ss

instance : DecidablePred IndexesSubject := fun _ => inferInstanceAs (Decidable (_ ≠ _))

instance : MedialForm Medial where
  sr := sr
  relations := relations
  IndexesSubject := IndexesSubject

end Medial

end Nungon
