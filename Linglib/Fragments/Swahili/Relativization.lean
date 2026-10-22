module

public import Linglib.Syntax.Clause.Relative
public import Linglib.Fragments.Swahili.Basic

/-!
# Swahili relativization

This file defines the Swahili *amba* relative clause and its resumptive pronouns as Scott
describes them. The head precedes the complementizer *amba*, which takes the relative concord
of the head's class, *vi-azi amba-vyo u-li-vi-menya* 'the potatoes that you peeled'. A
relativized subject or direct object leaves a gap, with subject and object agreement obligatory
on the verb, and no pronoun may fill it. The object of a monosyllabic preposition or
connective, *na* 'with', *ya* 'of' or *mwa* 'in', is instead resumed by a pronoun suffixed to
it, since a stranded monosyllable would fall below the two-unit minimal word; a trisyllabic
preposition such as *katika* 'on' is dropped instead. The resumptive pronouns are the
prepositional pronouns of matrix clauses, and the third person ones are the concords of
classes 1 and 2, the animate gender, which carry number and gender but no person. Inside an
adjunct island the resumptive is a bound pronoun matching the head in person; in a parasitic
gap it is a movement copy without person, the analysis of `Studies/Scott2021.lean`.

## Main definitions

* `Swahili.amba`, `Swahili.relativizers`: the relativizer *amba*
* `Swahili.pronoun`, `Swahili.resumptive`: the full and the resumptive pronouns by person and
  number
* `Swahili.NounClass.concord?`: the relative concord of classes 1 to 10
* `Swahili.Preposition`, `Preposition.TriggersResumption`: the prepositions and connectives
  with their syllable count, and the minimal-word condition on resumption

## Main results

* `Swahili.resumptive_third`: the third person resumptives are the concords of classes 1 and 2
* `Swahili.Preposition.triggersResumption`: the monosyllables trigger resumption and the
  trisyllable does not

## Implementation notes

* Scott gives the concords of classes 1 to 10 only, so `concord?` is partial. The concord is
  also the suffix of the emphatic copula *ndi-* of the clefts Scott's data come from.
* The syllable count is recorded rather than read off the form, since a syllabic nasal, as in
  *mtu*, would need the phonology.

## References

* [T. Scott, *Two Types of Resumptive Pronouns in Swahili* (2021)][scott-2021]
-/

@[expose] public section

namespace Swahili

open Agreement Morphology

/-! ### The amba relative clause -/

/-- The complementizer *amba* with the relative concord of the head's class. A relativized
subject or direct object leaves a gap, and the verb agrees with both; the object of a
monosyllabic preposition is resumed by a pronoun suffixed to it. -/
def amba : Relativizer where
  form := "amba"
  placement := .postNominal
  realize
    | .subject | .directObject => {.gap}
    | .oblique => {.resumptive}
    | _ => ∅

/-- The relativizers. -/
def relativizers : List Relativizer := [amba]

/-! ### Pronouns -/

/-- The full personal pronouns. -/
def pronoun : Paradigm Morph :=
  [(.personNumber .first .singular, .free "mimi"), (.personNumber .second .singular, .free "wewe"),
    (.personNumber .third .singular, .free "yeye"), (.personNumber .first .plural, .free "sisi"),
    (.personNumber .second .plural, .free "nyinyi"), (.personNumber .third .plural, .free "wao")]

/-- The resumptive pronouns, suffixed to the monosyllabic preposition; they are also the
prepositional pronouns of matrix clauses, *ni-li-kutana na-ye* 'I met with her'. -/
def resumptive : Paradigm Morph :=
  [(.personNumber .first .singular, .suff "mi"), (.personNumber .second .singular, .suff "we"),
    (.personNumber .third .singular, .suff "ye"), (.personNumber .first .plural, .suff "si"),
    (.personNumber .second .plural, .suff "nyi"), (.personNumber .third .plural, .suff "o")]

/-- The relative concord of a class, the suffix of *amba* and the resumptive pronoun of a noun
of the class, for classes 1 to 10. -/
def NounClass.concord? : NounClass → Option Morph
  | .cl1 => some (.suff "ye")
  | .cl2 => some (.suff "o")
  | .cl3 => some (.suff "o")
  | .cl4 => some (.suff "yo")
  | .cl5 => some (.suff "lo")
  | .cl6 => some (.suff "yo")
  | .cl7 => some (.suff "cho")
  | .cl8 => some (.suff "vyo")
  | .cl9 => some (.suff "yo")
  | .cl10 => some (.suff "zo")
  | _ => none

/-- The third person resumptives are the concords of classes 1 and 2, the animate gender, and
so carry number and gender but no person. -/
theorem resumptive_third :
    resumptive.realize (.personNumber .third .singular) = Gender.genderA.singularClass.concord? ∧
      resumptive.realize (.personNumber .third .plural) = Gender.genderA.pluralClass.concord? :=
  ⟨rfl, rfl⟩

/-! ### Resumption and the minimal word -/

/-- A preposition or connective with its number of syllables, the size that decides whether
its object is resumed. -/
structure Preposition where
  /-- The form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The number of syllables. -/
  syllables : ℕ
  deriving DecidableEq, Repr

namespace Preposition

/-- *na* 'with, to, by'. -/
def na : Preposition := ⟨"na", "with, to, by", 1⟩

/-- The connective *ya* 'of', the class 9 concord on *-a*. -/
def ya : Preposition := ⟨"ya", "of", 1⟩

/-- The connective *mwa* 'in', the class 18 concord on *-a*. -/
def mwa : Preposition := ⟨"mwa", "in", 1⟩

/-- *katika* 'on, in'. -/
def katika : Preposition := ⟨"katika", "on, in", 3⟩

/-- A preposition's object is resumed when stranding the preposition would leave a word below
the two-unit minimum, that is, when the preposition is monosyllabic. -/
def TriggersResumption (p : Preposition) : Prop := p.syllables = 1

instance : DecidablePred TriggersResumption := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The monosyllables *na*, *ya* and *mwa* trigger resumption, and the trisyllable *katika*
does not, its object being relativized with the preposition dropped. -/
theorem triggersResumption :
    na.TriggersResumption ∧ ya.TriggersResumption ∧ mwa.TriggersResumption ∧
      ¬ katika.TriggersResumption := by
  decide

end Preposition

end Swahili
