module

public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Syntax.Gender.Basic
public import Linglib.Morphology.Morph
public import Linglib.Fragments.Bantu.Params

/-!
# Swahili noun classes

This file defines the noun classes of Swahili, the genders that pair a singular class with its
plural, and the subject prefixes of the verb. A class is one of the Bantu classes in the
traditional numbering. A noun of a class carries its prefix, *ki-kapu* 'basket' in class 7 and
*vi-kapu* 'baskets' in class 8, and controls its agreement, the prefix *ki-* or *vi-* on the
adjective, the numeral and the verb. A controller gender is the pair of classes a noun takes
its agreements from, and Corbett's outline of the gender forms, after Welmers, gives the noun
prefixes and the verbal agreements of each. A verb agrees with its subject by a prefix, the
class prefix for a nominal subject and a person prefix for a speech-act participant. In the
negative indicative *ha-* precedes the subject prefix, changing in the three persons singular.

## Main definitions

* `Swahili.subjPrefix`, `Swahili.classes`: the subject prefix of each class and the classes
* `Swahili.Gender`, `Gender.singularClass`, `Gender.pluralClass`, `Gender.class`: the five
  genders as pairs of classes
* `Swahili.subjectPrefix`: the subject prefixes of the person cells, the third person those of
  classes 1 and 2
* `Swahili.negSubjPrefix`, `Swahili.negativeSubjectPrefix`: the negative subject
  prefixes of the classes and of the person cells

## Main results

* `Swahili.Gender.faithful_subjPrefix`: subject agreement distinguishes the five genders
* `Swahili.negativeSubjectPrefix_eq_iff`: a negative person prefix is *ha-* before the
  affirmative one exactly in the plural

## Implementation notes

* The numbering is Scott's, after Carstens, with the *u-* class as 14 and no class 11; Corbett
  and Welmers number that class 11 and pair it with class 10 as a gender of its own, and count
  the infinitive class 15 as a gender with no plural. Neither is among the five genders here,
  which are Scott's genders A to E.
* The class prefixes are the typical forms of Corbett's table: *m-* before a consonant and
  *mw-* before a vowel in classes 1 and 3, *ji-* or nothing in class 5, and a nasal that
  assimilates to the stem in classes 9 and 10.

## References

* [E. O. Ashton, *Swahili Grammar (Including Intonation)* (1947)][ashton-1947]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [T. Scott, *Two Types of Resumptive Pronouns in Swahili* (2021)][scott-2021]
-/

@[expose] public section

namespace Swahili

open Agreement Bantu Morphology

/-! ### Classes -/

/-- The subject prefix of a class on the verb, *m-* in class 18 before a consonant; Swahili has
no classes 11–13. -/
def subjPrefix : NounClass → Option Morph
  | .cl1 => some (.pref "a")    -- noun prefix m-, mw-: mtu 'person', mwalimu 'teacher'
  | .cl2 => some (.pref "wa")   -- wa-: watu 'people'
  | .cl3 => some (.pref "u")    -- m-, mw-: mti 'tree'
  | .cl4 => some (.pref "i")    -- mi-: miti 'trees'
  | .cl5 => some (.pref "li")   -- ji-, often absent: joka 'giant snake'
  | .cl6 => some (.pref "ya")   -- ma-: maji 'water'
  | .cl7 => some (.pref "ki")   -- ki-: kikapu 'basket'
  | .cl8 => some (.pref "vi")   -- vi-: vikapu 'baskets'
  | .cl9 => some (.pref "i")    -- a nasal: nyoka 'snake', nyumba 'house'
  | .cl10 => some (.pref "zi")  -- a nasal: nyumba 'houses'
  | .cl14 => some (.pref "u")   -- u-, the class Corbett and Welmers number 11
  | .cl15 => some (.pref "ku")  -- ku-, the infinitive: ku-la 'to eat'
  | .cl16 => some (.pref "pa")  -- definite place: hapa pa-na miti 'there are trees here'
  | .cl17 => some (.pref "ku")  -- indefinite place: nje ku-na watu 'there are people outside'
  | .cl18 => some (.pref "m")   -- area or withinness: kisima-ni m-na maji 'there is water in
                                -- the well'
  | _ => none

/-- The classes, those with a subject prefix. -/
def classes : Finset NounClass := Finset.univ.filter fun c ↦ (subjPrefix c).isSome

/-! ### Genders -/

/-- A controller gender pairs a singular class with its plural, in Scott's lettering. -/
inductive Gender where
  /-- Classes 1/2, the animates. -/
  | genderA
  /-- Classes 3/4. -/
  | genderB
  /-- Classes 5/6. -/
  | genderC
  /-- Classes 7/8. -/
  | genderD
  /-- Classes 9/10. -/
  | genderE
  deriving DecidableEq, Repr, Fintype

/-- The singular class of a gender. -/
def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9

/-- The plural class of a gender. -/
def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10

/-- Swahili distinguishes the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- The class of a gender in a number. -/
def Gender.class (g : Gender) : numberSystem.values → NounClass :=
  numberSystem.elim g.singularClass g.pluralClass

/-- Subject agreement, singular and plural, distinguishes the five genders. -/
theorem Gender.faithful_subjPrefix :
    Gender.Faithful fun (g : Gender) (n : numberSystem.values) ↦ subjPrefix (g.class n) := by
  decide

/-! ### Subject prefixes of the persons -/

/-- The subject prefixes of the person cells are *ni-*, *u-*, *tu-* and *m-* for the speech-act
participants and the prefixes of classes 1 and 2 for the third person. -/
def subjectPrefix : Paradigm Morph :=
  [(.personNumber .first .singular, .pref "ni"), (.personNumber .second .singular, .pref "u"),
    (.personNumber .third .singular, (subjPrefix .cl1).get rfl),
    (.personNumber .first .plural, .pref "tu"),
    (.personNumber .second .plural, .pref "m"),
    (.personNumber .third .plural, (subjPrefix .cl2).get rfl)]

/-! ### Negative subject prefixes -/

/-- The negative *ha-* of the indicative, prefixed to the subject prefix. -/
def ha : Morph := .pref "ha"

/-- The negative subject prefix of a class is *ha-* before its subject prefix, into which the
*a-* of class 1 is elided. -/
def negSubjPrefix : NounClass → Option (List Morph)
  | .cl1 => some [ha]
  | c => (subjPrefix c).map ([ha, ·])

/-- The negative subject prefixes of the person cells are *si-*, *hu-* and *ha-* in the
singular and *ha-* before *tu-*, *m-* and *wa-* in the plural. -/
def negativeSubjectPrefix : Paradigm (List Morph) :=
  [(.personNumber .first .singular, [.pref "si"]), (.personNumber .second .singular, [.pref "hu"]),
    (.personNumber .third .singular, (negSubjPrefix .cl1).get rfl),
    (.personNumber .first .plural, [ha, .pref "tu"]),
    (.personNumber .second .plural, [ha, .pref "m"]),
    (.personNumber .third .plural, (negSubjPrefix .cl2).get rfl)]

/-- A negative person prefix is *ha-* before the affirmative one exactly in the plural, the
three persons singular changing. -/
theorem negativeSubjectPrefix_eq_iff : ∀ c ∈ Bundle.personNumberCells,
    negativeSubjectPrefix.realize c = (subjectPrefix.realize c).map ([ha, ·]) ↔ c.IsPlural := by
  decide

end Swahili
