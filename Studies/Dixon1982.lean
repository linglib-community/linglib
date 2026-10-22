module

public import Linglib.Semantics.Root.PropertyConcept
public import Linglib.Data.StructureDataset.Dixon1982
public import Linglib.Data.UD.UPOS

/-!
# Dixon (1982): Where have all the adjectives gone?

Dixon argues that the adjectives of a language draw on seven semantic types, and that where a
language's adjective class is small the types fall to its other parts of speech in a regular way.
In a language with a closed adjective class, age, dimension, value and colour stay adjectives,
human propensity goes to the nouns, and speed follows physical property. Table 2 records the parts
of speech of the seven types in seventeen languages, `Dixon1982.StructureDataset.table2`, and each
of Dixon's generalisations holds of it with exactly the exceptions stated here: those he lists,
and three he does not.

## Main definitions

* `Dixon1982.StructureDataset.PartOfSpeech.parts`: the basic parts of speech a code of Table 2
  involves.
* `Dixon1982.StructureDataset.Row.Takes`, `Dixon1982.StructureDataset.Row.Predominantly`: some,
  or more than a few, of a type's items are of a part of speech.
* `Dixon1982.openClass`, `Dixon1982.noClass`, `Dixon1982.closedClass`: the languages by their
  adjective class.

## Main results

* `exists_predominantly_iff`: a language with an open adjective class or none has one predominant
  part of speech for all seven types, except Tzotzil.
* `takes_adjective_iff`: (a), age, dimension, value and colour have adjectives in every
  closed-class language, except Bemba and Kiriwinian colour and Hua value.
* `predominantly_noun_iff`: (b), human propensity is mostly nouns, except in Alamblak and
  Kiriwinian.
* `takes_physicalProperty_of_humanPropensity`: (c), a closed class with a human-propensity
  adjective has a physical-property one, except in Sango.
* `speed_iff`: (d), speed shares a part of speech with physical property, or is an adverb where
  physical property is verbal, except in Kiriwinian.
* `pair_iff`: the A/V and N/V pairs of Table 2 are the strongly verbal languages, Hausa and
  Alamblak.

## Implementation notes

* A code's parts are the basic parts of speech it involves. A pair code such as `A/V` involves
  both members. A Sango adjunctive is an adjective when it modifies nouns, an adverb when it
  modifies verbs and a noun when it is a substantive, which is how Dixon reads the speed
  adjunctives for (d). A Hua verbalised noun is a verb on a noun root, and a Telugu `N-A` item a
  noun that also modifies.
* A code Table 2 qualifies with *some*, *one*, *two* or *few* is `minor`, and a type is
  predominantly of a part of speech when a code that is not minor involves it.
* The languages are classed by their adjective class as Dixon classes them in §1.4.3. He leaves
  Chinook out of that classification, and so do the theorems that depend on it.

## TODO

* (c) also says that the smaller the closed class the fewer its physical-property adjectives;
  Dixon gives the sizes only roughly, and this is not stated.
* The commentary gives Kiriwinian some physical-property verbs ('be strong', 'be weak', p. 43)
  that Table 2 does not list; as a minority they would leave (d) unchanged.
* The survey of twenty small adjective classes (§1.1) and the English criteria of Table 1 (§1.3)
  are not formalized.

## References

* [dixon-1982]
-/

@[expose] public section

namespace Dixon1982

open Semantics Data.StructureDataset UD

namespace StructureDataset

/-- The basic parts of speech a code of Table 2 involves. -/
def PartOfSpeech.parts : PartOfSpeech → List UPOS
  | .adjective => [.ADJ]
  | .noun => [.NOUN]
  | .verb => [.VERB]
  | .adverb => [.ADV]
  | .particle => [.PART]
  | .verbalisedNoun => [.NOUN, .VERB]
  | .nounAdjective => [.NOUN, .ADJ]
  | .adjunctiveN => [.ADJ]
  | .adjunctiveV => [.ADV]
  | .adjunctiveNVS => [.ADJ, .ADV, .NOUN]
  | .adjunctiveNS => [.ADJ, .NOUN]
  | .adjectiveVerb => [.ADJ, .VERB]
  | .nounVerb => [.NOUN, .VERB]
  | .adjectiveAdverb => [.ADJ, .ADV]
  | .nounAdverb => [.NOUN, .ADV]

namespace Row

variable (r : Row) (t : PropertyConcept.Class) (p : UPOS)

/-- The codes of a row for a semantic type. -/
def cell : PropertyConcept.Class → List (Coded PartOfSpeech)
  | .dimension => r.dimension
  | .physicalProperty => r.physicalProperty
  | .color => r.color
  | .humanPropensity => r.humanPropensity
  | .age => r.age
  | .value => r.value
  | .speed => r.speed

/-- Some of the language's items of the type are of the part of speech. -/
def Takes : Prop := ∃ v ∈ r.cell t, p ∈ v.code.parts

/-- More than a few of the language's items of the type are of the part of speech. -/
def Predominantly : Prop := ∃ v ∈ r.cell t, v.minor = false ∧ p ∈ v.code.parts

instance : Decidable (r.Takes t p) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (r.Predominantly t p) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

end Row

end StructureDataset

open StructureDataset

/-- The languages with an open adjective class (§1.4.3), Tzotzil only probably. -/
def openClass : List Language := [english, dyirbal, tzotzil]

/-- The languages with no adjective class, whose verbs take in the seven types (§1.4.3). -/
def noClass : List Language := [yurok, samoan]

/-- The languages with a small closed adjective class (§1.4.3). -/
def closedClass : List Language :=
  [swahili, luganda, bemba, japanese, sango, hausa, acooli, hua, alamblak, telugu, kiriwinian]

/-- A language with an open adjective class, or with none, has one part of speech that is
predominant in all seven types, except Tzotzil, most of whose human-propensity items are nouns
(pp. 43–44). Dixon does not count Tzotzil an exception. -/
theorem exists_predominantly_iff :
    ∀ r ∈ table2, r.language ∈ openClass ++ noClass →
      ((∃ p ∈ [UPOS.ADJ, .VERB], ∀ t, r.Predominantly t p) ↔
        r.language ≠ tzotzil) := by
  decide +kernel

/-- (a) Age, dimension, value and colour have adjectives in every language with a closed
adjective class, except Bemba and Kiriwinian colour, which are Dixon's exception (3), and Hua
value, which he does not list. -/
theorem takes_adjective_iff :
    ∀ r ∈ table2, r.language ∈ closedClass → ∀ t ∈ [PropertyConcept.Class.age, .dimension,
      .value, .color], (r.Takes t .ADJ ↔
        (r.language, t) ∉ [(bemba, .color), (kiriwinian, .color), (hua, .value)]) := by
  decide +kernel

/-- (b) Human propensity is predominantly nouns in a language with a closed adjective class,
except in Alamblak and Kiriwinian, the exceptions Dixon names. -/
theorem predominantly_noun_iff :
    ∀ r ∈ table2, r.language ∈ closedClass →
      (r.Predominantly .humanPropensity .NOUN ↔ r.language ∉ [alamblak, kiriwinian]) := by
  decide +kernel

/-- (c) An adjective class of a given size is more likely to include physical-property adjectives
than human-propensity ones: every closed class with a human-propensity adjective has a
physical-property adjective, except in Sango, whose one human-propensity adjunctive is
*buba* 'foolish' and whose adjunctives include no physical property (pp. 39, 48). -/
theorem takes_physicalProperty_of_humanPropensity :
    ∀ r ∈ table2, r.language ∈ closedClass → r.Takes .humanPropensity .ADJ →
      (r.Takes .physicalProperty .ADJ ↔ r.language ≠ sango) := by
  decide +kernel

/-- (d) Speed shares a part of speech with what physical property predominantly is, or is an
adverb where physical property is predominantly verbal, in every language of Table 2, Chinook
included, but Kiriwinian, which Dixon calls the only real exception (p. 48). -/
theorem speed_iff :
    ∀ r ∈ table2,
      ((∃ v ∈ r.speed, ∃ p ∈ v.code.parts, r.Predominantly .physicalProperty p) ∨
          (r.Takes .speed .ADV ∧ r.Predominantly .physicalProperty .VERB)) ↔
        r.language ≠ kiriwinian := by
  decide +kernel

/-- The A/V and N/V pairs, an adjective or noun for the unmarked member of an antonym pair and a
verb for the marked one, occur in Table 2 exactly in Hausa and Alamblak, Dixon's strongly verbal
languages (p. 51). -/
theorem pair_iff :
    ∀ r ∈ table2,
      (∃ t, ∃ v ∈ r.cell t, v.code = .adjectiveVerb ∨ v.code = .nounVerb) ↔
        r.language ∈ [hausa, alamblak] := by
  decide +kernel

end Dixon1982
