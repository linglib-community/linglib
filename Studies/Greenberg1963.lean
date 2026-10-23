module

public import Linglib.Data.WordOrder.Greenberg1963
public import Linglib.Syntax.WordOrder

/-!
# Greenberg (1963): Some Universals of Grammar

Greenberg's basic order typology classifies a language by its dominant order of nominal subject,
object and verb, by its prepositions or postpositions, and by the order of noun and adjective. Of
the six orders of subject, object and verb only the three in which the subject precedes the object
are common (Universal 1), and they are the paper's types I, II and III, verb-initial, verb-medial
and verb-final. This file states the implicational universals of order over the paper's own data:
the 30-language sample of Appendix I, extended by the per-language properties the text and its
footnotes record, and the 24 order types of Appendix II with the languages listed as attesting each
(`Data.WordOrder.Greenberg1963`). Each basic type is an arrangement of subject, object and verb,
and each adposition and each order of a noun and its dependent a head direction, so the harmony
universals are statements about `HeadDirection`: a verb-peripheral language's adposition is a head
in the verb's direction (Universals 3 and 4), and the noun's direction towards its genitive is the
adposition's (Universal 2).

## Main statements

* `subjectFirst_iff_mem_range`: the three basic types are exactly the subject-first orders, the
  typology Universal 1 leaves.
* `universal_3_4`: in the sample a verb-initial language is prepositional and a verb-final one
  postpositional, its adposition a head in the verb's direction.
* `universal_2`: the noun precedes or follows its genitive as the adposition precedes or follows
  its noun phrase, but in Norwegian, which has both genitive orders.
* `not_universal_23_as_printed`, `universal_23`: the data contradict Universal 23 as printed and
  bear it out with its genitive orders exchanged.

## Implementation notes

* A universal is a statement that every language of the sample with one property has another
  (`Universal`), and "almost always" and "with overwhelmingly more than chance frequency" are
  universals with the exceptions the paper names (`UniversalExcept`). Universals over the attested
  order types are `TypeUniversal`.
* The genitive column follows the text, every postpositional language preposing the genitive and
  every prepositional one postposing it but Norwegian, which the paper's additional note records
  with both orders. The demonstrative and numeral columns follow Appendix I, whose counts the
  printed Table 6 garbles (its NA column sums to 23 against the 19 of Table 5).
* Zapotec and Songhai, whose question particles follow more than one rule, carry none, as in
  Table 2.
* Universal 23 as printed pairs proper-noun-first apposition with a postposed genitive, as do the
  genitive rows of Table 9. The languages footnote 19 lists, with their genitive orders, Table 9's
  rows by basic type, and the text's assimilation of apposition to the genitive pair it with a
  preposed genitive, so the printed universal has the two genitive orders exchanged.

## TODO

Universals 6 to 8, 11, 13 to 15, 19, 20, 25, and 26 and the morphological universals 28 to 45
concern properties the appendices and footnotes do not record per language.

## References

* [greenberg-1963]
-/

@[expose] public section

namespace Greenberg1963

open Data.WordOrder Data.WordOrder.Greenberg1963 WordOrder

/-! ### The basic order typology -/

/-- The arrangement of subject, object and verb of a basic order type. The paper's types I, II and
III, named by the position of the verb, are verb-subject-object, subject-verb-object and
subject-object-verb. -/
def _root_.Data.WordOrder.VerbPosition.arrangement : VerbPosition → Arrangement Constituent 3
  | .initial => .vso
  | .medial => .svo
  | .final => .sov

theorem subjectFirst_iff_mem_range (a : Arrangement Constituent 3) :
    a.Precedes .subject .object ↔ a ∈ Set.range VerbPosition.arrangement := by
  revert a
  decide

/-- The basic order of a language of the sample. -/
abbrev _root_.Data.WordOrder.SampleRow.basicOrder (r : SampleRow) : Arrangement Constituent 3 :=
  r.verbPosition.arrangement

/-- The basic order of an order type. -/
abbrev _root_.Data.WordOrder.OrderType.basicOrder (t : OrderType) : Arrangement Constituent 3 :=
  t.verbPosition.arrangement

/-- An adposition is a head-initial preposition or a head-final postposition. -/
def _root_.Data.WordOrder.Adposition.headDirection : Adposition → HeadDirection
  | .prepositions => .headInitial
  | .postpositions => .headFinal

/-- The direction of a noun towards a dependent, when the language has one order of the two. -/
def _root_.Data.WordOrder.NounOrder.headDirection? : NounOrder → Option HeadDirection
  | .nounFirst => some .headInitial
  | .dependentFirst => some .headFinal
  | .both => none

/-! ### Universals over the sample -/

/-- A Greenbergian implicational universal over the sample, by which every language with `P` has
`Q`. -/
def Universal (P Q : SampleRow → Prop) : Prop := ∀ r ∈ sample, P r → Q r

instance (P Q : SampleRow → Prop) [DecidablePred P] [DecidablePred Q] :
    Decidable (Universal P Q) :=
  inferInstanceAs (Decidable (∀ r ∈ sample, P r → Q r))

/-- A universal holding but for the named languages, the paper's "almost always". -/
def UniversalExcept (P Q : SampleRow → Prop) (exceptions : List String) : Prop :=
  ∀ r ∈ sample, P r → Q r ∨ r.language ∈ exceptions

instance (P Q : SampleRow → Prop) (exceptions : List String) [DecidablePred P]
    [DecidablePred Q] : Decidable (UniversalExcept P Q exceptions) :=
  inferInstanceAs (Decidable (∀ r ∈ sample, P r → Q r ∨ r.language ∈ exceptions))

theorem universal_2 :
    UniversalExcept (fun _ ↦ True)
      (fun r ↦ r.genitive.headDirection? = some r.adposition.headDirection) ["Norwegian"] := by
  decide

theorem universal_3_4 (d : HeadDirection) :
    Universal (·.basicOrder.IsEnd .verb d) (·.adposition.headDirection = d) := by
  cases d <;> decide

/-- A question particle placed at the start of the sentence occurs in a prepositional language,
and one placed at its end in a postpositional language, Thai and Yoruba excepted (Universal 9,
Table 2). -/
theorem universal_9 :
    Universal (·.questionParticleSentence = some .initial) (·.adposition = .prepositions) ∧
      UniversalExcept (·.questionParticleSentence = some .final)
        (·.adposition = .postpositions) ["Thai", "Yoruba"] := by
  decide

theorem universal_10 :
    UniversalExcept (·.questionParticleWord ≠ none) (·.questionParticleWord = some .follows)
        ["Yoruba"] ∧
      Universal (·.questionParticleWord ≠ none) (¬ ·.basicOrder.IsInitial .verb) := by
  decide

/-- Verb-initial languages put the interrogative word first, and verb-final ones never do
(Universal 12, Table 3). -/
theorem universal_12 :
    Universal (·.basicOrder.IsInitial .verb) (·.questionWordFirst = true) ∧
      Universal (·.basicOrder.IsFinal .verb) (·.questionWordFirst = false) := by
  decide

/-- An inflected auxiliary precedes the main verb in a verb-initial language and follows it in a
verb-final one (Universal 16, Table 4). -/
theorem universal_16 :
    Universal (·.basicOrder.IsInitial .verb) (·.auxiliary ≠ some .follows) ∧
      Universal (·.basicOrder.IsFinal .verb) (·.auxiliary ≠ some .precedes) := by
  decide

/-- The verb-initial languages of the sample have the adjective after the noun (Universal 17,
Table 5). -/
theorem universal_17 :
    Universal (·.basicOrder.IsInitial .verb) (·.adjective.headDirection? = some .headInitial) := by
  decide

/-- When the adjective precedes the noun, so do the demonstrative and the numeral (Universal 18,
Table 6). -/
theorem universal_18 :
    Universal (·.adjective = .dependentFirst)
      (fun r ↦ r.demonstrative = .dependentFirst ∧ r.numeral = .dependentFirst) := by
  decide

/-- Where some or all adverbs follow the adjective, the adjective follows the noun and the verb
precedes its object (Universal 21, Table 7). -/
theorem universal_21 :
    Universal (fun r ↦ r.adverbAdjective = some .adjectiveAdverb ∨ r.adverbAdjective = some .both)
      (fun r ↦ r.adjective = .nounFirst ∧ r.basicOrder.Precedes .verb .object) := by
  decide

/-- Standard-marker-adjective, alone or as an alternative, goes with postpositions, and
adjective-marker-standard alone with prepositions, Songhai excepted (Universal 22, Table 8). -/
theorem universal_22 :
    Universal (fun r ↦ r.comparison = some .standardMarkerAdjective ∨ r.comparison = some .both)
        (·.adposition = .postpositions) ∧
      UniversalExcept (·.comparison = some .adjectiveMarkerStandard)
        (·.adposition = .prepositions) ["Songhai"] := by
  decide

theorem not_universal_23_as_printed :
    ¬ Universal (·.apposition = some .properCommon) (·.genitive = .nounFirst) := by
  decide

/-- Universal 23 with the genitive orders exchanged, as footnote 19 and the text's assimilation of
apposition to the genitive have it: the proper noun first goes with a preposed genitive, but in
Norwegian, which has both, and the common noun first with a postposed one, Guarani excepted. -/
theorem universal_23 :
    UniversalExcept (·.apposition = some .properCommon) (·.genitive = .dependentFirst)
        ["Norwegian"] ∧
      UniversalExcept (·.apposition = some .commonProper) (·.genitive = .nounFirst)
        ["Guarani"] := by
  decide

/-- A relative expression preceding the noun, alone or as an alternative, goes with
postpositions or a preposed adjective (Universal 24, Table 10). -/
theorem universal_24 :
    Universal (fun r ↦ r.relative = some .dependentFirst ∨ r.relative = some .both)
      (fun r ↦ r.adposition = .postpositions ∨ r.adjective = .dependentFirst) := by
  decide

/-- An exclusively suffixing language is postpositional, and an exclusively prefixing one
prepositional (Universal 27, Table 11). -/
theorem universal_27 :
    Universal (·.affixing = .suffixingOnly) (·.adposition = .postpositions) ∧
      Universal (·.affixing = .prefixingOnly) (·.adposition = .prepositions) := by
  decide

/-! ### Universals over the attested order types of Appendix II -/

/-- The order types the paper lists a language for. -/
def attested : List OrderType := types.filter (·.attested ≠ [])

/-- A universal over the attested types. -/
def TypeUniversal (P Q : OrderType → Prop) : Prop := ∀ t ∈ attested, P t → Q t

instance (P Q : OrderType → Prop) [DecidablePred P] [DecidablePred Q] :
    Decidable (TypeUniversal P Q) :=
  inferInstanceAs (Decidable (∀ t ∈ attested, P t → Q t))

theorem universal_2_types :
    TypeUniversal (fun t ↦ t.adposition = .prepositions ∧ t.genitive = .dependentFirst)
        (·.index ∈ [3, 11, 12, 19]) ∧
      TypeUniversal (fun t ↦ t.adposition = .postpositions ∧ t.genitive = .nounFirst)
        (·.index ∈ [14, 21]) := by
  decide

theorem universal_3_types :
    TypeUniversal (·.basicOrder.IsInitial .verb) (·.adposition = .prepositions) := by
  decide

theorem universal_4_types :
    TypeUniversal (fun t ↦ t.basicOrder.IsFinal .verb ∧ t.adposition = .prepositions)
      (·.index ∈ [17, 19]) := by
  decide

theorem universal_5_types :
    TypeUniversal (fun t ↦ t.basicOrder.IsFinal .verb ∧ t.genitive = .nounFirst)
      (·.adjective = .nounFirst) := by
  decide

theorem universal_17_types :
    TypeUniversal (fun t ↦ t.basicOrder.IsInitial .verb ∧ t.adjective = .dependentFirst)
      (·.index ∈ [2, 3]) := by
  decide

end Greenberg1963
