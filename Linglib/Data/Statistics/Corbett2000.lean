module

public import Linglib.Data.Statistics.Schema

/-!
# Corbett2000: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Corbett2000.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The counts and judgements of chapter 6: judgements on agreement with corporate nouns in three
varieties of English, plural agreement with corporate nouns in British newspaper texts, agreement
with honorific *vy* across the Slavonic languages, and number resolution with conjoined noun phrases
by target and by controller.

## References

* [corbett-2000]
-/

@[expose] public section

namespace Corbett2000

open Data.Statistics

/-- The varieties of English of Table 6.10. -/
inductive Variety where
  /-- GB: British English -/
  | gb
  /-- US: American English -/
  | us
  /-- NZ: New Zealand English -/
  | nz
  deriving DecidableEq, Repr, Fintype

/-- The responses to *The audience were enjoying every minute of the show*. -/
inductive Response where
  /-- no correction: the sentence is left as given -/
  | noCorrection
  /-- was enjoying: the verb is corrected to the singular -/
  | wasEnjoying
  /-- other response: any other correction -/
  | other
  deriving DecidableEq, Repr, Fintype

/-- The agreement targets counted with corporate nouns in a corpus of British newspaper texts. -/
inductive CorporateTarget where
  /-- predicate: the predicate -/
  | predicate
  /-- pronoun: the personal and the possessive pronoun together -/
  | pronoun
  deriving DecidableEq, Repr, Fintype

/-- A cell of Table 6.11: lower case is syntactic (plural) agreement, upper case semantic
(singular) agreement, and parentheses mark the less frequent or less preferred variant. -/
inductive Mark where
  /-- pl: plural only -/
  | pl
  /-- pl/(SG): plural, the singular less preferred -/
  | plRarelySg
  /-- pl/SG: plural or singular -/
  | either
  /-- (pl)/SG: singular, the plural less preferred -/
  | sgRarelyPl
  /-- SG: singular only -/
  | sg
  deriving DecidableEq, Repr, Fintype

/-- The rows of Table 6.11, Russian once for each form of its adjective. -/
inductive Slavonic where
  /-- Czech: West Slavonic -/
  | czech
  /-- Slovak: West Slavonic -/
  | slovak
  /-- Lower Sorbian: West Slavonic -/
  | lowerSorbian
  /-- Upper Sorbian: West Slavonic -/
  | upperSorbian
  /-- Polish dialects: West Slavonic -/
  | polishDialects
  /-- Bulgarian: South Slavonic -/
  | bulgarian
  /-- Macedonian: South Slavonic -/
  | macedonian
  /-- Serbo-Croat: South Slavonic -/
  | serboCroat
  /-- Slovene: South Slavonic -/
  | slovene
  /-- Ukrainian: East Slavonic -/
  | ukrainian
  /-- Belarusian: East Slavonic -/
  | belarusian
  /-- Russian, short form: East Slavonic, the adjective in its short form -/
  | russianShort
  /-- Russian, long form: East Slavonic, the adjective in its long form -/
  | russianLong
  deriving DecidableEq, Repr, Fintype

/-- The positions of the Agreement Hierarchy. -/
inductive Target where
  /-- attributive: the attributive modifier -/
  | attributive
  /-- predicate: the predicate -/
  | predicate
  /-- relative pronoun: the relative pronoun -/
  | relativePronoun
  /-- personal pronoun: the personal pronoun -/
  | personalPronoun
  deriving DecidableEq, Repr, Fintype

/-- The languages of Table 6.13. -/
inductive ConjoinedLanguage where
  /-- Medieval Spanish: texts of the thirteenth to fifteenth centuries -/
  | medievalSpanish
  /-- German: German -/
  | german
  /-- Russian: Russian -/
  | russian
  /-- Serbo-Croat: modern literary texts -/
  | serboCroat
  deriving DecidableEq, Repr, Fintype

/-- The order of the conjoined subject and its predicate. -/
inductive Order where
  /-- subject–predicate: the subject precedes the predicate -/
  | subjectPredicate
  /-- predicate–subject: the predicate precedes the subject -/
  | predicateSubject
  deriving DecidableEq, Repr, Fintype

/-- The animacy of the conjuncts. -/
inductive Animacy where
  /-- animate: the conjuncts denote animates -/
  | animate
  /-- inanimate: the conjuncts denote inanimates -/
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 6.10: the percentage of respondents of a variety giving a response to the test
sentence. -/
structure Judgement where
  /-- The percentage of respondents. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 6.10, by variety and response; from a sociolinguistic survey; checked
against the page images. -/
def judgement : Variety → Response → Judgement
  | .gb, .noCorrection => ⟨⟨772, 1⟩⟩
  | .gb, .wasEnjoying => ⟨⟨152, 1⟩⟩
  | .gb, .other => ⟨⟨76, 1⟩⟩
  | .us, .noCorrection => ⟨⟨54, 1⟩⟩
  | .us, .wasEnjoying => ⟨⟨903, 1⟩⟩
  | .us, .other => ⟨⟨43, 1⟩⟩
  | .nz, .noCorrection => ⟨⟨725, 1⟩⟩
  | .nz, .wasEnjoying => ⟨⟨206, 1⟩⟩
  | .nz, .other => ⟨⟨69, 1⟩⟩

/-- A row of Table 6.10: the number of respondents of a variety. -/
structure Respondents where
  /-- The number of respondents. -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 6.10, by variety; from a sociolinguistic survey; checked against the page
images. -/
def respondents : Variety → Respondents
  | .gb => ⟨92⟩
  | .us => ⟨93⟩
  | .nz => ⟨102⟩

/-- A row of section 6.2: plural agreement with corporate nouns at a target, in a corpus of
British newspaper texts. -/
structure Corporate where
  /-- The number of examples. -/
  n : ℕ
  /-- The percentage with plural agreement. -/
  percentPlural : Decimal
  deriving DecidableEq, Repr

/-- The cells of section 6.2, by target; counted in a corpus; checked against the PDF text layer
only. -/
def corporate : CorporateTarget → Corporate
  | .predicate => ⟨181, ⟨122, 1⟩⟩
  | .pronoun => ⟨106, ⟨274, 1⟩⟩

/-- A row of Table 6.11: agreement with honorific *vy* in a Slavonic language, at each sub-
position of the predicate. -/
structure Honorific where
  /-- The finite verb. -/
  finiteVerb : Mark
  /-- The participle. -/
  participle : Mark
  /-- The adjective. -/
  adjective : Mark
  /-- The noun. -/
  noun : Mark
  /-- The percentage of the participle's mark, where the table prints one. -/
  participlePercent : Option Decimal
  /-- The number of examples behind it. -/
  participleN : Option ℕ
  /-- The percentage of the adjective's mark, where the table prints one. -/
  adjectivePercent : Option Decimal
  /-- The number of examples behind it. -/
  adjectiveN : Option ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 6.11, by language; counted in a corpus; checked against the page images. -/
def honorific : Slavonic → Honorific
  | .czech => ⟨.pl, .sgRarelyPl, .sgRarelyPl, .sg, none, none, none, none⟩
  | .slovak => ⟨.pl, .plRarelySg, .sg, .sg, none, none, none, none⟩
  | .lowerSorbian => ⟨.pl, .pl, .either, .sg, none, none, none, none⟩
  | .upperSorbian => ⟨.pl, .sgRarelyPl, .sgRarelyPl, .sg, none, none, none, none⟩
  | .polishDialects => ⟨.pl, .either, .either, .sg, none, none, none, none⟩
  | .bulgarian => ⟨.pl, .pl, .sg, .sg, some ⟨96, 0⟩, some 167, some ⟨97, 0⟩, some 163⟩
  | .macedonian => ⟨.pl, .pl, .sgRarelyPl, .sg, none, none, none, none⟩
  | .serboCroat => ⟨.pl, .pl, .plRarelySg, .sg, none, none, none, none⟩
  | .slovene => ⟨.pl, .plRarelySg, .plRarelySg, .sg, none, none, none, none⟩
  | .ukrainian => ⟨.pl, .plRarelySg, .sgRarelyPl, .sg, none, none, none, none⟩
  | .belarusian => ⟨.pl, .pl, .sg, .sg, none, none, none, none⟩
  | .russianShort => ⟨.pl, .pl, .pl, .sg, none, none, some ⟨97, 0⟩, some 145⟩
  | .russianLong => ⟨.pl, .pl, .sg, .sg, none, none, some ⟨89, 0⟩, some 37⟩

/-- A row of Table 6.12: number resolution with conjoined noun phrases at a target in modern
literary Russian. -/
structure RussianConjoined where
  /-- The number of examples. -/
  n : ℕ
  /-- The percentage with number resolution. -/
  percentPlural : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 6.12, by target; counted in a corpus; checked against the page images. -/
def russianConjoined : Target → RussianConjoined
  | .attributive => ⟨34, ⟨12, 0⟩⟩
  | .predicate => ⟨230, ⟨70, 0⟩⟩
  | .relativePronoun => ⟨10, ⟨100, 0⟩⟩
  | .personalPronoun => ⟨26, ⟨100, 0⟩⟩

/-- A row of Table 6.13: plural predicates with conjoined subjects, by the animacy of the
conjuncts and their order relative to the predicate. -/
structure Resolution where
  /-- The number of examples. -/
  n : ℕ
  /-- The percentage with a plural predicate. -/
  percentPlural : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 6.13, by language and order and animacy; counted in a corpus; checked
against the page images. -/
def resolution : ConjoinedLanguage → Order → Animacy → Resolution
  | .medievalSpanish, .subjectPredicate, .animate => ⟨288, ⟨96, 0⟩⟩
  | .medievalSpanish, .subjectPredicate, .inanimate => ⟨243, ⟨31, 0⟩⟩
  | .german, .subjectPredicate, .animate => ⟨1095, ⟨96, 0⟩⟩
  | .german, .subjectPredicate, .inanimate => ⟨1702, ⟨67, 0⟩⟩
  | .russian, .subjectPredicate, .animate => ⟨115, ⟨100, 0⟩⟩
  | .russian, .subjectPredicate, .inanimate => ⟨67, ⟨85, 0⟩⟩
  | .serboCroat, .subjectPredicate, .animate => ⟨21, ⟨100, 0⟩⟩
  | .serboCroat, .subjectPredicate, .inanimate => ⟨35, ⟨91, 0⟩⟩
  | .medievalSpanish, .predicateSubject, .animate => ⟨318, ⟨69, 0⟩⟩
  | .medievalSpanish, .predicateSubject, .inanimate => ⟨239, ⟨6, 0⟩⟩
  | .german, .predicateSubject, .animate => ⟨379, ⟨93, 0⟩⟩
  | .german, .predicateSubject, .inanimate => ⟨925, ⟨40, 0⟩⟩
  | .russian, .predicateSubject, .animate => ⟨89, ⟨84, 0⟩⟩
  | .russian, .predicateSubject, .inanimate => ⟨114, ⟨28, 0⟩⟩
  | .serboCroat, .predicateSubject, .animate => ⟨23, ⟨70, 0⟩⟩
  | .serboCroat, .predicateSubject, .inanimate => ⟨62, ⟨26, 0⟩⟩

end Corbett2000
