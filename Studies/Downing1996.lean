module

public import Linglib.Fragments.Japanese.Nouns
public import Linglib.Data.Examples.Downing1996

/-!
# Downing (1996): Numeral Classifier Systems: The Case of Japanese

This file formalizes the semantic and pragmatic analysis of the Japanese numeral classifier system
in [downing-1996]. A numeral classifier is a form that follows a numeral, readily co-occurs with a
noun denoting the enumerated referent, and denotes a natural unit of that referent whose
characteristics dictate its choice, which excludes standard measures, containers, partitions and
groupings (Chapter 1); the core inventory of Table 1.1 and the extended inventory of Table 1.2 are
`Row`, each row's entry a classifier of `Japanese.Classifiers`. The monograph evaluates two
universalist hypotheses (Chapter 5). Hypothesis 1, after [denny-1976], is that classifiers encode
categories defined by parameters of physical, functional and social interaction, `Interaction`, and
the core inventory conforms to this extent, `core_interaction`, though the monograph finds the
system adulterated with categories of little cultural weight. Hypothesis 2 is that classifiers
supplement the information carried by nouns; the capacity lies with the quality-classifiers, whose
deductive categories in the sense of [hunn-1977] are united by one or two physical properties and
crosscut noun categories, against the kind-classifiers of inductive categories, `cohesion`, the
animal and boat categories being inductive categories split by the deductive parameter of size,
`sizeSplits`. The morphemes serving as classifiers mostly bear independent senses related to their
categories along the six recurrent patterns of Table 5.2, `MorphemeRelation`; a seventh pattern
attested in other languages is absent from Japanese, `relation_ne_sharedQuality`, only the pairs of
the first pattern are clones of noun categories, and no quality-classifier is one,
`quality_not_clone`. Chapter 7 reconsiders [sanches-slobin-1973]'s universal that classifier
languages lack obligatory plural marking and [greenberg-1972]'s collective/singulative rationale for
it: Japanese common nouns are transnumeral and its pronouns and proper nouns inherently singular,
`numberSystem`, so plural marking is required on the latter and at most possible on the former,
Table 7.2, `pluralMarking`, and is monotone in the animacy of the referent and the referentiality of
the noun phrase, `pluralMarking_mono_referent` and `pluralMarking_mono_head`, a plurality split in
the sense of [smith-stark-1974]; the same suffixes read as associative plurals on the singular heads
and as class plurals on the transnumeral ones, `reading`. Classifier phrases unitize and plural
markers maintain tracking-worthy individuals, so a group is introduced with the former and tracked
with the latter and never the reverse, `Tracks`. The anaphoric use of classifier phrases (Chapter 6)
and the four positions of the classifier phrase (Chapter 8) are represented by their examples.

## Implementation notes

The kind/quality distinction is derived from the semantic parameters of each row's category, coded
in Aikhenvald's vocabulary from the descriptions of the tables (`Row.params`): a parameter of
physical interaction, including [allan-1977]'s quanta, is deductive, one of functional or social
interaction inductive, and a classifier is a quality-classifier when its parameters are all
deductive, a kind-classifier when all inductive, mixed when both, and general when it has none. The
morpheme-category relations of Table 5.2 are recorded for the rows the monograph assigns; the rows
it does not discuss are `none`, as are `mai` and `tsu`, which have no independent sense. Table 7.2
is the function `pluralMarking` and its regularities are proved by `decide` over the nine cells. The
frequency, breadth, acquisition, anaphoric-distance and construction-distribution counts of Chapters
3, 6 and 8 are corpus statistics and are not represented, nor are the taxonomic analyses of Chapter
4 or the history of Chapter 2.

## References

* [downing-1996]
* [denny-1976]
* [hunn-1977]
* [adams-conklin-1973]
* [allan-1977]
* [sanches-slobin-1973]
* [greenberg-1972]
* [smith-stark-1974]
* [martin-1975]
-/

@[expose] public section

namespace Downing1996

/-! ### The inventory, Tables 1.1 and 1.2 -/

/-- The classifiers of the questionnaire, the twenty-seven every respondent used (Table 1.1) and
the six a majority used (Table 1.2). -/
inductive Row where
  | tsu | nin | mei | hiki | tou | hon | mai | ko | satsu | tsubu | dai | kenBuilding
  | kenIncident | ki | ku | kyoku | mon | mune | seki | soku | soo | ten | toori | tsuu | kabu
  | shoku | teki | sao | wa | furi | zen | kyaku | rin
  deriving DecidableEq, Repr, Fintype

namespace Row

/-- The fragment's entry for the row. -/
def entry : Row → Classifier
  | .tsu => Japanese.Classifiers.tsu
  | .nin => Japanese.Classifiers.nin
  | .mei => Japanese.Classifiers.mei
  | .hiki => Japanese.Classifiers.hiki
  | .tou => Japanese.Classifiers.tou
  | .hon => Japanese.Classifiers.hon
  | .mai => Japanese.Classifiers.mai
  | .ko => Japanese.Classifiers.ko
  | .satsu => Japanese.Classifiers.satsu
  | .tsubu => Japanese.Classifiers.tsubu
  | .dai => Japanese.Classifiers.dai
  | .kenBuilding => Japanese.Classifiers.kenBuilding
  | .kenIncident => Japanese.Classifiers.kenIncident
  | .ki => Japanese.Classifiers.ki
  | .ku => Japanese.Classifiers.ku
  | .kyoku => Japanese.Classifiers.kyoku
  | .mon => Japanese.Classifiers.mon
  | .mune => Japanese.Classifiers.mune
  | .seki => Japanese.Classifiers.seki
  | .soku => Japanese.Classifiers.soku
  | .soo => Japanese.Classifiers.soo
  | .ten => Japanese.Classifiers.ten
  | .toori => Japanese.Classifiers.toori
  | .tsuu => Japanese.Classifiers.tsuu
  | .kabu => Japanese.Classifiers.kabu
  | .shoku => Japanese.Classifiers.shoku
  | .teki => Japanese.Classifiers.teki
  | .sao => Japanese.Classifiers.sao
  | .wa => Japanese.Classifiers.wa
  | .furi => Japanese.Classifiers.furi
  | .zen => Japanese.Classifiers.zen
  | .kyaku => Japanese.Classifiers.kyaku
  | .rin => Japanese.Classifiers.rin

/-- The twenty-seven classifiers every respondent used. -/
def core : List Row :=
  [.tsu, .nin, .mei, .hiki, .tou, .hon, .mai, .ko, .satsu, .tsubu, .dai, .kenBuilding,
    .kenIncident, .ki, .ku, .kyoku, .mon, .mune, .seki, .soku, .soo, .ten, .toori, .tsuu, .kabu,
    .shoku, .teki]

/-- The six further classifiers a majority of respondents used. -/
def extended : List Row := [.sao, .wa, .furi, .zen, .kyaku, .rin]

/-- The semantic parameters of the category each classifier names, coded in Aikhenvald's
vocabulary from the descriptions of the tables; the general *-tsu* has none. -/
def params : Row → List Classifier.Parameter
  | .tsu => []
  | .nin => [.humanness]
  | .mei => [.humanness, .register]
  | .hiki => [.animacy, .size]
  | .tou => [.animacy, .size]
  | .hon => [.shape]
  | .mai => [.shape]
  | .ko => [.shape]
  | .satsu => [.shape]
  | .tsubu => [.shape]
  | .dai => [.function]
  | .kenBuilding => [.function]
  | .kenIncident => [.function]
  | .ki => [.function]
  | .ku => [.function]
  | .kyoku => [.function]
  | .mon => [.function]
  | .mune => [.function]
  | .seki => [.function, .size]
  | .soku => [.function, .arrangement]
  | .soo => [.function, .size]
  | .ten => [.function]
  | .toori => [.function]
  | .tsuu => [.function]
  | .kabu => [.function]
  | .shoku => [.quanta]
  | .teki => [.quanta]
  | .sao => [.shape]
  | .wa => [.animacy]
  | .furi => [.function]
  | .zen => [.function]
  | .kyaku => [.function]
  | .rin => [.shape, .boundedness]

theorem params_eq_nil_iff (r : Row) : r.params = [] ↔ r = .tsu := by cases r <;> decide

end Row

/-! ### Interaction parameters, Hypothesis 1 -/

/-- The three kinds of human interaction by which [denny-1976] has classifier categories
defined. -/
inductive Interaction
  | physical
  | functional
  | social
  deriving DecidableEq, Repr

/-- The interaction a semantic parameter reflects: physical for the perceptual parameters,
[allan-1977]'s primary qualities, functional for use, and social for animacy and status;
colour, which no classifier system encodes, reflects none. -/
def interaction : Classifier.Parameter → Option Interaction
  | .shape | .size | .consistency | .constitution | .material | .arrangement | .boundedness
  | .interioricity | .direction | .nature | .quanta => some .physical
  | .function => some .functional
  | .animacy | .humanness | .sex | .socialStatus | .kinship | .register => some .social
  | .colour => none

/-- Hypothesis 1 on the core inventory: every core classifier but the general `tsu` encodes
a parameter of physical, functional or social interaction. -/
theorem core_interaction :
    ∀ r ∈ Row.core, r ≠ .tsu → ∃ p ∈ r.params, (interaction p).isSome := by
  decide

/-! ### Kind-classifiers and quality-classifiers, Chapter 3 -/

/-- A deductive parameter unites a category by a single perceptual property. -/
def Deductive (p : Classifier.Parameter) : Prop := interaction p = some .physical

/-- An inductive parameter names a category given by the world as humans use it. -/
def Inductive (p : Classifier.Parameter) : Prop :=
  interaction p = some .functional ∨ interaction p = some .social

instance : DecidablePred Deductive := fun p ↦ by unfold Deductive; infer_instance

instance : DecidablePred Inductive := fun p ↦ by unfold Inductive; infer_instance

/-- The type of semantic cohesion of a classifier's category. -/
inductive Cohesion
  | general
  | kind
  | quality
  | mixed
  deriving DecidableEq, Repr

/-- The cohesion of a classifier's category, read off its parameters: kind when all are
inductive, quality when all are deductive, mixed when both kinds occur, and general when it
has none. -/
def cohesion (r : Row) : Cohesion :=
  match r.params.any (decide <| Inductive ·), r.params.any (decide <| Deductive ·) with
  | false, false => .general
  | true, false => .kind
  | false, true => .quality
  | true, true => .mixed

theorem cohesion_shape_kind :
    cohesion .hon = .quality ∧ cohesion .mai = .quality ∧ cohesion .ko = .quality ∧
      cohesion .tsubu = .quality ∧ cohesion .nin = .kind ∧ cohesion .kenBuilding = .kind ∧
      cohesion .tsu = .general := by
  decide

/-- The pairs of core classifiers splitting one inductive category by size. -/
def sizeSplits : List (Row × Row) :=
  (Row.core.product Row.core).filter fun (r, r') ↦
    r ≠ r' ∧ cohesion r = .mixed ∧ r.params = r'.params ∧ .size ∈ r.params

theorem sizeSplits_eq :
    sizeSplits = [(.hiki, .tou), (.tou, .hiki), (.seki, .soo), (.soo, .seki)] := by
  decide

/-! ### The classifier and noun systems, Hypothesis 2 -/

/-- The recurrent relations between a classifier's category and the independent sense of
its morpheme, Table 5.2: the six patterns of Japanese, the seventh found in other
languages, and the metonymic and metaphoric extensions of (4) and (5). -/
inductive MorphemeRelation
  | identicalClass
  | partOfMembers
  | associatedAction
  | exemplar
  | creationAction
  | beneficiaryGoal
  | sharedQuality
  | metonymic
  | metaphoric
  deriving DecidableEq, Repr

/-- The relation the monograph assigns to the fragment's entries, `none` for the entries it
does not discuss and for `mai` and `tsu`, which are confined to classifier use. -/
def relation : Row → Option MorphemeRelation
  | .nin => some .identicalClass -- 'person', (3)
  | .kenIncident => some .identicalClass -- 'matter, case'
  | .ki => some .identicalClass -- 'machine'
  | .tou => some .partOfMembers -- 'head'
  | .kyaku => some .partOfMembers -- 'leg'
  | .tsuu => some .associatedAction -- 'to pass'
  | .furi => some .associatedAction -- 'to shake'
  | .soku => some .beneficiaryGoal -- 'foot'
  | .zen => some .metonymic -- 'tray', (4a)
  | _ => none

theorem relation_ne_sharedQuality : ∀ c, relation c ≠ some .sharedQuality := by decide

theorem quality_not_clone : ∀ c, cohesion c = .quality → relation c ≠ some .identicalClass := by
  decide

/-! ### Plural markers and classifier phrases as individuators, Chapter 7

Number is not an obligatory category of Japanese, and [martin-1975]'s six devices for
expressing it all carry other information; the classifier phrase and the plural suffixes
*-tachi*, *-ra* share the task of individuating referents, (2). -/

/-- The type of referent, in the order of the animacy hierarchy. -/
inductive ReferentType
  | inanimate
  | animate
  | human
  deriving DecidableEq, Repr, Fintype

/-- The head of the noun phrase, in the order of its referentiality. -/
inductive NPHead
  | commonNoun
  | properNoun
  | pronoun
  deriving DecidableEq, Repr, Fintype

/-- The availability of a plural marker, from impossible to required. -/
inductive Availability
  | impossible
  | rare
  | possible
  | required
  deriving DecidableEq, Repr, Fintype

def ReferentType.rank : ReferentType → ℕ
  | .inanimate => 0
  | .animate => 1
  | .human => 2

def NPHead.rank : NPHead → ℕ
  | .commonNoun => 0
  | .properNoun => 1
  | .pronoun => 2

def Availability.rank : Availability → ℕ
  | .impossible => 0
  | .rare => 1
  | .possible => 2
  | .required => 3

instance : LinearOrder ReferentType :=
  LinearOrder.lift' ReferentType.rank fun a b h ↦ by
    cases a <;> cases b <;> simp_all [ReferentType.rank]

instance : LinearOrder NPHead :=
  LinearOrder.lift' NPHead.rank fun a b h ↦ by cases a <;> cases b <;> simp_all [NPHead.rank]

instance : LinearOrder Availability :=
  LinearOrder.lift' Availability.rank fun a b h ↦ by
    cases a <;> cases b <;> simp_all [Availability.rank]

/-- Table 7.2: the availability of a plural marker by the type of the referent and the head
of the noun phrase. -/
def pluralMarking : ReferentType → NPHead → Availability
  | _, .pronoun => .required
  | .human, .properNoun => .required
  | .human, .commonNoun => .possible
  | .animate, _ => .rare
  | .inanimate, _ => .impossible

/-- Pronouns require a plural marker to refer to more than one individual, (10c). -/
theorem pluralMarking_pronoun (r : ReferentType) : pluralMarking r .pronoun = .required := by
  cases r <;> rfl

/-- Common nouns with inanimate referents reject plural markers, (8a) and (9b). -/
theorem pluralMarking_inanimate (h : NPHead) (hh : h ≠ .pronoun) :
    pluralMarking .inanimate h = .impossible := by
  cases h <;> first | rfl | exact absurd rfl hh

theorem pluralMarking_mono_referent (h : NPHead) : Monotone (pluralMarking · h) := by
  unfold Monotone
  decide +revert

theorem pluralMarking_mono_head (r : ReferentType) : Monotone (pluralMarking r) := by
  unfold Monotone
  decide +revert

/-- The number system of a noun phrase head: common nouns are transnumeral, denoting the
concept rather than individuals, while pronouns and proper nouns are inherently singular. -/
inductive NumberSystem
  | transnumeral
  | singularPlural
  deriving DecidableEq, Repr

def numberSystem : NPHead → NumberSystem
  | .commonNoun => .transnumeral
  | _ => .singularPlural

theorem required_iff_singularPlural (h : NPHead) :
    pluralMarking .human h = .required ↔ numberSystem h = .singularPlural := by
  cases h <;> decide

/-- What a plural suffix denotes: a group centred on the referent of its host, or a
plurality of members of the host's category. -/
inductive PluralReading
  | associative
  | classPlural
  deriving DecidableEq, Repr

/-- *-tachi* and *-ra* are associative on pronouns and proper nouns, (11), and class plurals
on common nouns, (12). -/
def reading : NPHead → PluralReading
  | .commonNoun => .classPlural
  | _ => .associative

theorem reading_classPlural_iff (h : NPHead) :
    reading h = .classPlural ↔ numberSystem h = .transnumeral := by
  cases h <;> decide

/-- Against the hypothesis that classifiers and plural morphemes are in complementary
distribution: the lexicon pairs a plural form and a classifier with one noun, as in (2b). -/
theorem plural_and_classifier :
    ∃ n : Japanese.Nouns.Noun, n.plural.isSome ∧ n.classifiers.Nonempty :=
  ⟨Japanese.Nouns.hito, rfl, ⟨_, Finset.mem_singleton_self _⟩⟩

/-- The devices by which a mention of a group of referents marks their number. -/
inductive Mention
  | classifierPhrase
  | bare
  | pluralMarked
  deriving DecidableEq, Repr

/-- A sequence of mentions of one group tracks it when no plural-marked mention precedes a
classifier phrase: the classifier phrase unitizes on introduction and the plural marker
maintains the individuated status, (16) and (23), and the reverse order is unattested. -/
def Tracks (s : List Mention) : Prop :=
  s.Pairwise fun a b ↦ ¬ (a = .pluralMarked ∧ b = .classifierPhrase)

instance : DecidablePred Tracks := fun s ↦ by unfold Tracks; infer_instance

/-- The sequence of (16), a classifier phrase followed by plural-marked mentions, tracks, and
its reverse does not. -/
theorem tracks_16 :
    Tracks [.classifierPhrase, .pluralMarked, .pluralMarked] ∧
      ¬ Tracks [.pluralMarked, .classifierPhrase] := by
  decide

end Downing1996
