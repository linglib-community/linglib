module

public import Linglib.Fragments.Japanese.Nouns
public import Linglib.Fragments.Japanese.Pronouns
public import Studies.GundelHedbergZacharski1993
public import Linglib.Data.Examples.Downing1996
public import Linglib.Data.Examples.Readers

/-!
# Downing (1996): Numeral Classifier Systems: The Case of Japanese

[downing-1996] divides the Japanese numeral classifiers into kind-classifiers, whose inductive
categories are given by the world and often clone noun categories, and quality-classifiers, whose
deductive categories rest on one or two physical properties. Read off the parameters of each
category, the division [matches her labels](##cohesion_eq_label), and Denny's hypothesis [holds of
the classifiers she cites for it](##params_toClass). The plural suffixes *-tachi* and *-ra* are
not facultative: their use [rises with animacy and referentiality](##pluralMarking_monotone), [as
her judgments bear out](##plural_rows), and since they mark individuals the hearer can identify,
[no new group is introduced with them](##licensed_cons_iff).

## Implementation notes

The semantic parameters of each category are coded here in the vocabulary of `Classifier.Parameter`
from the referent classes of the inventory tables. The coding is the formalization's, and it answers
to Downing three times: to the kind and quality labels she prints beside her examples of
disambiguation, to her sorting of classifiers by Denny's three kinds of interaction, and to the
animacy of the nouns the fragment counts with each classifier. A parameter is deductive when it is
a physical property; an inherent nature, which a classifier specific to one kind of noun encodes,
is not, so *-rin* 'flowers' and *-kabu* 'rooted plants' are kind-classifiers. The coding is keyed by
the fragment's classifier entries, and the examples are linked to the fragments by typed lists, of
classifiers and of noun-phrase heads with the animacy of their groups; no row feature feeds a
prediction, and the printed labels are read only as the targets of the cohesion check. About a
dozen codings, among them *-ten*, *-shoku* and *-kabu*, meet none of these checks. The corpus
counts of Chapters 3, 6 and 8, the taxonomies of Chapter 4, the history of Chapter 2 and the
positions of the classifier phrase in Chapter 8 are not represented.

## TODO

Downing's claim that only quality-classifiers serve as modifiers, adding information a noun does
not carry, needs the conventional classifiers of the nouns concerned in the fragment; one of her
examples uses *-ten*, which the coding makes a kind-classifier. Her estimate that deductive forms
are under a quarter of the core and extended inventories needs the whole extended inventory.

## References

* [downing-1996]
* [denny-1976]
* [hunn-1977]
* [allan-1977]
* [sanches-slobin-1973]
* [greenberg-1972]
* [smith-stark-1974]
* [lambrecht-1994]
* [gundel-hedberg-zacharski-1993]
-/

@[expose] public section

namespace Downing1996

open Classifier (Parameter)

/-! ### The inventory -/

open Japanese.Classifiers in
/-- The core inventory of Table 1.1, the twenty-six classifiers every respondent of the
questionnaire used and the general *-tsu*, left off it, each with the semantic parameters of its
category. The parameters are coded from the referent classes of the table: *-shoku* by the use of
a meal, *-soku* by the pair of footwear it counts, a quantity of a kind ((13) of Chapter 1), and
*-kabu* 'rooted plants' by the inherent nature of its members. -/
def core : List (Classifier × List Parameter) :=
  [(tsu, []), (nin, [.humanness]), (mei, [.humanness, .register]), (hiki, [.animacy, .size]),
    (tou, [.animacy, .size]), (hon, [.shape]), (mai, [.shape]), (ko, [.shape]), (satsu, [.shape]),
    (tsubu, [.shape]), (dai, [.function]), (kenBuilding, [.function]),
    (kenIncident, [.function]), (ki, [.function]), (ku, [.function]), (kyoku, [.function]),
    (mon, [.function]), (mune, [.function]), (seki, [.function, .size]),
    (soku, [.function, .quanta]), (soo, [.function, .size]), (ten, [.function]),
    (toori, [.function]), (tsuu, [.function]), (kabu, [.nature]), (shoku, [.function]),
    (teki, [.quanta])]

open Japanese.Classifiers in
/-- Ten of the forty-seven further forms a majority used, the extended inventory of Table 1.2,
coded likewise: *-rin* by its category of flowers, not by its morpheme 'ring'. -/
def extended : List (Classifier × List Parameter) :=
  [(sao, [.shape]), (wa, [.animacy]), (furi, [.function]), (zen, [.function]),
    (kyaku, [.function]), (rin, [.nature]), (ryoo, [.function]), (fusa, [.quanta]),
    (suji, [.shape]), (maki, [.arrangement])]

/-- The classifiers coded here. -/
def coding : List (Classifier × List Parameter) := core ++ extended

/-- The parameters of a classifier's category, if the inventory codes it. -/
def params (c : Classifier) : Option (List Parameter) := coding.lookup c

-- Table 1.1: *-tsu* is the general classifier.
theorem coding_eq_nil_iff : ∀ p ∈ coding, p.2 = [] ↔ p.1 = Japanese.Classifiers.tsu := by
  decide

/-! ### Kind-classifiers and quality-classifiers -/

/-- A deductive parameter, in the sense of [hunn-1977], unites a category by a physical property,
as length unites the category of *-hon*. -/
def Deductive (p : Parameter) : Prop := p.toClass = some .physical

instance : DecidablePred Deductive := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The type of semantic cohesion of a classifier's category. -/
inductive Cohesion
  | general
  | kind
  | quality
  | mixed
  deriving DecidableEq, Repr

/-- A category is a kind, an inductive category, when none of its parameters is deductive, a
quality when all are, mixed when both occur, and general when it has none. -/
def Cohesion.ofParams (ps : List Parameter) : Cohesion :=
  match ps.any (decide <| Deductive ·), ps.any (decide <| ¬ Deductive ·) with
  | false, false => .general
  | false, true => .kind
  | true, false => .quality
  | true, true => .mixed

/-- The cohesion of a coded classifier's category. -/
def cohesion (c : Classifier) : Option Cohesion := (params c).map .ofParams

/-- The labels Downing prints beside her examples. -/
def Cohesion.labels : List (String × Cohesion) := [("kind", .kind), ("quality", .quality)]

open Japanese.Classifiers in
/-- The examples of disambiguation by the choice of classifier, each with its classifier. -/
def disambiguation : List (Classifier × Datum) :=
  [(dai, Examples.ex_3_33a), (tsuu, Examples.ex_3_33b), (dai, Examples.ex_3_34a),
    (ryoo, Examples.ex_3_34b), (tsubu, Examples.ex_3_35a), (ko, Examples.ex_3_35b),
    (fusa, Examples.ex_3_35c), (hon, Examples.ex_3_36a), (ko, Examples.ex_3_36b),
    (rin, Examples.ex_3_36c)]

/-- The cohesion read off each category's parameters is the one Downing prints beside her
examples of disambiguation, (33)–(36): kind for *-dai*, *-tsū*, *-ryō* and *-rin*, quality for
*-tsubu*, *-ko*, *-fusa* and *-hon*. -/
theorem cohesion_eq_label :
    ∀ p ∈ disambiguation, p.2.parse? "cohesion" Cohesion.labels = cohesion p.1 := by
  decide

-- The examples checked are every example carrying a printed label, so no side is `none`.
theorem disambiguation_eq_labelled :
    disambiguation.map (·.2.id) =
      (Examples.all.filter fun e ↦ (e.feature? "cohesion").isSome).map (·.id) := by
  decide

/-- The pairs of core classifiers splitting one inductive category by size. -/
def sizeSplits : List (Classifier × Classifier) :=
  ((core.product core).filter fun (p, q) ↦
      .size ∈ p.2 ∧ p.2 = q.2 ∧ Cohesion.ofParams p.2 = .mixed ∧ p.1 ≠ q.1).map
    fun (p, q) ↦ (p.1, q.1)

open Japanese.Classifiers in
-- p. 91: the animal and boat categories are inductively given and split by size.
theorem sizeSplits_eq : sizeSplits = [(hiki, tou), (tou, hiki), (seki, soo), (soo, seki)] := by
  decide

open Japanese.Classifiers in
/-- Hypothesis 1, after [denny-1976], has classifiers encode categories of physical, functional and
social interaction, the substrate's physical, function and animacy classes, and it holds of the
classifiers Downing cites for it (p. 143): each encodes a parameter of the class she assigns it,
physical for *-hon*, *-suji*, *-mai* and *-satsu*, function for *-ken* and *-mune* 'buildings' and
*-ku* 'verses', animacy for *-nin*, *-mei*, *-hiki*, *-wa* and *-tō*. -/
theorem params_toClass :
    ∀ ci ∈ [(hon, Parameter.Class.physical), (suji, .physical), (mai, .physical),
        (satsu, .physical), (kenBuilding, .function), (mune, .function), (ku, .function),
        (nin, .animacy), (mei, .animacy), (hiki, .animacy), (wa, .animacy), (tou, .animacy)],
      ∃ ps ∈ params ci.1, ∃ p ∈ ps, p.toClass = some ci.2 := by
  decide

-- p. 143: the classifiers for humans and animals are set apart from those for inanimates, and the
-- classifiers that count the fragment's nouns encode animacy exactly for the animate nouns.
theorem params_animacy_iff :
    ∀ n ∈ Japanese.Nouns.nouns, ∀ c ∈ n.classifiers,
      ∃ ps ∈ params c, (∃ p ∈ ps, p.toClass = some .animacy) ↔ n.animacy ≠ .inanimate := by
  decide

/-! ### The classifier and noun systems -/

/-- The recurrent relations between a classifier's category and the independent sense of its
morpheme, Table 5.2: the six patterns of Japanese, the seventh found in other languages, and the
metonymic and metaphoric extensions of (4) and (5). -/
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

open Japanese.Classifiers in
/-- The relations Downing assigns, by Table 5.2, its surrounding text and (4a). She assigns none to
*-mai* and *-tsu*, which have no independent sense, nor to *-sao* 'pole', whose members bear
several relations to it; the pattern of shared quality and the metaphoric extension have no
Japanese instance. -/
def relations : List (Classifier × MorphemeRelation) :=
  [(nin, .identicalClass), (kenIncident, .identicalClass), (ki, .identicalClass),
    (tou, .partOfMembers), (kyaku, .partOfMembers), (mune, .partOfMembers),
    (tsuu, .associatedAction), (furi, .associatedAction), (suji, .exemplar),
    (maki, .creationAction), (soku, .beneficiaryGoal), (zen, .metonymic)]

-- pp. 151–152: only the first pattern pairs identical classes, and the quality-classifiers are
-- not clones of noun categories.
theorem relations_identicalClass :
    ∀ p ∈ relations, p.2 = .identicalClass → ∃ k ∈ cohesion p.1, k ≠ .quality := by
  decide

/-! ### Plural suffixes

Number is not obligatory in Japanese, and the classifier phrase and the plural suffixes *-tachi*
and *-ra* share the task of individuating referents, against the universal of
[sanches-slobin-1973] that classifier languages lack obligatory plural marking. -/

/-- The head of a noun phrase, in the order of its referentiality. -/
inductive NPHead
  | commonNoun
  | properNoun
  | pronoun
  deriving DecidableEq, Repr, Fintype

/-- The availability of the plural suffix, from impossible to required. -/
inductive Availability
  | impossible
  | rare
  | possible
  | required
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder NPHead := LinearOrder.lift' NPHead.ctorIdx (by decide)

instance : LinearOrder Availability := LinearOrder.lift' Availability.ctorIdx (by decide)

/-- Table 7.2: the availability of the plural suffix by the animacy of the referents and the head
of the noun phrase. -/
def pluralMarking : Animacy → NPHead → Availability
  | _, .pronoun => .required
  | .human, .properNoun => .required
  | .human, .commonNoun => .possible
  | .animate, _ => .rare
  | .inanimate, _ => .impossible

theorem pluralMarking_mono_referent (h : NPHead) : Monotone (pluralMarking · h) := by
  unfold Monotone
  decide +revert

theorem pluralMarking_mono_head (r : Animacy) : Monotone (pluralMarking r) := by
  unfold Monotone
  decide +revert

/-- The two factors of Table 7.2 correlate with the speaker's referential intent: the use of the
suffix rises with the animacy of the referents and with the referentiality of the head, from the
common noun to the proper noun to the pronoun, a plurality split in the sense of
[smith-stark-1974]. -/
theorem pluralMarking_monotone : Monotone (Function.uncurry pluralMarking) :=
  fun a b h ↦ (pluralMarking_mono_referent a.2 h.1).trans (pluralMarking_mono_head b.1 h.2)

-- pp. 216–217: the speaker has a true option only with common nouns referring to humans.
theorem pluralMarking_eq_possible_iff {r : Animacy} {h : NPHead} :
    pluralMarking r h = .possible ↔ r = .human ∧ h = .commonNoun := by
  decide +revert

/-- The number system of a head, after [greenberg-1972]: common nouns are transnumeral, denoting
the concept rather than individuals, while pronouns and proper nouns are inherently singular. The
suffix accordingly makes a class plural of a common noun, *kodomo-tachi* 'children', and an
associative plural of a singular head, *Endoo-san-tachi* 'Mr. Endo and the others'. -/
inductive NumberSystem
  | transnumeral
  | singularPlural
  deriving DecidableEq, Repr

/-- The number system of each head. -/
def numberSystem : NPHead → NumberSystem
  | .commonNoun => .transnumeral
  | .properNoun | .pronoun => .singularPlural

-- pp. 211–212: an inherently singular head referring to several humans requires the suffix.
theorem required_iff_singularPlural (h : NPHead) :
    pluralMarking .human h = .required ↔ numberSystem h = .singularPlural := by
  cases h <;> decide

/-- The head of a noun phrase as an entry of the fragments. -/
inductive Head
  | noun (n : Japanese.Nouns.Noun)
  | name (n : Japanese.Nouns.ProperName)
  | personal (p : PersonalPronoun)
  | demonstrative (p : DemonstrativePronoun)

/-- The head type of Table 7.2 that an entry instantiates. -/
def Head.type : Head → NPHead
  | .noun _ => .commonNoun
  | .name _ => .properNoun
  | .personal _ | .demonstrative _ => .pronoun

/-- A noun phrase referring to a group: its head and the animacy of the group's members. -/
structure GroupNP where
  /-- The head. -/
  head : Head
  /-- The animacy of the members of the group. -/
  animacy : Animacy

/-- A common noun refers to a group of the animacy the fragment records for it. -/
def GroupNP.ofNoun (n : Japanese.Nouns.Noun) : GroupNP := ⟨.noun n, n.animacy⟩

/-- The availability of the plural suffix on the noun phrase. -/
def GroupNP.availability (x : GroupNP) : Availability := pluralMarking x.animacy x.head.type

open Japanese.Nouns Japanese.Pronouns in
/-- The plural-suffixed noun phrases of the examples (6)–(12), each with its example. A pronoun's
group is the one the context names with a common noun, the faces of (9a) and the patients of
(10a), and *Endoo-san* 'Mr. Endo' of (11) is a person. -/
def suffixed : List (Datum × GroupNP) :=
  [(Examples.ex_7_6a, .ofNoun kodomo), (Examples.ex_7_7a, .ofNoun neko),
    (Examples.ex_7_8a, .ofNoun tatemono), (Examples.ex_7_9a, ⟨.demonstrative kore, kao.animacy⟩),
    (Examples.ex_7_9b, .ofNoun kao), (Examples.ex_7_10a, ⟨.personal kare, kanja.animacy⟩),
    (Examples.ex_7_10b, .ofNoun kanja), (Examples.ex_7_11, ⟨.name endoo, .human⟩),
    (Examples.ex_7_12, .ofNoun kodomo)]

open Japanese.Nouns Japanese.Pronouns in
/-- The bare noun phrases of the examples (6)–(10) referring to the same groups. -/
def bare : List (Datum × GroupNP) :=
  [(Examples.ex_7_6b, .ofNoun kodomo), (Examples.ex_7_7b, .ofNoun neko),
    (Examples.ex_7_8b, .ofNoun tatemono), (Examples.ex_7_10c, ⟨.personal kare, kanja.animacy⟩)]

/-- Table 7.2 predicts the judgments of the examples that test it: a plural-suffixed noun phrase
is accepted where the suffix is possible or required, so *kodomo-tachi* 'children' and *kore-ra*
'these' but not *neko-tachi* 'cats', *tatemono-tachi* 'buildings' or *kao-tachi* 'faces', and a
bare noun phrase referring to a group wherever the suffix is not required, so *kodomo*, *neko* and
*tatemono* but not *kare* for *kare-ra* 'they'. -/
theorem plural_rows :
    (∀ p ∈ suffixed, p.1.judgment.band = .ofProp (.possible ≤ p.2.availability)) ∧
      ∀ p ∈ bare, p.1.judgment.band = .ofProp (p.2.availability < .required) := by
  decide

/-! ### Introducing and tracking a group -/

/-- The two individuators. -/
inductive Individuator
  | classifierPhrase
  | pluralMarker
  deriving DecidableEq, Repr, Fintype

/-- A mention of a group, by the individuators its noun phrase carries: none on a bare noun, and
both on *sono futari-no otoko-no ko-tachi* 'those two boys' (2b). -/
abbrev Mention := Finset Individuator

/-- A sequence of mentions of a group is licensed when the group is identifiable to the hearer
([lambrecht-1994]), at least uniquely identifiable on the Givenness Hierarchy
([gundel-hedberg-zacharski-1993]), at every plural-marked mention: at the first as the context
makes it, and after it, since a mention makes the group identifiable. -/
def Licensed : GundelHedbergZacharski1993.CognitiveStatus → List Mention → Prop
  | _, [] => True
  | s, m :: l => (.pluralMarker ∈ m → .uniquelyIdentifiable ≤ s) ∧ Licensed .uniquelyIdentifiable l

instance instDecidableLicensed : ∀ s l, Decidable (Licensed s l)
  | _, [] => isTrue trivial
  | s, m :: l =>
    have := instDecidableLicensed .uniquelyIdentifiable l
    decidable_of_iff
      ((.pluralMarker ∈ m → .uniquelyIdentifiable ≤ s) ∧ Licensed .uniquelyIdentifiable l) Iff.rfl

theorem licensed_uniquelyIdentifiable : ∀ l, Licensed .uniquelyIdentifiable l
  | [] => trivial
  | _ :: l => ⟨fun _ ↦ le_rfl, licensed_uniquelyIdentifiable l⟩

/-- A group the hearer cannot yet identify is tracked by a licensed sequence of mentions exactly
when its introduction carries no plural marker: it is introduced bare or with a classifier phrase,
and the plural marker then maintains it, since a plural-marked introduction would be like an
initial mention with a definite article in English. -/
theorem licensed_cons_iff {s : GundelHedbergZacharski1993.CognitiveStatus}
    (hs : s < .uniquelyIdentifiable) {m : Mention} {l : List Mention} :
    Licensed s (m :: l) ↔ .pluralMarker ∉ m := by
  simp [Licensed, licensed_uniquelyIdentifiable, not_le.2 hs]

-- p. 215: no group is introduced with the plural marker and then counted with a classifier
-- phrase, though the classifier phrase may be repeated.
example : ¬ Licensed .referential [{.pluralMarker}, {.classifierPhrase}] := by decide

example : Licensed .referential [{.classifierPhrase}, {.pluralMarker}, {.classifierPhrase}] := by
  decide

/-- The mentions of the groups of (16) and (23) and of (43) of Chapter 8: *otoko-ga iku-nin-mo*
'men, any number', then *kare-ra* 'they' and *ano otoko-tachi* 'those men'; *iku-nin-mo-no onna*
'a number of women', then *sono onna-tachi* 'those women'; *heishi-ga ni-mei* 'two soldiers', then
*futari-no heishi-tachi* 'the two soldiers'. -/
def chains : List (Datum × List Mention) :=
  [(Examples.ex_7_16, [{.classifierPhrase}, {.pluralMarker}, {.pluralMarker}]),
    (Examples.ex_7_23, [{.classifierPhrase}, {.pluralMarker}]),
    (Examples.ex_8_43, [{.classifierPhrase}, {.classifierPhrase, .pluralMarker}])]

-- (16), (23), and (43) of Chapter 8
theorem chains_licensed : ∀ p ∈ chains, ∀ s : GundelHedbergZacharski1993.CognitiveStatus,
    s < .uniquelyIdentifiable → p.1.judgment.band = .ofProp (Licensed s p.2) := by
  decide

end Downing1996
