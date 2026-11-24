module

public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Nordlinger2023
public import Linglib.Data.WALS.Features.F106A
public import Linglib.Syntax.Reciprocal
public import Studies.Siloni2012
public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Languages.English.Reciprocals
public import Linglib.Languages.Chichewa.Reciprocals
public import Linglib.Languages.Romance.French.Reciprocals
public import Linglib.Languages.Greek.StandardModern.Reciprocals
public import Linglib.Languages.Hungarian.Reciprocals
public import Linglib.Languages.Icelandic.Reciprocals
public import Linglib.Languages.Mandarin.Reciprocals
public import Linglib.Languages.Slavic.Czech.Reciprocals
public import Linglib.Languages.Slavic.Russian.Reciprocals
public import Linglib.Languages.Swahili.Reciprocals
public import Linglib.Languages.Wambaya.Reciprocals

/-!
# Nordlinger (2023): The Typology of Reciprocal Constructions

Nordlinger's review of reciprocal constructions organizes the classificatory work of Nedjalkov,
Maslova, Evans, Siloni and Hurst.

* Strategies. König and Kokutani, Nedjalkov and Evans sort the same strategies differently, and
  the review's examples (9)–(13) show where: the Wambaya clitic is nominal for the first,
  a class of its own for the second and argument-marking for the third, and the Mandarin compound
  is morphological for Nedjalkov and a multiple-predicate strategy for Evans
  (`typologies_on_examples`).
* Valency. Nominal and argument strategies tend to preserve the valency of the base verb and
  verb-marking strategies to reduce it: wherever the valency indicators of a unary construction
  agree, they agree with the strategy's default (`valency_follows_default`). Tonga's verb-marked
  reciprocal keeps both argument NPs and is binary in Maslova's sense (`tonga_counterexample`),
  and in the Australian cases of Evans and colleagues the indicators disagree
  (`kuukThaayorre_mixed`, `dalabon_mixed`).
* Discontinuous reciprocals are licensed exactly for lexically formed reciprocal verbs on
  Siloni's typology, which the review's examples confirm (`discontinuous_iff_lexical`).
* Levels. Hurst's four reciprocation strategies are all the ways of having one or two arguments
  at argument, functional and constituent structure without gaining one from a level to the next
  (`exists_arguments_eq_iff`), and a reciprocal verb is lexically formed exactly when it has one
  argument at argument structure (`lexical_iff_one_argument`).
* Semantics. The six configurations of a mutual event, from strong reciprocity to the ring, are
  stated as conditions on the relation (`ReciprocityType.Realizes`): only the strong and pairwise
  configurations are symmetric, and all but the melee involve every participant. The review's
  five children who each see and are seen by another, though not by every other, are weakly and
  not strongly reciprocal (`weakReciprocity_sees`). Reflexive and reciprocal marking coincide in
  60 of the 175 languages of Maslova and Nedjalkov's sample (`reflexive_polysemy_count`).

## Implementation notes

Each language's construction takes its marker from the language's fragment, or from the review's
example where no fragment exists (Warlpiri, Kuuk Thaayorre, Dalabon, Tonga), and records the
valency indicators the review reports; the ergative and accusative glosses of its examples are
checked against them (`ergative_iff_subjectCase_bivalent`, `objectSlot_bivalent_of_accusative`).
The Wambaya clitic is classed as the review classes it, with the pronominal strategies; the
language file's entry follows Evans and colleagues, who argue that it marks the predicate. The
review
gives no discontinuous example for Czech. The formation locus is Siloni's own classification where
it covers the language and the review's extension otherwise. Malagasy, bivalent at f-structure and
monovalent at c-structure on Hurst's analysis, is one of the four strategies of `Reciprocation` and
has no construction in the sample. A marker records only whether it is also reflexive, the polysemy
carried by the markers glossed RR (French *se*, Wambaya *-ngg-*, Warlpiri *-nyanu*, Dalabon *-rr*);
the review's further polysemy types, Yakut *-üs* with collective and sociative readings (ex. 49)
and East Futunan *fe-...-ʼaki* with iterative ones (ex. 50, both after Nedjalkov), are not. The six
configurations are given conditions of the formalization's own, the review naming them by example
only; the melee is taken as some interaction that leaves a participant out.

## References

* [nordlinger-2023]
* [nedjalkov-2007a]
* [nedjalkov-2007b]
* [maslova-2008]
* [evans-2008]
* [siloni-2008]
* [siloni-2012]
* [dalrymple-et-al-1998]
* [evans-et-al-2011b]
* [evans-et-al-2007]
* [dimitriadis-2008]
* [hurst-2012]
* [konig-kokutani-2006]
* [maslova-nedjalkov-2013]
* [majid-et-al-2011]
-/

@[expose] public section

namespace Nordlinger2023

open Reciprocal

/-! ### The review's languages -/

/-- The languages whose reciprocal constructions the review describes. -/
inductive Language where
  | english | russian | hausa | swahili | hungarian | french | greek | mandarin
  | wambaya | icelandic | chichewa | czech | warlpiri | kuukThaayorre | dalabon | tonga
  deriving DecidableEq, Fintype

/-- Hausa *jūnan-* is a reciprocal pronoun with a person suffix ([nordlinger-2023] ex. 10). -/
def hausaJuna : Marker := { morphs := [.free "jūnan"], strategy := .recipPronoun }

/-- The Wambaya clitic as the review classes it, a pronominal element in the object position of
the auxiliary ([nordlinger-2023] ex. 11, §3.1). -/
def wambayaRr : Marker := { Wambaya.Reciprocals.rr with strategy := .boundPronoun }

/-- Warlpiri *-nyanu* is the reflexive–reciprocal bound pronoun in the object slot of the
pronominal complex ([nordlinger-2023] ex. 18b, 48). -/
def warlpiriNyanu : Marker :=
  { morphs := [.suff "nyanu"], strategy := .boundPronoun }

/-- Kuuk Thaayorre *-rr* is the reciprocal verbal suffix ([nordlinger-2023] ex. 25). -/
def kuukThaayorreRr : Marker := { morphs := [.suff "rr"], strategy := .verbalAffix }

/-- Dalabon *-rr* is the reflexive–reciprocal verbal suffix ([nordlinger-2023] ex. 26b). -/
def dalabonRr : Marker :=
  { morphs := [.suff "rr"], strategy := .verbalAffix }

/-- Tonga *-an* is the reciprocal verbal suffix ([nordlinger-2023] ex. 21, from
[maslova-2008] (9), p. 230). -/
def tongaAn : Marker := { morphs := [.suff "an"], strategy := .verbalAffix }

/-- A construction whose only reported indicator is the object slot. -/
def objectSlot (v : Valency) : Indicator → Option Valency
  | .objectSlot => some v
  | _ => none

/-- The reciprocal construction the review describes for each language.

English: bipartite NP *each other* in the object position (ex. 1b), distinct from the reflexive; the
lexical reciprocals (*quarrel*, *meet*, ex. 7) are verb entries, not a marker. Russian: bipartite
*drug druga* 'other other-ACC' (ex. 9), the accusative showing the object slot filled; the
reflexive-identical postfix *-sja* (ex. 31) is the inventory's second marker. Swahili: verbal affix
*-an-* with a single subject NP (ex. 12). Hungarian: verbal affix *-óz-* (ex. 19, 30). French: the
clitic *se* is not a reciprocal object (ex. 28, 35), so the slot is empty; bipartite *l'un l'autre*
is the second marker. Greek: nonactive morphology (ex. 27a). Mandarin: compound *dǎ-lái-dǎ-qù* with
a single subject NP (ex. 13). Hausa: the reciprocal pronoun *jūnan-mù* (ex. 10), of whose valency
the review says nothing. Wambaya: the RR clitic in the object position of the auxiliary (ex. 11),
which the review groups with the argument strategies (§3.1) and of whose valency it says nothing.
Icelandic: bipartite *hvort annað*, the accusative on *annað* showing the clause transitive
(ex. 17a). Chicheŵa: verbal affix *-an-* (ex. 20). Czech: the clitic *se* (ex. 29), as in French.
Warlpiri: the object bound pronoun and the ergative subject both keep the clause transitive
(ex. 18b). Kuuk Thaayorre: the object NP is obligatorily absent yet the subject keeps ergative case
(ex. 25). Dalabon: the verb takes the intransitive subject pronominal series yet incorporates the
patient's body part as in the transitive clause (ex. 26). Tonga: both reciprocants are argument NPs
of the verb-marked reciprocal (ex. 21). -/
def Language.construction : Language → Construction
  | .english => { marker := English.Reciprocals.eachOther, valency := objectSlot .bivalent }
  | .russian => { marker := Russian.Reciprocals.drugDruga, valency := objectSlot .bivalent }
  | .hausa => { marker := hausaJuna }
  | .swahili => { marker := Swahili.Reciprocals.anSuffix, valency := objectSlot .monovalent }
  | .hungarian =>
      { marker := Hungarian.Reciprocals.ozSuffix, valency := objectSlot .monovalent }
  | .french => { marker := French.Reciprocals.se, valency := objectSlot .monovalent }
  | .greek =>
      { marker := Greek.StandardModern.Reciprocals.nonactive
      , valency := objectSlot .monovalent }
  | .mandarin => { marker := Mandarin.Reciprocals.compound, valency := objectSlot .monovalent }
  | .wambaya => { marker := wambayaRr }
  | .icelandic => { marker := Icelandic.Reciprocals.hvorAnnad, valency := objectSlot .bivalent }
  | .chichewa => { marker := Chichewa.Reciprocals.anSuffix, valency := objectSlot .monovalent }
  | .czech => { marker := Czech.Reciprocals.se, valency := objectSlot .monovalent }
  | .warlpiri =>
      { marker := warlpiriNyanu
      , valency := fun | .objectSlot | .subjectCase => some .bivalent | _ => none }
  | .kuukThaayorre =>
      { marker := kuukThaayorreRr
      , valency := fun | .objectSlot => some .monovalent | .subjectCase => some .bivalent
                       | _ => none }
  | .dalabon =>
      { marker := dalabonRr
      , valency := fun | .agreement => some .monovalent | .incorporation => some .bivalent
                       | _ => none }
  | .tonga => { marker := tongaAn, valency := objectSlot .bivalent }

/-- The formation locus of the verb-marked reciprocals the review discusses (§3.3):
[siloni-2012]'s own classification where it covers the language, and the review's
extension to Swahili and Greek, lexicon-formed because they form discontinuous
reciprocals with a comitative (ex. 36, 37). English's lexical reciprocals are set aside:
*kiss* and *hug* resist the discontinuous construction ([siloni-2012] fn. 32), and German
*sich*-reciprocals ([siloni-2012] fn. 13) are not taken up by the review. -/
def Language.formation : Language → Option Formation
  | .french => some Siloni2012.Language.french.formation
  | .czech => some Siloni2012.Language.czech.formation
  | .hungarian => some Siloni2012.Language.hungarian.formation
  | .swahili | .greek => some .lexical
  | _ => none

/-- The Glottocode of a language, under which the review's examples are filed. -/
def Language.glottocode : Language → Glottocode
  | .english => .english
  | .russian => .russian
  | .hausa => .hausa
  | .swahili => .swahili
  | .hungarian => .hungarian
  | .french => .french
  | .greek => .modernGreek
  | .mandarin => .mandarinChinese
  | .wambaya => .wambayan
  | .icelandic => .icelandic
  | .chichewa => .nyanja
  | .czech => .czech
  | .warlpiri => .warlpiri
  | .kuukThaayorre => .thayore
  | .dalabon => .ngalkbun
  | .tonga => .tongaZambia

/-- A word of the row is glossed with the label. -/
def Glossed (e : Datum) (label : String) : Prop :=
  ∃ w ∈ e.glossedWords, label.toList <:+: w.gloss

instance (e : Datum) (label : String) : Decidable (Glossed e label) :=
  inferInstanceAs (Decidable (∃ w ∈ e.glossedWords, _))

/-! ### Strategy and valency -/

/-- The reciprocal examples of the language are unary in Maslova's sense: one slot is open to the
free expression of the reciprocants. -/
def Language.Unary (l : Language) : Prop :=
  ∀ e ∈ Examples.all, e.language = l.glottocode →
    Examples.construction e = some .reciprocal → Examples.slots e = some .unary

instance : DecidablePred Language.Unary := fun _ ↦ List.decidableBAll _ _

/-- Where the indicators of a language's unary reciprocal construction agree, they read the
default valency of its strategy. -/
theorem valency_follows_default :
    ∀ l : Language, ¬ l.construction.Mixed → l.Unary →
      l.construction.Unanimous l.construction.strategy.defaultValency := by
  decide

variable {l : Language}

theorem nominal_strategy_bivalent (hm : ¬ l.construction.Mixed) (hu : l.Unary)
    (h : l.construction.strategy.IsNominal) : ¬ l.construction.Reads .monovalent := fun hr ↦
  (Strategy.defaultValency_eq_monovalent_iff _).1
    (valency_follows_default l hm hu _ hr).symm h

theorem monovalent_implies_verbal (hm : ¬ l.construction.Mixed) (hu : l.Unary)
    (h : l.construction.Reads .monovalent) : ¬ l.construction.strategy.IsNominal :=
  (Strategy.defaultValency_eq_monovalent_iff _).1 (valency_follows_default l hm hu _ h).symm

/-! ### Mixed transitivity effects

The tendency is not absolute. Tonga's verb-marked reciprocal keeps both reciprocants as
argument NPs ([maslova-2008] (9), p. 230), and in the Australian cases of [evans-et-al-2007] the
indicators of valency disagree with one another. -/

theorem kuukThaayorre_mixed : Language.kuukThaayorre.construction.Mixed := by decide

theorem dalabon_mixed : Language.dalabon.construction.Mixed := by decide

theorem tonga_counterexample :
    ¬ Language.tonga.construction.strategy.IsNominal ∧
      Language.tonga.construction.Reads .bivalent ∧ ¬ Language.tonga.Unary := by
  decide

/-! ### Discontinuous reciprocals -/

/-- A discontinuous reciprocal of the review's examples is acceptable exactly when the
language's reciprocal verbs are formed in the lexicon: (36), (37), (38) against (39). -/
theorem discontinuous_iff_lexical :
    ∀ e ∈ Examples.all, Examples.construction e = some .discontinuous →
      ∀ l : Language, l.glottocode = e.language → ∀ f ∈ l.formation,
        (Siloni2012.Property.discontinuous.Holds f ↔ e.judgment = .acceptable) := by
  decide

/-! ### The indicators in the examples -/

-- (18b), (25)
theorem ergative_iff_subjectCase_bivalent :
    ∀ e ∈ Examples.all, Examples.construction e = some .reciprocal →
      ∀ l : Language, l.glottocode = e.language →
        (Glossed e "ERG" ↔ l.construction.valency .subjectCase = some .bivalent) := by
  decide

-- (9), (17a)
theorem objectSlot_bivalent_of_accusative :
    ∀ e ∈ Examples.all, Examples.construction e = some .reciprocal → Glossed e "ACC" →
      ∀ l : Language, l.glottocode = e.language →
        l.construction.valency .objectSlot = some .bivalent := by
  decide

/-! ### Three typologies of strategy (§3.1)

König and Kokutani divide strategies into nominal and verbal, the nominal ones quantificational
or pronominal and the verbal ones synthetic or compound. Nedjalkov divides the grammatical
reciprocals by the means that express the marker, syntactic, morphological or clitic. Evans
divides single-clause strategies into argument-marking and predicate-marking and sets
multiple-predicate strategies apart, `Reciprocal.Strategy.codingSite`. -/

/-- König and Kokutani's four kinds of strategy. -/
inductive KonigKokutani where
  | quantificational
  | pronominal
  | synthetic
  | compound
  deriving DecidableEq, Repr, Fintype

/-- The nominal kinds, against the verbal ones. -/
def KonigKokutani.IsNominal (k : KonigKokutani) : Prop := k = .quantificational ∨ k = .pronominal

instance : DecidablePred KonigKokutani.IsNominal :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Nedjalkov's three means of expressing a grammatical reciprocal marker. -/
inductive Nedjalkov where
  | syntactic
  | morphological
  | clitic
  deriving DecidableEq, Repr, Fintype

/-- The kind of a strategy for König and Kokutani, where the review places it. -/
def konigKokutani : Strategy → Option KonigKokutani
  | .bipartiteNP => some .quantificational
  | .recipPronoun | .boundPronoun => some .pronominal
  | .verbalAffix => some .synthetic
  | .compoundVerb => some .compound
  | _ => none

/-- The means of a strategy for Nedjalkov, where the review places it. -/
def nedjalkov : Strategy → Option Nedjalkov
  | .bipartiteNP | .recipPronoun => some .syntactic
  | .verbalAffix | .compoundVerb => some .morphological
  | .boundPronoun | .recipClitic => some .clitic
  | _ => none

/-- The five languages of the review's examples (9)–(13). -/
def surveyed : List Language := [.russian, .hausa, .wambaya, .swahili, .mandarin]

/-- The review's sorting of examples (9)–(13): nominal in (9)–(11) and verbal in (12)–(13) for
König and Kokutani; syntactic in (9)–(10), a clitic in (11) and morphological in (12)–(13) for
Nedjalkov; argument-marking in (9)–(11), predicate-marking in (12) and multiple predicates in
(13) for Evans. -/
theorem typologies_on_examples :
    (surveyed.filter fun l ↦ ∃ k ∈ konigKokutani l.construction.strategy, k.IsNominal) =
        [.russian, .hausa, .wambaya] ∧
      (surveyed.filter fun l ↦ nedjalkov l.construction.strategy = some .syntactic) =
        [.russian, .hausa] ∧
      (surveyed.filter fun l ↦ nedjalkov l.construction.strategy = some .clitic) = [.wambaya] ∧
      (surveyed.filter fun l ↦ l.construction.strategy.codingSite = .argument) =
        [.russian, .hausa, .wambaya] ∧
      (surveyed.filter fun l ↦ l.construction.strategy.codingSite = .predicate) = [.swahili] ∧
      (surveyed.filter fun l ↦ l.construction.strategy.codingSite = .multiclausal) =
        [.mandarin] := by
  decide

theorem konigKokutani_isNominal_iff {s : Strategy} {k : KonigKokutani}
    (h : konigKokutani s = some k) : k.IsNominal ↔ s.codingSite = .argument := by
  cases s <;> cases k <;> revert h <;> decide

theorem nedjalkov_crosses_codingSite :
    (∃ s t, nedjalkov s = nedjalkov t ∧ nedjalkov s ≠ none ∧ s.codingSite ≠ t.codingSite) ∧
      ∃ s t, s.codingSite = t.codingSite ∧ nedjalkov s ≠ none ∧ nedjalkov t ≠ none ∧
        nedjalkov s ≠ nedjalkov t :=
  ⟨⟨.verbalAffix, .compoundVerb, by decide⟩, ⟨.bipartiteNP, .boundPronoun, by decide⟩⟩

/-! ### Levels of structure (§3.3)

Hurst sorts reciprocation strategies by the number of arguments at argument structure, at
functional structure and at constituent structure. -/

/-- The three levels of syntactic structure, from the most abstract. -/
inductive Level where
  | argument
  | functional
  | constituent
  deriving DecidableEq, Repr, Fintype

/-- The levels in order, argument structure first. -/
instance : LinearOrder Level := .lift' Level.ctorIdx (by decide)

/-- Hurst's four reciprocation strategies. -/
inductive Reciprocation where
  /-- A reciprocal anaphor, two arguments at every level, as in English and Icelandic. -/
  | anaphor
  /-- A verb-marked reciprocal whose second argument is unexpressed in the constituent structure
  only, as in Malagasy. -/
  | unexpressed
  /-- A monovalent reciprocal verb formed in the syntax, as in French. -/
  | syntacticVerb
  /-- A monovalent reciprocal verb formed in the lexicon, as in Swahili. -/
  | lexicalVerb
  deriving DecidableEq, Repr, Fintype

/-- The number of arguments of a strategy at a level. -/
def Reciprocation.arguments : Reciprocation → Level → ℕ
  | .anaphor, _ => 2
  | .unexpressed, .constituent => 1
  | .unexpressed, _ => 2
  | .syntacticVerb, .argument => 2
  | .syntacticVerb, _ => 1
  | .lexicalVerb, _ => 1

theorem Reciprocation.arguments_antitone (r : Reciprocation) : Antitone r.arguments := by
  intro a b h
  cases r <;> cases a <;> cases b <;> first | exact absurd h (by decide) | decide

theorem Reciprocation.arguments_injective : Function.Injective Reciprocation.arguments := by
  intro r r' h
  have h₁ := congrFun h .argument
  have h₂ := congrFun h .functional
  have h₃ := congrFun h .constituent
  cases r <;> cases r' <;>
    first
    | rfl
    | exact absurd h₁ (by decide)
    | exact absurd h₂ (by decide)
    | exact absurd h₃ (by decide)

/-- Hurst's four strategies are all the ways of having one or two arguments at each level without
gaining an argument from one level to the next. -/
theorem exists_arguments_eq_iff (f : Level → ℕ) :
    (∃ r : Reciprocation, r.arguments = f) ↔ Antitone f ∧ ∀ l, f l = 1 ∨ f l = 2 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r.arguments_antitone, fun l ↦ by cases r <;> cases l <;> decide⟩
  · rintro ⟨hf, hv⟩
    have hab : f .functional ≤ f .argument := hf (by decide)
    have hbc : f .constituent ≤ f .functional := hf (by decide)
    have key : ∀ r : Reciprocation, r.arguments .argument = f .argument →
        r.arguments .functional = f .functional → r.arguments .constituent = f .constituent →
        r.arguments = f := fun r h₁ h₂ h₃ ↦ funext fun l ↦ by cases l <;> assumption
    rcases hv .argument with ha | ha <;> rcases hv .functional with hb | hb <;>
      rcases hv .constituent with hc | hc
    · exact ⟨.lexicalVerb, key _ ha.symm hb.symm hc.symm⟩
    · omega
    · omega
    · omega
    · exact ⟨.syntacticVerb, key _ ha.symm hb.symm hc.symm⟩
    · omega
    · exact ⟨.unexpressed, key _ ha.symm hb.symm hc.symm⟩
    · exact ⟨.anaphor, key _ ha.symm hb.symm hc.symm⟩

/-- The strategy the review assigns a language of the sample. -/
def Language.reciprocation : Language → Option Reciprocation
  | .english | .icelandic => some .anaphor
  | .swahili => some .lexicalVerb
  | .french => some .syntacticVerb
  | _ => none

theorem lexical_iff_one_argument :
    ∀ l : Language, ∀ r ∈ l.reciprocation, ∀ f ∈ l.formation,
      (f = .lexical ↔ r.arguments .argument = 1) := by
  decide

/-! ### Reflexive and reciprocal polysemy (§4) -/

open Data.WALS.F106A in
-- 60 of the 175 languages of Maslova and Nedjalkov's sample
theorem reflexive_polysemy_count :
    allData.length = 175 ∧
      (allData.filter fun d ↦ d.2 = .identicalToReflexive ∨ d.2 = .mixed).length = 60 := by
  decide +kernel

/-! ### Semantic reciprocity types (§4)

The review presents the semantic typology of Evans and colleagues, who start from the relations
Dalrymple and colleagues identify and distinguish six configurations of a mutual event. Each is
stated here, after the extensional schemas of Majid and colleagues, as a condition fixing the
extension of `R` on the participants `X`; adjacency in a chain or ring is a pair of consecutive
positions in a duplicate-free list. -/

section Configurations

variable {A : Type*} {R : A → A → Prop} {X : Finset A}

/-- `y` immediately follows `x` in `l`. -/
def Consecutive (l : List A) (x y : A) : Prop := ∃ i, l[i]? = some x ∧ l[i + 1]? = some y

theorem Consecutive.mem_left {l : List A} {x y : A} (h : Consecutive l x y) : x ∈ l :=
  let ⟨_, hx, _⟩ := h
  List.mem_of_getElem? hx

theorem Consecutive.mem_right {l : List A} {x y : A} (h : Consecutive l x y) : y ∈ l :=
  let ⟨_, _, hy⟩ := h
  List.mem_of_getElem? hy

theorem Consecutive.ne {l : List A} (hnd : l.Nodup) {x y : A} (h : Consecutive l x y) :
    x ≠ y := by
  obtain ⟨i, hx, hy⟩ := h
  rintro rfl
  have := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hx).1 hnd).1 (hx.trans hy.symm)
  omega

theorem Consecutive.asymm {l : List A} (hnd : l.Nodup) {x y : A} (hxy : Consecutive l x y) :
    ¬ Consecutive l y x := by
  rintro ⟨j, hy', hx'⟩
  obtain ⟨i, hx, hy⟩ := hxy
  have h₁ := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hx).1 hnd).1
    (hx.trans hx'.symm)
  have h₂ := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hy).1 hnd).1
    (hy.trans hy'.symm)
  omega

theorem exists_consecutive_or_getLast {l : List A} {x : A} (hx : x ∈ l) :
    (∃ y, Consecutive l x y) ∨ l.getLast? = some x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  by_cases h : i + 1 < l.length
  · exact .inl ⟨l[i + 1], i, hi, List.getElem?_eq_getElem h⟩
  · right
    rw [List.getLast?_eq_getElem?]
    convert hi using 2
    have := (List.getElem?_eq_some_iff.1 hi).1
    omega

theorem exists_consecutive_of_getLast {l : List A} (hlen : 2 ≤ l.length) {x : A}
    (hx : l.getLast? = some x) : ∃ y, Consecutive l y x := by
  rw [List.getLast?_eq_getElem?] at hx
  refine ⟨l[l.length - 2], l.length - 2, List.getElem?_eq_getElem (by omega), ?_⟩
  convert hx using 2
  omega

/-- In the pairwise configuration the participants split into two-member cells and `R` holds
exactly within cells. -/
def PairwiseConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ P : Finpartition X, (∀ c ∈ P.parts, c.card = 2) ∧
    ∀ x y, R x y ↔ ∃ c ∈ P.parts, x ∈ c ∧ y ∈ c ∧ x ≠ y

/-- In the chain configuration the participants form a line and `R` holds exactly from each
member to the next. -/
def ChainConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.toFinset = X ∧ 2 ≤ l.length ∧ ∀ x y, R x y ↔ Consecutive l x y

/-- The ring configuration is a chain whose last member also acts on the first. -/
def RingConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.toFinset = X ∧ 3 ≤ l.length ∧
    ∀ x y, R x y ↔ Consecutive l x y ∨ (l.getLast? = some x ∧ l.head? = some y)

/-- In the radial configuration one central participant acts on each of the others. -/
def RadialConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ c ∈ X, 2 ≤ X.card ∧ ∀ x y, R x y ↔ x = c ∧ y ∈ X ∧ y ≠ c

/-- In the melee configuration there is some interaction, but participation is not
exhaustive. -/
def MeleeConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  (∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ R x y) ∧ ¬ InclusiveAlternativeOrdering R X

theorem symm_of_strongReciprocity (h : StrongReciprocity R X) :
    Std.Symm fun a b : (X : Set A) ↦ R a b :=
  ⟨fun a b hab ↦ by
    by_cases hba : b = a
    · exact hba ▸ hab
    · exact h.2 hba⟩

theorem RadialConfig.not_symm (h : RadialConfig R X) :
    ¬ Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  obtain ⟨y, hy, hyc⟩ := X.exists_mem_ne hcard c
  intro hsym
  exact hyc ((hiff y c).1 (hsym.symm ⟨c, hc⟩ ⟨y, hy⟩ ((hiff c y).2 ⟨rfl, hy, hyc⟩))).1

theorem RadialConfig.inclusiveAlternativeOrdering (h : RadialConfig R X) :
    InclusiveAlternativeOrdering R X := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  refine oneWayWeakReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 hcard, fun x hx ↦ ?_⟩
  by_cases hxc : x = c
  · subst hxc
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hyx.symm, .of_rel ((hiff x y).2 ⟨rfl, hy, hyx⟩)⟩
  · exact ⟨c, hc, hxc, .of_rel_symm ((hiff c x).2 ⟨rfl, hx, hxc⟩)⟩

variable [DecidableEq A]

theorem PairwiseConfig.symm (h : PairwiseConfig R X) : Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨P, -, hiff⟩ := h
  refine ⟨fun x y hR ↦ ?_⟩
  obtain ⟨c, hc, hxc, hyc, hne⟩ := (hiff x y).1 hR
  exact (hiff y x).2 ⟨c, hc, hyc, hxc, hne.symm⟩

theorem ChainConfig.not_symm (h : ChainConfig R X) :
    ¬ Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  obtain ⟨b, hb⟩ := exists_consecutive_of_getLast hlen
    (List.getLast?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega)))
  intro hsym
  exact hb.asymm hnd ((hiff _ _).1 (hsym.symm ⟨_, List.mem_toFinset.2 hb.mem_left⟩
    ⟨_, List.mem_toFinset.2 hb.mem_right⟩ ((hiff _ _).2 hb)))

theorem RingConfig.not_symm (h : RingConfig R X) :
    ¬ Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  obtain ⟨b, hb⟩ := exists_consecutive_of_getLast (by omega : 2 ≤ l.length)
    (List.getLast?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega)))
  intro hsym
  rcases (hiff _ _).1 (hsym.symm ⟨_, List.mem_toFinset.2 hb.mem_left⟩
      ⟨_, List.mem_toFinset.2 hb.mem_right⟩ ((hiff _ _).2 (.inl hb))) with hba | ⟨-, hhead⟩
  · exact hb.asymm hnd hba
  · obtain ⟨i, hi, hi'⟩ := hb
    have hi₁ : i + 1 < l.length := (List.getElem?_eq_some_iff.1 hi').1
    have e₁ := (List.Nodup.getElem?_inj hi₁ hnd).1
      (hi'.trans (List.getElem?_eq_getElem (by omega)).symm)
    rw [List.head?_eq_getElem?] at hhead
    have e₂ := (List.Nodup.getElem?_inj (by omega : 0 < l.length) hnd).1 (hhead.trans hi.symm)
    omega

theorem PairwiseConfig.partitionedStrong (h : PairwiseConfig R X) :
    PartitionedStrongReciprocity R X :=
  let ⟨P, hcells, hiff⟩ := h
  ⟨P, fun c hc ↦ strongReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 (by
    rw [hcells c hc]; omega), fun x hx y hy hne ↦ (hiff x y).2 ⟨c, hc, hx, hy, hne⟩⟩⟩

theorem ChainConfig.inclusiveAlternativeOrdering (h : ChainConfig R X) :
    InclusiveAlternativeOrdering R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  refine oneWayWeakReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 (by
    rw [List.toFinset_card_of_nodup hnd]; omega), fun x hx ↦ ?_⟩
  rcases exists_consecutive_or_getLast (List.mem_toFinset.1 hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, List.mem_toFinset.2 hy.mem_right, hy.ne hnd, .of_rel ((hiff x y).2 hy)⟩
  · obtain ⟨y, hy⟩ := exists_consecutive_of_getLast hlen hlast
    exact ⟨y, List.mem_toFinset.2 hy.mem_left, (hy.ne hnd).symm, .of_rel_symm ((hiff y x).2 hy)⟩

theorem RingConfig.oneWayWeak (h : RingConfig R X) : OneWayWeakReciprocity R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  refine oneWayWeakReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 (by
    rw [List.toFinset_card_of_nodup hnd]; omega), fun x hx ↦ ?_⟩
  rcases exists_consecutive_or_getLast (List.mem_toFinset.1 hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, List.mem_toFinset.2 hy.mem_right, hy.ne hnd, (hiff x y).2 (.inl hy)⟩
  · have hhead : l.head? = some l[0] :=
      List.head?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega))
    refine ⟨l[0], List.mem_toFinset.2 (List.getElem_mem _), fun hx0 ↦ ?_,
      (hiff x _).2 (.inr ⟨hlast, hhead⟩)⟩
    rw [List.getLast?_eq_getElem?, hx0] at hlast
    have := (List.Nodup.getElem?_inj (by omega : l.length - 1 < l.length) hnd).1
      (hlast.trans (List.getElem?_eq_getElem (by omega)).symm)
    omega

end Configurations

/-- The six configurations of a mutual event among more than two participants, each with the
review's example: strong (*The members of this family love one another*), pairwise (*The people
at the dinner party were married to one another*), chain (*The graduating students followed one
another up onto the stage*), radial (*The teacher and her pupils intimidated one another*), melee
(*The drunks in the pub were punching one another*) and ring (*The children chased each other
round in a ring*). -/
inductive ReciprocityType where
  | strong
  | pairwise
  | chain
  | radial
  | melee
  | ring
  deriving DecidableEq, Repr

/-- The relation shape each type denotes over a participant plurality. -/
def ReciprocityType.Realizes {A : Type*} [DecidableEq A] :
    ReciprocityType → (A → A → Prop) → Finset A → Prop
  | .strong,   R, X => StrongReciprocity R X
  | .pairwise, R, X => PairwiseConfig R X
  | .chain,    R, X => ChainConfig R X
  | .radial,   R, X => RadialConfig R X
  | .melee,    R, X => MeleeConfig R X
  | .ring,     R, X => RingConfig R X

section Realizes

variable {A : Type*} [DecidableEq A] {R : A → A → Prop} {X : Finset A} {t : ReciprocityType}

theorem ReciprocityType.Realizes.symm_iff (h : t.Realizes R X) (ht : t ≠ .melee) :
    (Std.Symm fun a b : (X : Set A) ↦ R a b) ↔ t = .strong ∨ t = .pairwise := by
  cases t with
  | strong => exact iff_of_true (symm_of_strongReciprocity h) (.inl rfl)
  | pairwise => exact iff_of_true (PairwiseConfig.symm h) (.inr rfl)
  | chain => exact iff_of_false (ChainConfig.not_symm h) (by decide)
  | radial => exact iff_of_false (RadialConfig.not_symm h) (by decide)
  | ring => exact iff_of_false (RingConfig.not_symm h) (by decide)
  | melee => exact absurd rfl ht

theorem ReciprocityType.Realizes.inclusiveAlternativeOrdering (h : t.Realizes R X)
    (ht : t ≠ .melee) (hX : 2 ≤ X.card) : InclusiveAlternativeOrdering R X := by
  cases t with
  | strong =>
    exact (StrongReciprocity.intermediate h).oneWayWeak.inclusiveAlternativeOrdering
  | pairwise =>
    exact ((PairwiseConfig.partitionedStrong h).weak.oneWayWeak
      (Finset.card_pos.1 (by omega))).inclusiveAlternativeOrdering
  | chain => exact ChainConfig.inclusiveAlternativeOrdering h
  | radial => exact RadialConfig.inclusiveAlternativeOrdering h
  | ring => exact (RingConfig.oneWayWeak h).inclusiveAlternativeOrdering
  | melee => exact absurd rfl ht

end Realizes

/-! ### Weak reciprocity among five children -/

/-- The seeing of the review's five children: the first sees the second and third, the second
the third, fourth and fifth, the third the first and second, the fourth the fifth, and the fifth
the third. -/
def Sees (a b : Fin 5) : Prop :=
  (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (3, 4), (4, 2)] :
    List (Fin 5 × Fin 5))

instance : DecidableRel Sees := fun _ _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- Each of the five children sees another and is seen by another, though not every child sees
every other: weak reciprocity without strong reciprocity. -/
theorem weakReciprocity_sees :
    WeakReciprocity Sees Finset.univ ∧ ¬ StrongReciprocity Sees Finset.univ := by
  refine ⟨by decide, fun h ↦ ?_⟩
  exact absurd ((strongReciprocity_iff.1 h).2 (Finset.mem_coe.2 (Finset.mem_univ 0))
    (Finset.mem_coe.2 (Finset.mem_univ 3)) (by decide)) (by decide)

end Nordlinger2023
