module

public import Linglib.Syntax.WordOrder
public import Linglib.Fragments.Slavic.Russian.Agreement
public import Linglib.Data.Examples.AlexeyenkoZeijlstra2025
public import Linglib.Data.Examples.Languages
public import Linglib.Data.StructureDataset.AlexeyenkoZeijlstra2025

/-!
# Alexeyenko and Zeijlstra (2025): linearization of complex modifiers

The Head-Final Filter of [williams-1982] bars a prenominal modifier whose head is followed by
one of its dependents, so that the order A–XP–N is out. This file formalizes the
Modifier-Noun Adjacency Generalization of [alexeyenko-zeijlstra-2025], which replaces it and
covers the mirror order N–XP–A of postnominal adjectives as well.

An adjectival form is used at some positions and its agreement marker is specified for some
features. The adjectives of a language are φ/κ-complete, `Language.PhiKappaComplete`, if some
form is used both attributively and predicatively and is specified for every φ-feature of the
noun phrase and for case. Adjectives that are not φ/κ-complete take an attributivizer, which
must be adjacent to the adjective when it is an overt or null affix on it,
`AttrStatus.Adjacent`, as the Input Correspondence Principle of [ackema-neeleman-2004]
requires of an affix and its host. We define `Language.Possible l o`, for an order `o` of
adjective and noun: adjective phrases of `l` have the internal order that puts the dependent
next to the noun, and the adjectives are φ/κ-complete or their attributivizer need not be
adjacent to them.

`table3_predicted` checks `Language.Possible` against the paper's sample for each language the
paper analyses, and `intervention_rows` against its examples, where the positions of the
adjective, the noun and the dependent are spans of the row. The agreement paradigms that the
analysis assigns are checked against the rows that show them, `marker_rows`, with the Russian
long and short forms those of the Fragment, `russian_form_rows`. `degree_rows` covers a degree
word between adjective and noun, which a null affix may attach to and an overt one may not.

## Implementation notes

The attributivizer of Dutch is recorded as an overt affix, although it is null with indefinite
neuter singular nouns: the two statuses agree on adjacency, `attributivizer_rows`, and differ
only before a degree word, where `degree_rows` reads the status from the row.

## TODO

* The definiteness of the Icelandic and Serbo-Croatian rows is recorded and not read: no theorem
  derives the definiteness feature of their attributive forms from the distribution of the
  strong and weak, or short and long, forms.
* Chácobo and Eastern Oromo, whose rows and sample values are recorded, have no analysis here.

## References

* [alexeyenko-zeijlstra-2025]
* [williams-1982]
* [ackema-neeleman-2004]
-/

@[expose] public section

namespace AlexeyenkoZeijlstra2025

open Examples
open StructureDataset (AdjectiveOrder Intervention table3)

/-! ### Agreement marking -/

/-- An adjectival form is used at some positions, and its agreement marker is specified for some
features, a bare form's for none. -/
structure Form where
  uses : Finset Agreement.Position
  features : Finset Agreement.Dimension
  deriving DecidableEq

/-- An adjectival target of the Russian fragment as a form, its marker specified for the
dimensions the target inflects for. -/
def form {F : Type*} (t : Agreement.Target Russian.Agreement.Value F) : Form :=
  ⟨t.positions, t.inflection⟩

/-! ### Attributivizers -/

/-- Morphophonological status of the attributivizer. -/
inductive AttrStatus
  | adjectivalAffix
  | null
  | clitic
  | freeWord
  | nominalAffix
  deriving DecidableEq

/-- An affix takes the head it selects as its host (the Input Correspondence Principle), and the
paper extends this to null affixes; clitics, free words and affixes on the noun leave the
adjective free. -/
def AttrStatus.Adjacent : AttrStatus → Prop
  | .adjectivalAffix | .null => True
  | _ => False

instance : DecidablePred AttrStatus.Adjacent := fun s ↦ by
  cases s <;> simp [AttrStatus.Adjacent] <;> infer_instance

/-- Hosts an attributivizer may attach to when a degree word closes the AP. -/
inductive Host
  | adjective
  | degreeWord

/-- A null affix attaches to the head of the phrase it selects, DegP included; an overt affix may
attach to a non-lexical head only if that head is itself an affix (the Affix Continuity
Constraint), which *enough* and *genoeg* are not. -/
def AttrStatus.MayHost : AttrStatus → Host → Prop
  | .adjectivalAffix, .degreeWord => False
  | _, _ => True

instance : DecidableRel AttrStatus.MayHost := fun s h ↦ by
  cases s <;> cases h <;> simp [AttrStatus.MayHost] <;> infer_instance

/-- The status of the attributivizer a row shows. -/
def _root_.AlexeyenkoZeijlstra2025.Examples.Attributivizer.status : Attributivizer → AttrStatus
  | .affix => .adjectivalAffix
  | .null => .null
  | .clitic => .clitic

/-! ### The languages of the paper -/

/-- The AP-internal order that puts the dependent between adjective and noun. -/
def _root_.AlexeyenkoZeijlstra2025.StructureDataset.AdjectiveOrder.intervening :
    AdjectiveOrder → HeadDirection
  | .adjectiveNoun => .headInitial
  | .nounAdjective => .headFinal

theorem intervening_injective : Function.Injective AdjectiveOrder.intervening := by
  rintro (_ | _) (_ | _) h <;> first | rfl | cases h

/-- A language the paper analyses. -/
inductive Language
  | greek | russian | latin | kalaallisut | italian | german | dutch | english | icelandic
  | serboCroatian | mandarin | tagalog | farsi | atong | basque | japanese
  deriving DecidableEq, Repr, Fintype

namespace Language

/-- The Glottocode of a language. -/
def glottocode : Language → Glottocode
  | greek => .modernGreek
  | russian => .russian
  | latin => .latin
  | kalaallisut => .kalaallisut
  | italian => .italian
  | german => .german
  | dutch => .dutch
  | english => .english
  | icelandic => .icelandic
  | serboCroatian => .serbianCroatianBosnian
  | mandarin => .mandarinChinese
  | tagalog => .tagalog
  | farsi => .westernFarsi
  | atong => .atongIndia
  | basque => .basque
  | japanese => .japanese

theorem glottocode_injective : Function.Injective glottocode := by decide

/-- The orders of adjective and noun a language allows. -/
def orders : Language → Finset AdjectiveOrder
  | italian => {.adjectiveNoun, .nounAdjective}
  | kalaallisut | farsi | atong | basque => {.nounAdjective}
  | _ => {.adjectiveNoun}

/-- The AP-internal orders a language's predicative adjectives allow; Japanese APs are
strictly head-final. -/
def apOrders : Language → Finset HeadDirection
  | german | dutch | icelandic | mandarin => {.headInitial, .headFinal}
  | kalaallisut | farsi | atong | basque | japanese => {.headFinal}
  | _ => {.headInitial}

/-- Gender, number and case. -/
def φκ : Finset Agreement.Dimension := {.number, .gender, .case}

/-- A language's adjectival forms. Greek and Latin adjectives have one form, inflected for
gender, number and case in both uses, and Kalaallisut's affixal number and case agreement is
likewise shared; Russian's are the Fragment's long and short adjectives; Italian's one form
agrees in gender and number but never case. German and Dutch predicative adjectives are
bare, the attributive forms carrying gender, number and case or, in Dutch, a schwa sensitive
to gender, number and definiteness; Icelandic and Serbo-Croatian attributive forms add
definiteness to what the predicative forms carry. The rest have one uninflected form. -/
def forms : Language → Finset Form
  | greek | latin => {⟨{.attributive, .predicate}, φκ⟩}
  | russian => {form Russian.Agreement.longAdjective, form Russian.Agreement.shortAdjective}
  | kalaallisut => {⟨{.attributive, .predicate}, {.number, .case}⟩}
  | italian => {⟨{.attributive, .predicate}, {.number, .gender}⟩}
  | german => {⟨{.attributive}, φκ⟩, ⟨{.predicate}, ∅⟩}
  | dutch => {⟨{.attributive}, {.number, .gender, .definiteness}⟩, ⟨{.predicate}, ∅⟩}
  | icelandic | serboCroatian => {⟨{.attributive}, insert .definiteness φκ⟩, ⟨{.predicate}, φκ⟩}
  | _ => {⟨{.attributive, .predicate}, ∅⟩}

/-- The φ-features of a language's DP. Case is not among them: the paper takes it to be
present in every DP whether or not it is realized. -/
def phi : Language → Finset Agreement.Dimension
  | greek | russian | latin | italian | german => {.number, .gender}
  | kalaallisut | english => {.number}
  | dutch | icelandic | serboCroatian => {.number, .gender, .definiteness}
  | _ => ∅

/-- A language's adjectives take no attributivizer, a null or overt adjectival affix, or a clitic
such as Mandarin *de*, the Tagalog linker or the Farsi ezafe. -/
def attributivizer : Language → Option AttrStatus
  | greek | russian | latin | kalaallisut => none
  | italian | english | basque | japanese => some .null
  | german | dutch | icelandic | serboCroatian => some .adjectivalAffix
  | mandarin | tagalog | farsi | atong => some .clitic

/-- A language's adjectives are φ/κ-complete: some form is used both attributively and
predicatively, and its overt marker is specified for every feature of the DP, case
included. -/
def PhiKappaComplete (l : Language) : Prop :=
  ∃ f ∈ l.forms, {.attributive, .predicate} ⊆ f.uses ∧ insert .case l.phi ⊆ f.features

instance (l : Language) : Decidable l.PhiKappaComplete := by
  unfold PhiKappaComplete; infer_instance

theorem phiKappaComplete_iff (l : Language) :
    l.PhiKappaComplete ↔ l = greek ∨ l = russian ∨ l = latin ∨ l = kalaallisut := by
  cases l <;> decide

theorem attributivizer_ne_none (l : Language) (h : ¬ l.PhiKappaComplete) :
    l.attributivizer ≠ none := by
  revert h; cases l <;> decide

/-- An XP may separate the adjective from the noun in the given order when the AP order creates
the configuration and either the adjectives are φ/κ-complete or the attributivizer does not need
to be adjacent to the adjective. -/
def Possible (l : Language) (o : AdjectiveOrder) : Prop :=
  o.intervening ∈ l.apOrders ∧ (l.PhiKappaComplete ∨ ∃ a ∈ l.attributivizer, ¬ a.Adjacent)

instance (l : Language) (o : AdjectiveOrder) : Decidable (l.Possible o) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ ∃ a ∈ _, _)))

-- (34)
theorem mag (l : Language) (o : AdjectiveOrder) (h : l.Possible o) :
    l.PhiKappaComplete ∨ ∃ a ∈ l.attributivizer, ¬ a.Adjacent :=
  h.2

-- (44)
theorem possible_adjectiveNoun :
    ¬ japanese.Possible .adjectiveNoun ∧ greek.Possible .adjectiveNoun ∧
      tagalog.Possible .adjectiveNoun ∧ ¬ german.Possible .adjectiveNoun ∧
      ¬ english.Possible .adjectiveNoun := by
  decide

-- (45)
theorem possible_nounAdjective :
    ¬ italian.Possible .nounAdjective ∧ kalaallisut.Possible .nounAdjective ∧
      farsi.Possible .nounAdjective ∧ ¬ basque.Possible .nounAdjective := by
  decide

end Language

/-! ### The sample -/

/-- Each language of Table 3 that the paper analyses allows an XP between adjective and noun
exactly when the analysis makes it possible. -/
theorem table3_predicted :
    ∀ r ∈ table3, ∀ l : Language, r.language.glottocode = some l.glottocode →
      ∀ o ∈ r.adjectiveOrder, (l.Possible o.code ↔ ∃ i ∈ r.intervention, i.code = .possible) := by
  decide +kernel

/-- Neither order of adjective and noun settles whether an XP may intervene: each block of
Table 3 has languages of both kinds. -/
theorem order_insufficient (o : AdjectiveOrder) :
    ∃ r ∈ table3, ∃ s ∈ table3, (∃ a ∈ r.adjectiveOrder, a.code = o) ∧
      (∃ a ∈ s.adjectiveOrder, a.code = o) ∧ (∃ i ∈ r.intervention, i.code = .possible) ∧
      ∃ i ∈ s.intervention, i.code = .impossible := by
  cases o <;> decide +kernel

/-! ### Rows -/

/-- The position of the first word of the span of an example with the given label. -/
def pos (x : Example) (l : SpanLabel) : Option ℕ :=
  (x.datum.spans.find? (label? · = some l)).map (·.start)

/-- The order of the head and the noun of an example. -/
def order (x : Example) : Option AdjectiveOrder :=
  (pos x .head).bind fun h ↦ (pos x .noun).map fun n ↦
    if h < n then .adjectiveNoun else .nounAdjective

/-- The dependent of the head stands between the head and the noun. -/
def Intervenes (x : Example) : Prop :=
  ∃ h ∈ pos x .head, ∃ n ∈ pos x .noun, ∃ d ∈ pos x .dependent, h < d ∧ d < n ∨ n < d ∧ d < h

instance (x : Example) : Decidable (Intervenes x) := by
  unfold Intervenes; infer_instance

/-- An adjective with a noun is attributive, one without is predicative. -/
def use (x : Example) : Agreement.Position :=
  if (pos x .noun).isSome then .attributive else .predicate

example : order .az2025_1b = some .adjectiveNoun ∧ Intervenes .az2025_1b := by decide +kernel
example : order .az2025_4b = some .nounAdjective ∧ Intervenes .az2025_4b := by decide +kernel
example : ¬ Intervenes .az2025_36b ∧ ¬ Intervenes .az2025_41b := by decide +kernel

/-- An example whose dependent stands between the adjective and the noun is acceptable exactly
when the analysis of its language makes the intervention possible. -/
theorem intervention_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode → x.construction = none →
      Intervenes x → ∀ o ∈ order x, (x.datum.judgment = .acceptable ↔ l.Possible o) := by
  decide +kernel

theorem order_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode → x.construction = none →
      x.datum.judgment = .acceptable → ∀ o ∈ order x, o ∈ l.orders := by
  decide +kernel

theorem apOrder_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode →
      x.datum.judgment = .acceptable → pos x .noun = none →
      ∀ h ∈ pos x .head, ∀ d ∈ pos x .dependent, HeadDirection.ofLT h d ∈ l.apOrders := by
  decide +kernel

theorem attributivizer_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode →
      ∀ s ∈ x.attributivizer, ∀ a ∈ l.attributivizer, (s.status.Adjacent ↔ a.Adjacent) := by
  decide +kernel

/-- An adjective with or without an agreement marker is acceptable in a use exactly when its
language has a form for that use that is marked or bare accordingly. -/
theorem marker_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode → ∀ m ∈ x.marker,
      (x.datum.judgment = .acceptable ↔
        ∃ f ∈ l.forms, use x ∈ f.uses ∧ (f.features = ∅ ↔ m = .bare)) := by
  decide +kernel

-- Table 4
theorem russian_form_rows :
    ∀ x : Example, x.datum.language = Glottocode.russian →
      (x.adjectiveForm = some .long →
        (x.datum.judgment = .acceptable ↔ use x ∈ Russian.Agreement.longAdjective.positions)) ∧
      (x.adjectiveForm = some .short →
        (x.datum.judgment = .acceptable ↔ use x ∈ Russian.Agreement.shortAdjective.positions)) := by
  decide +kernel

/-- With a degree word between adjective and noun, an example is acceptable exactly when its
attributivizer may attach to the degree word. -/
theorem degree_rows :
    ∀ x : Example, (pos x .degree).isSome →
      ∀ s ∈ x.attributivizer, (x.datum.judgment = .acceptable ↔ s.status.MayHost .degreeWord) := by
  decide +kernel

end AlexeyenkoZeijlstra2025
