module

public import Linglib.Syntax.WordOrder
public import Linglib.Fragments.Slavic.Russian.Agreement
public import Linglib.Fragments.German.Agreement
public import Linglib.Fragments.Dutch.Agreement
public import Linglib.Fragments.Greek.StandardModern.Agreement
public import Linglib.Data.Examples.AlexeyenkoZeijlstra2025
public import Linglib.Data.Examples.Languages
public import Linglib.Data.StructureDataset.AlexeyenkoZeijlstra2025
public import Mathlib.Data.List.Permutation

/-!
# Alexeyenko and Zeijlstra (2025): linearization of complex modifiers

The Head-Final Filter of [williams-1982] bars a prenominal modifier whose head is followed by
one of its dependents, so that the order A–XP–N is out. This file formalizes the account of
[alexeyenko-zeijlstra-2025], which replaces the filter and covers the mirror order N–XP–A of
postnominal adjectives as well.

An attributive adjective with its noun is a string of items: the adjective, its dependent, a
degree word, the noun, and an attributivizer. The adjectives of a language need no attributivizer
when they are φ/κ-complete, `Language.PhiKappaComplete`: some form is used both attributively and
predicatively and is specified for every φ-feature of the noun phrase and for case. Otherwise
they take one. An attributivizer that is an affix on the adjective, overt or null, is adjacent to
its host, as the Input Correspondence Principle of [ackema-neeleman-2004] requires, and adjacent
to the noun, `Affixed s`; its host is the head of the phrase it selects, the degree word if there
is one. A clitic or a free word is unconstrained.

We define `Language.Possible l o`, for an order `o` of adjective and noun: some string of the
language's items in that order, with the adjective and its dependent in an order the language
allows, has the dependent between the adjective and the noun, and has its attributivizer affixed
if the language's is an affix. `Language.possible_iff` shows that this is the paper's pair of
decision trees, and `Affixed.not_intervenes` is the reason an affix excludes the dependent: an
item adjacent to both the adjective and the noun leaves no room between them.

`table3_predicted` checks `Language.Possible` against the paper's sample for each language the
paper analyses, and `intervention_rows` against its examples, whose strings are read off the
spans of the rows. `licit_rows` checks well-formedness directly on the rows that show their
attributivizer, among them those with a degree word. The agreement paradigms the analysis
assigns are checked against the rows that show them, `marker_rows`. The Greek, Russian, German
and Dutch paradigms are those of the Fragments, and `russian_form_rows` checks the long and
short forms.

## Implementation notes

An affixal attributivizer is required to be adjacent to the noun, and a clitic is not: the
Atong attributive clitic follows the adjective phrase on the side away from the noun.

A language records only whether its attributivizer is an affix. That of Dutch is overt, and null
with indefinite neuter singular nouns: the two agree on whether an XP may intervene, and differ
only before a degree word, where `licit_rows` reads the attributivizer from the row.

## TODO

* The definiteness of the Icelandic and Serbo-Croatian rows is recorded and not read: no theorem
  derives the definiteness feature of their attributive forms from the distribution of the
  strong and weak, or short and long, forms.
* Chácobo and Eastern Oromo, whose rows and sample values are recorded, have no analysis here.
* A row that lacks an attributivizer its language requires, as the bare adjective with a degree
  word before a Dutch common noun does, is not covered by `licit_rows`.

## References

* [alexeyenko-zeijlstra-2025]
* [williams-1982]
* [ackema-neeleman-2004]
-/

@[expose] public section

namespace AlexeyenkoZeijlstra2025

open Examples List
open StructureDataset (AdjectiveOrder Intervention table3)

/-! ### Agreement marking -/

/-- An adjectival form is used at some positions, and its agreement marker is specified for some
features, a bare form's for none. -/
structure Form where
  uses : Finset Agreement.Position
  features : Finset Agreement.Dimension
  deriving DecidableEq

/-- An adjectival target of a fragment as a form, its marker specified for the dimensions the
target inflects for. -/
def form {V : Agreement.Dimension → Type*} {F : Type*} (t : Agreement.Target V F) : Form :=
  ⟨t.positions, t.inflection⟩

/-! ### Strings -/

/-- The items of an attributive adjective phrase and its noun: the adjective, a dependent of
the adjective, a degree word, the attributivizer and the noun. -/
inductive Item
  | adj
  | dep
  | deg
  | attr
  | noun
  deriving DecidableEq

/-- Two items stand next to each other in a string. -/
def Adjacent (a b : Item) (s : List Item) : Prop := [a, b] <:+: s ∨ [b, a] <:+: s

instance (a b : Item) (s : List Item) : Decidable (Adjacent a b s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The dependent stands between the adjective and the noun. -/
def Intervenes (s : List Item) : Prop := [.adj, .dep, .noun] <+ s ∨ [.noun, .dep, .adj] <+ s

instance (s : List Item) : Decidable (Intervenes s) := inferInstanceAs (Decidable (_ ∨ _))

/-- The order of adjective and noun in a string that has both. -/
def order (s : List Item) : Option AdjectiveOrder :=
  if [.adj, .noun] <+ s then some .adjectiveNoun
  else if [.noun, .adj] <+ s then some .nounAdjective else none

/-- The order of the adjective and its dependent in a string that has both. -/
def apOrder (s : List Item) : Option HeadDirection :=
  if [.adj, .dep] <+ s then some .headInitial
  else if [.dep, .adj] <+ s then some .headFinal else none

/-- The head of the phrase the attributivizer selects: the degree word where there is one, and
otherwise the adjective. -/
def host (s : List Item) : Item := if .deg ∈ s then .deg else .adj

/-! ### Attributivizers -/

/-- The attributivizer is affixed in a string: it stands next to its host, the head of the
phrase it selects (the Input Correspondence Principle, which the paper extends to null affixes),
and next to the noun. -/
def Affixed (s : List Item) : Prop := Adjacent .attr (host s) s ∧ Adjacent .attr .noun s

instance (s : List Item) : Decidable (Affixed s) := inferInstanceAs (Decidable (_ ∧ _))

/-- A string of adjective, dependent, noun and an affixed attributivizer does not have the
dependent between the adjective and the noun. -/
theorem Affixed.not_intervenes {s : List Item} (hs : s.Perm [.adj, .dep, .noun, .attr])
    (h : Affixed s) : ¬ Intervenes s := by
  have key : ∀ s ∈ [Item.adj, .dep, .noun, .attr].permutations', Affixed s → ¬ Intervenes s := by
    decide
  exact key s (mem_permutations'.2 hs) h

/-- A string is well formed for the attributivizer a row shows. A clitic is unconstrained, an
affix is affixed, and an overt affix does not take a degree word as its host (the Affix
Continuity Constraint, a degree word not being an affix). -/
def _root_.AlexeyenkoZeijlstra2025.Examples.Attributivizer.Licit :
    Attributivizer → List Item → Prop
  | .clitic, _ => True
  | .null, s => Affixed s
  | .affix, s => Affixed s ∧ host s = .adj

instance (a : Attributivizer) (s : List Item) : Decidable (a.Licit s) := by
  cases a <;> unfold Attributivizer.Licit <;> infer_instance

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
  | greek | russian | latin | german | dutch | english | icelandic | serboCroatian | mandarin
  | tagalog | japanese => {.adjectiveNoun}

/-- The AP-internal orders a language's predicative adjectives allow; Japanese APs are
strictly head-final. -/
def apOrders : Language → Finset HeadDirection
  | german | dutch | icelandic | mandarin => {.headInitial, .headFinal}
  | kalaallisut | farsi | atong | basque | japanese => {.headFinal}
  | greek | russian | latin | italian | english | serboCroatian | tagalog => {.headInitial}

/-- Gender, number and case. -/
def φκ : Finset Agreement.Dimension := {.number, .gender, .case}

/-- A language's adjectival forms. Greek's are the adjective of its Fragment, Russian's the long
and short adjectives of its Fragment, and German's and Dutch's the attributive and the bare
predicative adjectives of theirs. Latin adjectives have one form, inflected for gender, number
and case in both uses, and Kalaallisut's affixal number and case agreement is likewise shared;
Italian's one form agrees in gender and number but never case. Icelandic and Serbo-Croatian
attributive forms add definiteness to what the predicative forms carry. The rest have one
uninflected form. -/
def forms : Language → Finset Form
  | greek => {form Greek.StandardModern.Agreement.adjective}
  | latin => {⟨{.attributive, .predicate}, φκ⟩}
  | russian => {form Russian.Agreement.longAdjective, form Russian.Agreement.shortAdjective}
  | kalaallisut => {⟨{.attributive, .predicate}, {.number, .case}⟩}
  | italian => {⟨{.attributive, .predicate}, {.number, .gender}⟩}
  | german => {form German.Agreement.strongAdjective, form German.Agreement.weakAdjective,
      form German.Agreement.predicativeAdjective}
  | dutch => {form Dutch.Agreement.attributiveAdjective,
      form Dutch.Agreement.predicativeAdjective}
  | icelandic | serboCroatian => {⟨{.attributive}, insert .definiteness φκ⟩, ⟨{.predicate}, φκ⟩}
  | english | mandarin | tagalog | farsi | atong | basque | japanese =>
    {⟨{.attributive, .predicate}, ∅⟩}

/-- The φ-features of a language's DP. Case is not among them: the paper takes it to be
present in every DP whether or not it is realized. -/
def phi : Language → Finset Agreement.Dimension
  | greek | russian | latin | italian | german => {.number, .gender}
  | kalaallisut | english => {.number}
  | dutch | icelandic | serboCroatian => {.number, .gender, .definiteness}
  | mandarin | tagalog | farsi | atong | basque | japanese => ∅

/-- The attributivizer of a language is an affix on the adjective, overt as in German or null as
in English, and not a clitic such as Mandarin *de*, the Tagalog linker or the Farsi ezafe. It
holds of no language whose adjectives take no attributivizer. -/
def AffixalAttributivizer : Language → Prop
  | italian | english | basque | japanese | german | dutch | icelandic | serboCroatian => True
  | mandarin | tagalog | farsi | atong | greek | russian | latin | kalaallisut => False

instance : DecidablePred AffixalAttributivizer := fun l ↦ by
  cases l <;> unfold AffixalAttributivizer <;> infer_instance

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

/-- The items of an attributive adjective with a dependent: an attributivizer is among them
unless the adjectives are φ/κ-complete. -/
def items (l : Language) : List Item :=
  [.adj, .dep, .noun] ++ if l.PhiKappaComplete then [] else [.attr]

/-- An XP may separate the adjective from the noun in the given order: some string of the
language's items in that order, with adjective and dependent in an order the language allows,
has the dependent between adjective and noun, and its attributivizer affixed if the language's
is an affix. -/
def Possible (l : Language) (o : AdjectiveOrder) : Prop :=
  ∃ s ∈ l.items.permutations', order s = some o ∧ (∃ d ∈ apOrder s, d ∈ l.apOrders) ∧
    Intervenes s ∧ (l.AffixalAttributivizer → Affixed s)

instance (l : Language) (o : AdjectiveOrder) : Decidable (l.Possible o) := by
  unfold Possible; infer_instance

/-- The decision trees: an XP may intervene exactly when the AP order creates the configuration
and either the adjectives are φ/κ-complete or the attributivizer is not an affix on the
adjective. -/
theorem possible_iff (l : Language) (o : AdjectiveOrder) :
    l.Possible o ↔
      o.intervening ∈ l.apOrders ∧ (l.PhiKappaComplete ∨ ¬ l.AffixalAttributivizer) := by
  cases l <;> cases o <;> decide

-- (34)
theorem mag (l : Language) (o : AdjectiveOrder) (h : l.Possible o) :
    l.PhiKappaComplete ∨ ¬ l.AffixalAttributivizer :=
  ((possible_iff l o).1 h).2

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

-- Table 3
theorem order_insufficient (o : AdjectiveOrder) :
    ∃ r ∈ table3, ∃ s ∈ table3, (∃ a ∈ r.adjectiveOrder, a.code = o) ∧
      (∃ a ∈ s.adjectiveOrder, a.code = o) ∧ (∃ i ∈ r.intervention, i.code = .possible) ∧
      ∃ i ∈ s.intervention, i.code = .impossible := by
  cases o <;> decide +kernel

/-! ### Rows -/

/-- The item a span marks. -/
def Item.ofLabel : SpanLabel → Item
  | .head => .adj
  | .noun => .noun
  | .dependent => .dep
  | .degree => .deg
  | .attributivizer => .attr

/-- The place of a span's item in the string of its row: a suffix or enclitic follows the word
that carries it, and a null attributivizer precedes the word it is placed before. -/
def place (l : SpanLabel) (s : Datum.Span) : ℕ :=
  3 * s.start + if l = .attributivizer then (if s.length = 0 then 0 else 2) else 1

/-- The string of an example: the items its spans mark, in the order of the words. -/
def items (x : Example) : List Item :=
  let marked := x.datum.spans.filterMap fun s ↦ (label? s).map fun l ↦ (place l s, Item.ofLabel l)
  (range (3 * (x.datum.glossedTokens.length + 1))).flatMap fun k ↦
    (marked.filter (·.1 = k)).map (·.2)

/-- An adjective with a noun is attributive, one without is predicative. -/
def use (x : Example) : Agreement.Position :=
  if .noun ∈ items x then .attributive else .predicate

example : items .az2025_1b = [.adj, .dep, .noun] := by decide +kernel
example : items .az2025_4b = [.noun, .attr, .dep, .adj] := by decide +kernel
example : items .az2025_27 = [.adj, .dep, .attr, .noun] := by decide +kernel
example : items .az2025_66c = [.adj, .attr, .dep, .noun] := by decide +kernel
example : items .az2025_15 = [.adj, .deg, .attr, .noun] := by decide +kernel

/-- An example whose dependent stands between the adjective and the noun is acceptable exactly
when the analysis of its language makes the intervention possible. -/
theorem intervention_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode → x.construction = none →
      Intervenes (items x) →
      ∀ o ∈ order (items x), (x.datum.judgment = .acceptable ↔ l.Possible o) := by
  decide +kernel

/-- An example that shows its attributivizer is acceptable exactly when its string is well
formed for the attributivizer. -/
theorem licit_rows :
    ∀ x : Example, ∀ a ∈ x.attributivizer,
      (x.datum.judgment = .acceptable ↔ a.Licit (items x)) := by
  decide +kernel

theorem order_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode → x.construction = none →
      x.datum.judgment = .acceptable → ∀ o ∈ order (items x), o ∈ l.orders := by
  decide +kernel

theorem apOrder_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode →
      x.datum.judgment = .acceptable → .noun ∉ items x →
      ∀ d ∈ apOrder (items x), d ∈ l.apOrders := by
  decide +kernel

theorem attributivizer_rows :
    ∀ (x : Example) (l : Language), x.datum.language = l.glottocode →
      ∀ a ∈ x.attributivizer, (a ≠ .clitic ↔ l.AffixalAttributivizer) := by
  decide +kernel

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

end AlexeyenkoZeijlstra2025
