/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.English.Inflection
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Inflection
public import Linglib.Morphology.Realization
public import Linglib.Morphology.Root.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Bloomfield (1933): Language

Bloomfield defines a word as a minimum free form, a free form that does not consist of lesser
free forms, and sorts words by the free forms they contain: [*man* and *re-ceive* are primary,
*boy-ish* and *door-knob* secondary](##Bloomfield1933.primary_secondary). By the definition
[*poor John* is a phrase, and so is the compound *door-knob*](##Bloomfield1933.phrases), which
Bloomfield tells from a phrase by its single high stress. A suppletive alternant bears no
resemblance to the other alternants of its form, and Bloomfield finds them for underlying forms,
*bet-* of *good* and *went* of *go*, and for bound forms, the plural *-en* of *ox-en*: [the roots
*good* and *go* vary while *kind* and *ox* do not, and the plural varies while the comparative does
not](##Bloomfield1933.suppletion).

## Implementation notes

The words of the suppletion examples are spelled out by Vocabulary Insertion, a root and the head
of its secondary derivation each by its own items, into an inflectional paradigm of stems and
inflectional material (`Morphology.InflectionalParadigm`). Suppletion of an underlying form is
variance of a lexeme's stems across its cells, and suppletion of a bound form variance of a cell's
inflectional material across lexemes. An exponent is a list of morphs, the zero alternant the
empty one.

## TODO

Bloomfield tells phonetic modification, as in *child : children* and *feel : felt*, from
suppletion by whether the language shows parallel modifications; a Vocabulary Item for each
modified form would count it as suppletive.

## References

* [bloomfield-1933]
-/

@[expose] public section

namespace Bloomfield1933

open Morphology

/-! ### Words and phrases -/

/-- The English morpheme-word *man*. -/
def man : Morph := .root "man"
/-- The bound prefix of *re-ceive*. -/
def re : Morph := .pref "re"
/-- The bound root of *re-ceive*. -/
def ceive : Morph := .root "ceive"
/-- The English root *boy*. -/
def boy : Morph := .root "boy"
/-- The English suffix *-ish*. -/
def ish : Morph := .suff "ish"
/-- The English root *door*. -/
def door : Morph := .root "door"
/-- The English root *knob*. -/
def knob : Morph := .root "knob"
/-- The English root *poor*. -/
def poor : Morph := .root "poor"
/-- The English name *John*. -/
def john : Morph := .root "John"

/-- The free forms *man*, *re-ceive*, *boy*, *boy-ish*, *door*, *knob*, *door-knob*, *poor*,
*John* and *poor John*. -/
def freeForms : List (List Morph) :=
  [[man], [re, ceive], [boy], [boy, ish], [door], [knob], [door, knob], [poor], [john],
    [poor, john]]

/-- *man* and *re-ceive* are primary words, containing no free form, while *boy-ish* and
*door-knob* are secondary (§13.3). -/
theorem primary_secondary :
    IsPrimaryWord freeForms [man] ∧ IsPrimaryWord freeForms [re, ceive] ∧
      ¬ IsPrimaryWord freeForms [boy, ish] ∧ ¬ IsPrimaryWord freeForms [door, knob] := by
  decide

/-- *poor John* consists of two lesser free forms and is a phrase (§11.5); so is *door-knob*, which
"resembles a two-word phrase" and is a compound word by its stress (§11.6). *re-ceive*, a primary
word, is a minimum free form. -/
theorem phrases :
    ¬ IsMinimalFreeForm freeForms [poor, john] ∧ ¬ IsMinimalFreeForm freeForms [door, knob] ∧
      IsMinimalFreeForm freeForms [re, ceive] :=
  ⟨fun h ↦ absurd (h.2 [[poor], [john]] rfl (by decide) (by decide)) (by decide),
    fun h ↦ absurd (h.2 [[door], [knob]] rfl (by decide) (by decide)) (by decide),
    primary_secondary.2.1.isMinimalFreeForm⟩

/-! ### Suppletion -/

/-- The English root *kind*. -/
def kind : Morph := .root "kind"
/-- The English root *good*. -/
def good : Morph := .root "good"
/-- *bet-*, the suppletive alternant of *good*. -/
def bet : Morph := .root "bet"
/-- The English root *ox*. -/
def ox : Morph := .root "ox"
/-- The English root *card*. -/
def card : Morph := .root "card"
/-- The English root *go*. -/
def go : Morph := .root "go"
/-- *went*, the suppletive alternant of *go*. -/
def went : Morph := .root "went"
/-- The English root *land*. -/
def land : Morph := .root "land"
/-- *-en*, the suppletive alternant of the plural suffix. -/
def en : Morph := .suff "en"

/-- The lexemes of the examples, the regular *card* and *land* beside *ox* and *go*. -/
inductive Lexeme where
  | kind
  | good
  | ox
  | card
  | go
  | land
  deriving DecidableEq, Fintype

/-- The cells of the examples, the plain form and the comparative, the plural and the past. -/
inductive Cell where
  | plain
  | cmpr
  | pl
  | past
  deriving DecidableEq, Fintype

/-- The cell of a lexeme's secondary derivative. -/
def Lexeme.derived : Lexeme → Cell
  | .kind | .good => .cmpr
  | .ox | .card => .pl
  | .go | .land => .past

/-- The terminals of a word, a root and the head of its secondary derivation. -/
inductive Terminal where
  | root (l : Lexeme)
  | cmpr
  | pl
  | past
  deriving DecidableEq

/-- The head a cell adds to the root, none in the plain form. -/
def Cell.head? : Cell → Option Terminal
  | .plain => none
  | .cmpr => some .cmpr
  | .pl => some .pl
  | .past => some .past

open DistributedMorphology Morphology in
/-- The Vocabulary Items condition each suppletive alternant on its neighbour, *bet-* and *went* on
the comparative and the past to their right, the plural *-en* and the zero past on √OX and √GO to
their left, and set an elsewhere item beside it. -/
def vocabulary : RuleSet (VocabularyItem Terminal (List Morph)) :=
  [⟨{(0, .root .good), (1, .cmpr)}, [bet]⟩, {.root .good} ⟷ [good],
    ⟨{(0, .root .go), (1, .past)}, [went]⟩, {.root .go} ⟷ [go],
    {.root .kind} ⟷ [kind], {.root .ox} ⟷ [ox], {.root .card} ⟷ [card], {.root .land} ⟷ [land],
    {.cmpr} ⟷ [English.Inflection.er], ⟨{(0, .pl), (-1, .root .ox)}, [en]⟩,
    {.pl} ⟷ [English.Inflection.s], ⟨{(0, .past), (-1, .root .go)}, []⟩,
    {.past} ⟷ [English.Inflection.ed]]

open DistributedMorphology in
/-- The root of `l` in the cell `c`, with the cell's head to its right. -/
def rootSite (l : Lexeme) (c : Cell) : Neighborhood (Finset Terminal) :=
  ⟨{.root l}, [], (c.head?.map ({·})).toList⟩

open DistributedMorphology in
/-- The head `t` beside the root of `l`. -/
def headSite (l : Lexeme) (t : Terminal) : Neighborhood (Finset Terminal) := ⟨{t}, [{.root l}], []⟩

open DistributedMorphology in
/-- The exponent of the head of `l`'s cell `c`, the empty list where the cell adds no head. -/
def headExponent (l : Lexeme) (c : Cell) : Option (List Morph) :=
  match c.head? with
  | none => some []
  | some t => subsetPrinciple vocabulary (headSite l t)

open DistributedMorphology in
/-- The pairs of a root's exponent and the inflectional material beside it, in the plain form and
in each lexeme's derivative. -/
def parts : Realization Lexeme Cell (List Morph × List Morph) :=
  ⟨fun l c ↦ if c = .plain ∨ c = l.derived then
    (Option.map₂ Prod.mk (subsetPrinciple vocabulary (rootSite l c)) (headExponent l c)).toFinset
    else ∅⟩

/-- The inflectional paradigm of the examples, each word a stem followed by its inflectional
material. -/
def english : InflectionalParadigm Lexeme Cell (List Morph) (List Morph) (List Morph) :=
  ⟨parts, (· ++ ·)⟩

open DistributedMorphology in
/-- The word of `l` in the cell `c`, the root's exponent followed by the head's. -/
def word (l : Lexeme) (c : Cell) : List Morph :=
  (subsetPrinciple vocabulary (rootSite l c)).getD [] ++ (headExponent l c).getD []

theorem english_realize_eq :
    ∀ l, english.realization.realize l .plain = {word l .plain} ∧
      english.realization.realize l l.derived = {word l l.derived} := by
  decide

-- §13.4, §13.7
theorem derived_words :
    [Lexeme.kind, .good, .ox, .card, .go, .land].map (fun l ↦ word l l.derived) =
      [[kind, English.Inflection.er], [bet, English.Inflection.er], [ox, en],
        [card, English.Inflection.s], [went], [land, English.Inflection.ed]] := by
  decide

/-- *good* and *go* have the suppletive alternants *bet-* and *went* of the underlying form, while
*kind* and *ox* keep theirs, and the plural has the suppletive alternant *-en* after *ox*, while
the comparative keeps *-er* (§13.7). -/
theorem suppletion :
    english.stem.IsSuppletive .good ∧ english.stem.IsSuppletive .go ∧
      english.stem.IsInvariant .kind ∧ english.stem.IsInvariant .ox ∧
      english.inflection.transpose.IsSuppletive .pl ∧
      english.inflection.transpose.IsInvariant .cmpr := by
  decide

-- §13.7: "a zero-alternant replaces the bound form, and a suppletive alternant the underlying
-- form, in cases like ... go : went"
theorem go_went : english.realization.realize .go .past = {[went]} ∧
    english.inflection.realize .go .past = {[]} ∧
    english.inflection.transpose.IsSuppletive .past := by
  decide

theorem not_isCanonical : ¬ english.IsCanonical := fun h ↦ h.not_isSuppletive.1 .good suppletion.1

-- *ox* and *card* differ in their plural, so they do not inflect alike
example : english.inflection.realize .ox ≠ english.inflection.realize .card :=
  fun h ↦ absurd (congrFun h .pl) (by decide)

end Bloomfield1933
