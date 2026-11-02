/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Root.Basic
public import Linglib.Morphology.Root.Certificates
public import Mathlib.Tactic.DeriveFintype

/-!
# Bloomfield (1933): Language

Bloomfield defines a word as a minimum free form, a free form that does not consist of lesser
free forms, and sorts words by the free forms they contain: [*man* and *re-ceive* are primary,
*boy-ish* and *door-knob* secondary](##Bloomfield1933.primary_secondary). By the definition
[*poor John* is a phrase, and so is the compound *door-knob*](##Bloomfield1933.phrases), which
Bloomfield tells from a phrase by its single high stress. A suppletive alternant bears no
resemblance to the other alternants of its form, and [suppletion of a bound form, as in *ox-en*,
leaves the underlying form in place, while suppletion of the underlying form, as in *bet-ter* and
*went*, replaces it](##Bloomfield1933.suppletion).

## Implementation notes

A word is a list of morphs labelled as roots and affixes following Bloomfield's analysis, and its
underlying form is its morphs other than the bound forms, so that *bet-*, the suppletive
alternant of *good*, is the underlying form of *better*. *went* is one morph, its zero past
suffix not written.

## TODO

Bloomfield tells phonetic modification of the underlying form, as in *child : children* and
*feel : felt*, from its suppletion by whether the language shows parallel modifications; the
underlying forms here vary under both.

## References

* [bloomfield-1933]
-/

@[expose] public section

namespace Bloomfield1933

open Morphology Morphology.Root

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
/-- The English comparative suffix *-er*. -/
def er : Morph := .suff "er"
/-- The English root *good*. -/
def good : Morph := .root "good"
/-- *bet-*, the suppletive alternant of *good*. -/
def bet : Morph := .root "bet"
/-- The English root *ox*. -/
def ox : Morph := .root "ox"
/-- *-en*, the suppletive alternant of the plural suffix. -/
def en : Morph := .suff "en"
/-- The English root *go*. -/
def go : Morph := .root "go"
/-- *went*, the suppletive alternant of *go*. -/
def went : Morph := .root "went"

/-- The words of Bloomfield's suppletion examples. -/
inductive Lexeme where
  | kind
  | good
  | ox
  | go
  deriving DecidableEq, Fintype

/-- The underlying word and its secondary derivative, the comparative, plural or past. -/
inductive Cell where
  | plain
  | derived
  deriving DecidableEq, Fintype

/-- `word l c` is the word of `l` in the cell `c`. -/
def word : Lexeme → Cell → List Morph
  | .kind, .plain => [kind]
  | .kind, .derived => [kind, er]
  | .good, .plain => [good]
  | .good, .derived => [bet, er]
  | .ox, .plain => [ox]
  | .ox, .derived => [ox, en]
  | .go, .plain => [go]
  | .go, .derived => [went]

/-- The realization of the four words in their two cells. -/
def english : Realization Lexeme Cell (List Morph) where
  realize l c := {word l c}

/-- The underlying form of a word is its morphs other than the bound forms. -/
def underlying (w : List Morph) : Finset Morph :=
  (w.filter fun m ↦ m.kind.attachment? = none).toFinset

/-- In *ox : ox-en* the plural suffix is suppletive, and in *good : bet-ter* and *go : went* the
underlying form is (§13.7): *ox*, like *kind* in *kind : kind-er*, keeps its underlying form,
while *good* and *go* change theirs. -/
theorem suppletion :
    IsAffixallyInflected english underlying .kind ∧ IsAffixallyInflected english underlying .ox ∧
      HasSuppletiveCore english underlying .good ∧ HasSuppletiveCore english underlying .go := by
  decide

end Bloomfield1933
