module

public import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# German numeral modifiers

This file records German expressions that combine with a numeral to bound or fix the amount it
names, as Claus and Walch use them in their framing experiments. *Genau* 'exactly' fixes the
amount. *Höchstens* 'at most' and *mindestens* 'at least' are superlatives, *bis zu* 'up to' is a
directional preposition and *maximal* 'maximally' an adverb, in the kinds of Nouwen's survey. Each
is a `Numerals.NumeralModifier` with the one reading of the comparison it expresses.

## TODO

Blok reports for German, as for English, that *bis zu* differs from *höchstens* in what it
asserts: its upper bound is implicated. The reading recorded here is truth-conditional content,
the upper bound it shares with *höchstens*.

## References

* [B. Claus and M. C. Walch, *Numeral Modification and Framing Effects: exactly and at most vs
  up to* (2024)][claus-walch-2024]
* [R. Nouwen, *Two kinds of modified numerals* (2010)][nouwen-2010]
* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
-/

@[expose] public section

namespace German.NumeralModifiers

open Numerals

/-- *genau* 'exactly' fixes the amount. -/
def genau : NumeralModifier := .ofComparison "genau" none .eq
/-- *bis zu* 'up to', a directional preposition, bounds the amount from above. -/
def bisZu : NumeralModifier := .ofComparison "bis zu" (some .directional) .le
/-- *höchstens* 'at most', a superlative, bounds the amount from above. -/
def hoechstens : NumeralModifier := .ofComparison "höchstens" (some .superlative) .le
/-- *mindestens* 'at least', a superlative, bounds the amount from below. -/
def mindestens : NumeralModifier := .ofComparison "mindestens" (some .superlative) .ge
/-- *maximal* 'maximally', an adverb, bounds the amount from above. -/
def maximal : NumeralModifier := .ofComparison "maximal" (some .adverbial) .le

/-- The German numeral modifiers recorded here. -/
def inventory : List NumeralModifier := [genau, bisZu, hoechstens, mindestens, maximal]

end German.NumeralModifiers
