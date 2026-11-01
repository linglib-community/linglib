module

public import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# Dutch numeral modifiers

This file records Dutch expressions that combine with a numeral to bound the amount it names, as
Blok uses them in the Dutch negative polarity data. *Tot* 'up to' is a directional preposition,
whose complement is the endpoint of a path, and *maximaal* 'maximally' an adverb, in the kinds of
Nouwen's survey. Each is a `Numerals.NumeralModifier` with the one reading of the comparison it
expresses.

## TODO

Blok argues that *tot*, like English *up to*, asserts only a lower bound and implicates its upper
bound. The reading recorded here is truth-conditional content, the upper bound it shares with
*maximaal*.

## References

* [R. Nouwen, *Two kinds of modified numerals* (2010)][nouwen-2010]
* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
-/

@[expose] public section

namespace Dutch.NumeralModifiers

open Degree Numerals

/-- *tot* 'up to', a directional preposition, bounds the amount from above. -/
def tot : NumeralModifier := .ofComparison "tot" (some .directional) .le
/-- *maximaal* 'maximally', an adverb, bounds the amount from above. -/
def maximaal : NumeralModifier := .ofComparison "maximaal" (some .adverbial) .le

/-- The Dutch numeral modifiers recorded here. -/
def inventory : List NumeralModifier := [tot, maximaal]

end Dutch.NumeralModifiers
