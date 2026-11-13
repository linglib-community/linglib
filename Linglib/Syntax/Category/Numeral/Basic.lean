/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Numerals

The numeral as a lexical entry: a word and the number it names. The entries of a language are
its simple numerals, the words its complex numerals are built from, together with the fused
words that name a number of their own, as English *eleven* and Welsh *pymtheg* 'fifteen' do. A
fragment lists a language's numerals in two stocks, the digits in counting order and the
multipliers, the lexicon of a recursive numeral system; whether a fused word is a digit or
spells out a complex numeral is a question for an analysis.

## References

* [hurford-1975]
* [denic-szymanik-2024]
-/

@[expose] public section

/-- A numeral entry records a word and the number it names. -/
structure Numeral where
  /-- The citation form. -/
  form : String
  /-- The number the word names. -/
  value : ℕ
  deriving DecidableEq, Repr, Inhabited
