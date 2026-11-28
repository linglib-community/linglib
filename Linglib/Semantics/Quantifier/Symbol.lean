/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype

/-!
# Determiner symbols

A determiner symbol names a determiner denotation, as the basic determiner symbols of the logic
L(GQ) of Barwise and Cooper do. This file defines the symbols alone, so that a lexical record can
list the readings of a word without the theory of generalized quantifiers; what a symbol denotes
is defined with the global determiner denotations.

## Main definitions

* `Quantifier.Det.Symbol`: the eight determiner symbols.

## Implementation notes

The eight symbols are a choice made here. The logical determiner symbols of Barwise and Cooper
are *some*, *every*, *no*, *both*, *neither*, the numerals and *the n*, their non-logical ones
include *most* and *few*, and they have no *half*.

## References

* [barwise-cooper-1981]
-/

@[expose] public section

namespace Quantifier.Det

/-- A determiner symbol names one of the canonical global determiner denotations, after the basic
determiner symbols of the logic L(GQ) of [barwise-cooper-1981]. -/
inductive Symbol where
  | every | some | no | most | few | half | both | neither
  deriving DecidableEq, Repr, Fintype

end Quantifier.Det
