/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.PolarityItem.Context
public import Mathlib.Data.Finset.Insert

/-!
# Polarity items

A *polarity item* is a lexical item whose distribution is restricted to certain contexts. Its
entry holds its form and what its sources say of single contexts: the contexts in which they
attest the item, and the contexts from which they exclude it. A context that no source mentions
for the item is in neither set, so an entry says nothing of it.

An entry does not classify the item. The classes of the strengths of negation are the subject of
`Semantics/PolarityItem/Class.lean`, and an entry is [compatible](##PolarityItem.Compatible) with
a class when its contexts agree with what the class predicts.

## References

* [zwarts-1998]
* [haspelmath-1997]
-/

@[expose] public section

/-- The entry of a polarity-sensitive lexical item: its form, the contexts in which its sources
attest it, and the contexts from which they exclude it. -/
structure PolarityItem where
  /-- The surface form. -/
  form : String
  /-- The contexts in which a source attests the item. -/
  attested : Finset PolarityItem.LicensingContext := ∅
  /-- The contexts from which a source excludes the item. -/
  excluded : Finset PolarityItem.LicensingContext := ∅
