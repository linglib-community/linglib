/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Polarity.LicensingContext
public import Linglib.Semantics.Polarity.Strength

/-!
# Polarity items

A polarity item is a lexical item with a defective distribution, as van der Wouden puts it: a
negative polarity item occurs only in a negative context and a positive polarity item cannot occur
in one. Both are graded by Zwarts's strengths of negation, `Negation.Strength`: a negative polarity
item needs at least some strength, which licenses it, and a positive polarity item is blocked by at
least some strength, which anti-licenses it. The two are independent, and an item with both, like
Dutch *ooit* 'ever', is bipolar. A free choice item is licensed in the generic contexts instead,
after Kadmon and Landman and Dayal; English *any* is both a negative polarity item and a free choice
item.

The record also holds the contexts in which the item is attested and those in which it is
attested to be out, the data against which `Semantics/Polarity/Licensing.lean` checks the theory.

## Main declarations

* `PolarityItem`: the lexical record.
* `PolarityItem.IsNPI`, `PolarityItem.IsPPI`, `PolarityItem.IsFCI`: the classes.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [kadmon-landman-1993]
* [dayal-1996]
-/

@[expose] public section

/-- A polarity-sensitive lexical item: its form, the weakest strength of negation that licenses
it and the weakest that blocks it, whether the generic contexts license it, and the contexts in
which it is attested and attested to be out. -/
structure PolarityItem where
  /-- The surface form. -/
  form : String
  /-- The weakest strength of negation that licenses the item, if it is a negative polarity
  item. A negative concord item that needs clausemate negation carries `antiMorphic`, the
  strength of clausal negation alone. -/
  licensor : Option Negation.Strength := none
  /-- The weakest strength of negation that blocks the item, if it is a positive polarity
  item. -/
  antiLicensor : Option Negation.Strength := none
  /-- Whether the generic contexts license the item. -/
  freeChoice : Bool := false
  /-- The contexts in which the item is attested. -/
  licensingContexts : List PolarityItem.LicensingContext := []
  /-- The contexts in which the item is attested to be out. -/
  excludedContexts : List PolarityItem.LicensingContext := []


namespace PolarityItem

/-- An item is a **negative polarity item** when some strength of negation licenses it. -/
abbrev IsNPI (e : PolarityItem) : Prop := e.licensor.isSome

/-- An item is a **positive polarity item** when some strength of negation blocks it. -/
abbrev IsPPI (e : PolarityItem) : Prop := e.antiLicensor.isSome

/-- An item is a **free choice item** when the generic contexts license it. -/
abbrev IsFCI (e : PolarityItem) : Prop := e.freeChoice = true

end PolarityItem
