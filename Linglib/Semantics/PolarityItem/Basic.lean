/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Negation.Strength

/-!
# Polarity items

A *polarity item* is a lexical item whose distribution is restricted to certain contexts. The
restriction is graded by Zwarts's strengths of negation. A *negative polarity item* requires at
least some strength of negation, and a *positive polarity item* is blocked by at least some
strength. An item may be both, as Dutch *ooit* 'ever' is, in which case it is *bipolar*. A *free
choice item* is licensed by the generic contexts. Each item therefore spans an interval of
strengths, from [the strength it requires](##PolarityItem.requirement) to [the strength that
blocks it](##PolarityItem.blocker). The licensers that admit an item are the subject of
`Semantics/PolarityItem/Licenser.lean`.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [dayal-1996]
* [chierchia-2006]
-/

@[expose] public section

/-- A polarity-sensitive lexical item. The record holds the form of the item, the weakest
strength of negation that licenses it, the weakest strength that blocks it, and whether the
generic contexts license it. -/
structure PolarityItem where
  /-- The surface form. -/
  form : String
  /-- The weakest strength of negation that licenses the item, when the item is a negative
  polarity item. A negative concord item that requires clausemate negation carries
  `antiMorphic`, which is the strength of clausal negation alone. -/
  licensor : Option Negation.Strength := none
  /-- The weakest strength of negation that blocks the item, when the item is a positive
  polarity item. -/
  antiLicensor : Option Negation.Strength := none
  /-- Whether the generic contexts license the item. -/
  freeChoice : Bool := false

namespace PolarityItem

/-- An item is a **negative polarity item** when some strength of negation licenses it. -/
abbrev IsNPI (e : PolarityItem) : Prop := e.licensor.isSome

/-- An item is a **positive polarity item** when some strength of negation blocks it. -/
abbrev IsPPI (e : PolarityItem) : Prop := e.antiLicensor.isSome

/-- An item is a **free choice item** when the generic contexts license it. -/
abbrev IsFCI (e : PolarityItem) : Prop := e.freeChoice = true

/-- The strength of negation that an item requires, or `⊥` if it requires none. -/
def requirement (e : PolarityItem) : WithBot (WithTop Negation.Strength) :=
  e.licensor.elim ⊥ fun s ↦
    ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))

/-- The strength of negation that blocks an item, or `⊤` if none does. -/
def blocker (e : PolarityItem) : WithBot (WithTop Negation.Strength) :=
  e.antiLicensor.elim ⊤ fun s ↦
    ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))

end PolarityItem
