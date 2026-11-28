/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Sigma
public import Linglib.Syntax.Feature.Person.Defs

/-!
# Valued person features

A bivalent person feature has a plus and a minus value: [+speaker] holds of what includes the
speaker and [−speaker] of what does not. This file defines a person feature with its value. A
demonstrative is specified for one: English *this* is [+speaker] and *that* [−speaker], Catalan
*aquest* is [+participant] and *aquell* [−participant], and Japanese *sore* is [+addressee].

## Main definitions

* `Person.Feature.Value`: the plus and the minus value.
* `Person.ValuedFeature`: a person feature with its value.

## References

* [harbour-2016]
* [terenghi-2023]
-/

@[expose] public section

namespace Person

/-- The value of a bivalent feature. -/
inductive Feature.Value where
  | plus
  | minus
  deriving DecidableEq, Repr, Fintype

/-- A person feature with its value, as [+speaker] or [−participant]. -/
structure ValuedFeature where
  /-- The feature. -/
  feature : Feature
  /-- Its value. -/
  value : Feature.Value
  deriving DecidableEq, Repr, Fintype

end Person
