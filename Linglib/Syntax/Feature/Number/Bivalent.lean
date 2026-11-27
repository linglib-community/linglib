/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Feature.Number.Basic

/-!
# The features of number

Harbour decomposes grammatical number into three bivalent features, `[±atomic]`, `[±minimal]` and
`[±additive]`, and a number head carries a bundle of their values. A bundle is the set of its
signed features, so the empty bundle, which carries no number, differs from
`[−atomic, −minimal]`. A bundle may carry both values of a feature, `Number.Bundle.CarriesBoth`:
on a number head under feature recursion, as the trial carries `[+minimal −minimal]`, and on a D
head whose values come from a noun's class and its natural number, where Kiowa-Tanoan spells the
conflict out as inverse.

## Implementation notes

Which bundle a number value names is a claim about a system, not about the value: the plural of
English is `[−atomic]`, that of a language with a dual `[−atomic, −minimal]`. So there is no map
from `Number` to bundles here. The features of person and gender are the privative chains of
`Person.Features` and `Gender.Features`.

## References

* [harbour-2011]
* [harbour-2014]
* [harbour-2016]
-/

@[expose] public section

namespace Number

/-- Harbour's number features are `[±atomic]`, `[±minimal]` and `[±additive]`. -/
inductive Feature where
  | atomic
  | minimal
  | additive
  deriving DecidableEq, Fintype, Repr

/-- A feature bundle is the set of its signed features, `(F, true)` standing for `+F`. The empty
bundle carries no number. -/
abbrev Bundle := Finset (Feature × Bool)

namespace Bundle

/-- `b.CarriesBoth f` holds when `b` carries both values of `f`. -/
def CarriesBoth (b : Bundle) (f : Feature) : Prop := (f, true) ∈ b ∧ (f, false) ∈ b

instance (b : Bundle) : DecidablePred b.CarriesBoth := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

end Bundle

end Number
