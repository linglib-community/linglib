/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Interval.Basic

/-!
# Interval orders

An interval order is an irreflexive relation `r` in which `r a b` and `r c d` imply `r a d` or
`r c b`: no two `r`-related pairs are incomparable crosswise, so the order contains no copy of
`2 + 2`. Transitivity follows. Interval orders are the orders of precedence among intervals of a
linear order, and the precedence of nonempty intervals is the motivating instance.

`[UPSTREAM]` candidate for mathlib's order theory.

## Main definitions

* `IsIntervalOrder α r`: `r` is an interval order on `α`.

## Main results

* `IsIntervalOrder.toIsStrictOrder`: an interval order is a strict order.
* `IsIntervalOrder.invImage`: interval orders pull back along maps.
* `NonemptyInterval.isIntervalOrder_precedes`: precedence of intervals in a linear order.

## References

* [fishburn-1970]
-/

@[expose] public section

/-- An interval order: an irreflexive relation in which `r a b` and `r c d` imply `r a d` or
`r c b`. -/
class IsIntervalOrder (α : Sort*) (r : α → α → Prop) : Prop extends Std.Irrefl r where
  /-- Two related pairs are related crosswise in one direction. -/
  two_plus_two : ∀ ⦃a b c d⦄, r a b → r c d → r a d ∨ r c b

namespace IsIntervalOrder

variable {α β : Sort*} {r : α → α → Prop}

instance (priority := 100) toIsStrictOrder [IsIntervalOrder α r] : IsStrictOrder α r where
  irrefl := Std.Irrefl.irrefl
  trans _ b _ hab hbc := (two_plus_two hab hbc).resolve_right (Std.Irrefl.irrefl b)

/-- An interval order pulls back along any map. -/
theorem invImage (h : IsIntervalOrder α r) (f : β → α) : IsIntervalOrder β (InvImage r f) where
  irrefl a := h.irrefl (f a)
  two_plus_two _ _ _ _ hab hcd := h.two_plus_two hab hcd

end IsIntervalOrder

namespace NonemptyInterval

variable {α : Type*} [LinearOrder α]

/-- Precedence of intervals in a linear order is an interval order. -/
instance isIntervalOrder_precedes : IsIntervalOrder (NonemptyInterval α) Precedes where
  irrefl := precedes_irrefl
  two_plus_two a b c d hab hcd := by
    rcases lt_or_ge a.snd d.fst with h | h
    exacts [.inl h, .inr ((hcd.trans_le h).trans hab)]

end NonemptyInterval
