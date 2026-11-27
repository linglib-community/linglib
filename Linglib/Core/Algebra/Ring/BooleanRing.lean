module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# The action of a Boolean ring on its Boolean algebra

A Boolean algebra `β` is a ring, `AsBoolRing β`, whose addition is symmetric difference. This file
makes that ring act on `β` by `a +ᵥ b = a ∆ b`. For `β = Set α` the action of a set `N` flips
membership in `N`: it takes `B` to the set that agrees with `B` outside `N` and with `Bᶜ` inside,
and the whole universe acts as the complement.

## Main results

* `AsBoolRing.vadd_def`: `a +ᵥ b = ofBoolRing a ∆ b`.
* `AsBoolRing.toBoolRing_top_vadd`: the top element acts as the complement.
-/

@[expose] public section

open symmDiff

namespace AsBoolRing

variable {β : Type*}

/-- A generalized Boolean algebra is acted on by its ring, by symmetric difference. -/
instance [GeneralizedBooleanAlgebra β] : AddAction (AsBoolRing β) β where
  vadd a b := ofBoolRing a ∆ b
  zero_vadd b := bot_symmDiff b
  add_vadd a b c := symmDiff_assoc (ofBoolRing a) (ofBoolRing b) c

theorem vadd_def [GeneralizedBooleanAlgebra β] (a : AsBoolRing β) (b : β) :
    a +ᵥ b = ofBoolRing a ∆ b := rfl

@[simp] theorem toBoolRing_vadd [GeneralizedBooleanAlgebra β] (a b : β) :
    toBoolRing a +ᵥ b = a ∆ b := rfl

@[simp] theorem toBoolRing_top_vadd [BooleanAlgebra β] (b : β) :
    toBoolRing (⊤ : β) +ᵥ b = bᶜ := (top_symmDiff b).trans hnot_eq_compl

end AsBoolRing
