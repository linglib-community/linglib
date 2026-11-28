/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Negation.Strength
public import Mathlib.Order.WithBot
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.Tactic.DeriveFintype

/-!
# Classes of polarity items

A *class* of polarity items is what Zwarts's strengths of negation say of an item: the strength
that the item requires and the strength that blocks it. Both are thresholds in the chain of
strengths extended by a least element, for no strength, and by a greatest element above every
strength. A *negative polarity* class requires some strength, a *positive polarity* class is
blocked by some strength, and a class may be both, as the class of Dutch *ooit* 'ever' is. A
*free choice* class is one that the generic contexts license.

A *profile* is what the same strengths say of a context: the greatest strength that the context
carries, the greatest strength that it holds outright, and whether it licenses free choice. A
profile [admits](##PolarityItem.Profile.Admits) a class when it meets the requirement of the class,
by strength or by free choice, and stays below its blocker.

## Main definitions

* `PolarityItem.Class`, with `PolarityItem.Class.npi`, `PolarityItem.Class.ppi` and
  `PolarityItem.Class.fci`.
* `PolarityItem.Profile`, with `PolarityItem.Profile.Licenses`,
  `PolarityItem.Profile.AntiLicenses` and `PolarityItem.Profile.Admits`.

## Implementation notes

A class that requires the greatest element is licensed by no strength of negation, so a free
choice class that is not a negative polarity class requires it.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [szabolcsi-2004]
* [chierchia-2006]
-/

@[expose] public section

namespace PolarityItem

open Negation

/-- A strength of negation in the chain extended by a least and a greatest element. -/
abbrev ofStrength (s : Strength) : WithBot (WithTop Strength) :=
  ((s : WithTop Strength) : WithBot (WithTop Strength))

theorem eq_bot_or_eq_ofStrength_of_lt_top {x : WithBot (WithTop Strength)} (h : x < ⊤) :
    x = ⊥ ∨ ∃ s : Strength, x = ofStrength s := by
  induction x using WithBot.recBotCoe with
  | bot => exact .inl rfl
  | coe a =>
    induction a using WithTop.recTopCoe with
    | top => exact absurd h (lt_irrefl _)
    | coe s => exact .inr ⟨s, rfl⟩

/-- Anti-morphic strength is the greatest element below the top of the extended chain. -/
theorem le_ofStrength_antimorphic {x : WithBot (WithTop Strength)} (h : x < ⊤) :
    x ≤ ofStrength .antimorphic := by
  obtain rfl | ⟨s, rfl⟩ := eq_bot_or_eq_ofStrength_of_lt_top h
  · exact bot_le
  · exact WithBot.coe_le_coe.2 (WithTop.coe_le_coe.2 s.le_antimorphic)

/-- A class of polarity items: the strength of negation that its members require, the strength
that blocks them, and whether the generic contexts license them. -/
structure Class where
  /-- The strength of negation that the class requires: `⊥` when it requires none, and `⊤` when no
  strength of negation licenses it. -/
  requirement : WithBot (WithTop Strength) := ⊥
  /-- The strength of negation that blocks the class, or `⊤` when none does. -/
  blocker : WithBot (WithTop Strength) := ⊤
  /-- Whether the generic contexts license the class. -/
  freeChoice : Bool := false
  deriving DecidableEq, Fintype

namespace Class

/-- The class of the negative polarity items that require the strength `s`, which are free choice
items as well when `fc` holds. -/
def npi (s : Strength) (fc : Bool := false) : Class :=
  { requirement := ((s : WithTop Strength) : WithBot (WithTop Strength)), freeChoice := fc }

/-- The class of the positive polarity items that the strength `s` blocks. -/
def ppi (s : Strength) : Class :=
  { blocker := ((s : WithTop Strength) : WithBot (WithTop Strength)) }

/-- The class of the free choice items that no strength of negation licenses. -/
def fci : Class := { requirement := ⊤, freeChoice := true }

/-- A class is a **negative polarity** class when it requires something. -/
abbrev IsNPI (k : Class) : Prop := ⊥ < k.requirement

/-- A class is a **positive polarity** class when some strength of negation blocks it. -/
abbrev IsPPI (k : Class) : Prop := k.blocker < ⊤

/-- A class is a **free choice** class when the generic contexts license it. -/
abbrev IsFCI (k : Class) : Prop := k.freeChoice = true

end Class

/-- What the strengths of negation say of a context: the greatest strength that it carries, the
greatest strength that it holds outright, each `⊥` when there is none, and whether it licenses
free choice. -/
structure Profile where
  /-- The greatest strength of negation that the context carries. -/
  carried : WithBot (WithTop Strength)
  /-- The greatest strength of negation that the context holds outright. -/
  held : WithBot (WithTop Strength)
  /-- Whether the context licenses free choice. -/
  freeChoice : Bool
  deriving DecidableEq, Fintype

namespace Profile

variable (p : Profile) (k : Class)

/-- A profile **licenses** a class when it carries the strength that the class requires, or it
licenses free choice and the class is a free choice class. -/
def Licenses : Prop := k.requirement ≤ p.carried ∨ p.freeChoice = true ∧ k.IsFCI

/-- A profile **anti-licenses** a class when it holds the strength that blocks the class. -/
def AntiLicenses : Prop := k.blocker ≤ p.held

/-- A profile **admits** a class when it licenses the class and does not anti-license it. -/
def Admits : Prop := p.Licenses k ∧ ¬ p.AntiLicenses k

instance : Decidable (p.Licenses k) := inferInstanceAs (Decidable (_ ∨ _))

instance : Decidable (p.AntiLicenses k) := inferInstanceAs (Decidable (_ ≤ _))

instance : Decidable (p.Admits k) := inferInstanceAs (Decidable (_ ∧ _))

end Profile

end PolarityItem
