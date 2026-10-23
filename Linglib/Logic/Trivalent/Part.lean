/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Pointwise
public import Mathlib.Data.Part

/-!
# Partial propositions and three-valued truth

A presuppositional meaning is carried either by a partial proposition `Part Prop`, as in Heim and
Kratzer's composition engine, or by a three-valued one, `SignType`. `SignType.ofPart` maps the
first carrier onto the second, sending an undefined value to `0` and a defined one to its
classical value, so theorems proved over either carrier transfer to the other.

## Main definitions

* `SignType.ofPart`: the three-valued value of a partial proposition.

## Main results

* `SignType.ofPart_eq_zero_iff`, `SignType.ofPart_eq_one_iff`, `SignType.ofPart_eq_neg_one_iff`:
  the three values of `ofPart`.
* `Trivalent.gapExt_ofPart`: pointwise, the gap is the set of undefined points.

## References

* [heim-kratzer-1998]
* [beaver-krahmer-2001]
-/

@[expose] public section

namespace SignType

open Classical in
/-- The three-valued value of a partial proposition is `0` where it is undefined and its
classical value elsewhere. -/
noncomputable def ofPart (p : Part Prop) : SignType :=
  if h : p.Dom then ofProp (p.get h) else 0

variable {p : Part Prop}

@[simp] theorem ofPart_eq_zero_iff : ofPart p = 0 ↔ ¬ p.Dom := by
  unfold ofPart; split_ifs <;> simp_all

@[simp] theorem ofPart_eq_one_iff : ofPart p = 1 ↔ ∃ a ∈ p, a := by
  unfold ofPart
  split_ifs with h
  · simp only [ofProp_eq_one_iff]
    exact ⟨fun ha ↦ ⟨_, Part.get_mem h, ha⟩, fun ⟨a, hm, ha⟩ ↦ Part.get_eq_of_mem hm h ▸ ha⟩
  · exact iff_of_false (by decide) fun ⟨a, hm, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨a, hm⟩)

@[simp] theorem ofPart_eq_neg_one_iff : ofPart p = -1 ↔ ∃ a ∈ p, ¬ a := by
  unfold ofPart
  split_ifs with h
  · simp only [ofProp_eq_neg_one_iff]
    exact ⟨fun ha ↦ ⟨_, Part.get_mem h, ha⟩, fun ⟨a, hm, ha⟩ ↦ Part.get_eq_of_mem hm h ▸ ha⟩
  · exact iff_of_false (by decide) fun ⟨a, hm, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨a, hm⟩)

@[simp] theorem ofPart_some (P : Prop) [Decidable P] : ofPart (Part.some P) = ofProp P :=
  eq_of_eq_zero_iff_of_eq_one_iff (by simp) <| by
    simp only [ofPart_eq_one_iff, Part.mem_some_iff, ofProp_eq_one_iff]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ha ▸ h, fun h ↦ ⟨P, rfl, h⟩⟩

@[simp] theorem ofPart_none : ofPart Part.none = 0 :=
  ofPart_eq_zero_iff.2 Part.not_none_dom

end SignType

namespace Trivalent

open SignType

/-- Pointwise, the gap of a partial proposition's three-valued value is where it is undefined. -/
theorem gapExt_ofPart {W : Type*} (p : W → Part Prop) :
    gapExt (fun w ↦ ofPart (p w)) = {w | ¬ (p w).Dom} := by
  ext w; simp

end Trivalent
