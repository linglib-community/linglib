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
Kratzer's composition engine, or by a three-valued one, `Trivalent`. `Trivalent.ofPart` maps the
first carrier onto the second, sending an undefined value to `0` and a defined one to its
classical value, so theorems proved over either carrier transfer to the other.

## Main definitions

* `Trivalent.ofPart`: the three-valued value of a partial proposition.

## Main results

* `Trivalent.ofPart_eq_undefined_iff`, `Trivalent.ofPart_eq_true_iff`,
  `Trivalent.ofPart_eq_false_iff`:
  the three values of `ofPart`.
* `Trivalent.ofPart_map_not`, `Trivalent.ofPart_ite_some_false`: negation and enrichment by a
  two-valued condition transport along `ofPart`.
* `Trivalent.ofPart_map_toPart`: the partial-Boolean reading `toPart` is a section of `ofPart`.
* `Trivalent.gapExt_ofPart`: pointwise, the gap is the set of undefined points.

## References

* [heim-kratzer-1998]
* [beaver-krahmer-2001]
-/

@[expose] public section

namespace Trivalent

open Classical in
/-- The three-valued value of a partial proposition is `0` where it is undefined and its
classical value elsewhere. -/
noncomputable def ofPart (p : Part Prop) : Trivalent :=
  if h : p.Dom then ofProp (p.get h) else .undefined

variable {p : Part Prop}

@[simp] theorem ofPart_eq_undefined_iff : ofPart p = .undefined ↔ ¬ p.Dom := by
  unfold ofPart; split_ifs <;> simp_all

@[simp] theorem ofPart_eq_true_iff : ofPart p = .true ↔ ∃ a ∈ p, a := by
  unfold ofPart
  split_ifs with h
  · simp only [ofProp_eq_true_iff]
    exact ⟨fun ha ↦ ⟨_, Part.get_mem h, ha⟩, fun ⟨a, hm, ha⟩ ↦ Part.get_eq_of_mem hm h ▸ ha⟩
  · exact iff_of_false (by decide) fun ⟨a, hm, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨a, hm⟩)

@[simp] theorem ofPart_eq_false_iff : ofPart p = .false ↔ ∃ a ∈ p, ¬ a := by
  unfold ofPart
  split_ifs with h
  · simp only [ofProp_eq_false_iff]
    exact ⟨fun ha ↦ ⟨_, Part.get_mem h, ha⟩, fun ⟨a, hm, ha⟩ ↦ Part.get_eq_of_mem hm h ▸ ha⟩
  · exact iff_of_false (by decide) fun ⟨a, hm, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨a, hm⟩)

@[simp] theorem ofPart_some (P : Prop) [Decidable P] : ofPart (Part.some P) = ofProp P :=
  eq_of_eq_undefined_iff_of_eq_true_iff (by simp) <| by
    simp only [ofPart_eq_true_iff, Part.mem_some_iff, ofProp_eq_true_iff]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ha ▸ h, fun h ↦ ⟨P, rfl, h⟩⟩

@[simp] theorem ofPart_none : ofPart Part.none = .undefined :=
  ofPart_eq_undefined_iff.2 Part.not_none_dom

/-- Negation transports along `ofPart`. -/
theorem ofPart_map_not : ofPart (p.map Not) = (ofPart p)ᶜ := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · simp only [ofPart_eq_undefined_iff, Trivalent.compl_eq_undefined_iff, Part.dom_iff_mem,
      Part.mem_map_iff]
    exact not_congr ⟨fun ⟨a, b, hb, _⟩ ↦ ⟨b, hb⟩, fun ⟨a, ha⟩ ↦ ⟨¬ a, a, ha, rfl⟩⟩
  · simp only [ofPart_eq_true_iff, Trivalent.compl_eq_true_iff, ofPart_eq_false_iff,
      Part.mem_map_iff]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, ha⟩
      exact ⟨b, hb, ha⟩
    · rintro ⟨a, ha, hna⟩
      exact ⟨¬ a, ⟨a, ha, rfl⟩, hna⟩

/-- Enrichment by a two-valued condition transports along `ofPart`. -/
theorem ofPart_ite_some_false (R : Prop) [Decidable R] (p : Part Prop) :
    ofPart (if R then p else Part.some False) = ofProp R ⊓ ofPart p := by
  split_ifs with h <;> simp [ofProp, h]

/-- The two partial readings agree: reading a value as a partial Boolean and then as a partial
proposition returns the value. -/
@[simp] theorem ofPart_map_toPart (a : Trivalent) :
    ofPart ((toPart a).map (· = Bool.true)) = a := by
  cases a <;> simp [toPart]

/-- Pointwise, the gap of a partial proposition's three-valued value is where it is undefined. -/
theorem gapExt_ofPart {W : Type*} (p : W → Part Prop) :
    gapExt (fun w ↦ ofPart (p w)) = {w | ¬ (p w).Dom} := by
  ext w; simp

end Trivalent
