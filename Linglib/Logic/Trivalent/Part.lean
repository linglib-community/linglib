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
Kratzer's composition engine, or by a three-valued one, `Trivalent`. The two carriers are
equivalent: `Trivalent.toPart` sends `undefined` to `Part.none` and a defined value to its
classical proposition, `Trivalent.ofPart` inverts it, and the knowledge order is `Part`'s order,
so theorems proved over either carrier transfer to the other.

Read in `Part`, transplication is the partiality monad's assertion, the Middle Kleene connectives
evaluate left to right by `bind`, and the Weak Kleene ones evaluate both operands by the
applicative lift. The Strong Kleene connectives are no such evaluation, since an undefined first
operand need not absorb.

## Main definitions

* `Trivalent.toPart`: a value as a partial proposition.
* `Trivalent.ofPart`: the three-valued value of a partial proposition.
* `Trivalent.equivPart`, `Trivalent.orderIsoPart`: the two carriers are equivalent, and the
  knowledge order is `Part`'s.

## Main results

* `Trivalent.ofPart_eq_undefined_iff`, `Trivalent.ofPart_eq_true_iff`,
  `Trivalent.ofPart_eq_false_iff`:
  the three values of `ofPart`.
* `Trivalent.ofPart_map_not`, `Trivalent.ofPart_ite_some_false`: negation and enrichment by a
  two-valued condition transport along `ofPart`.
* `Trivalent.toPart_transplication`, `Trivalent.toPart_meetMiddle`, `Trivalent.toPart_meetWeak`:
  transplication, Middle Kleene and Weak Kleene as evaluation in the partiality monad.
* `Trivalent.gapExt_ofPart`: pointwise, the gap is the set of undefined points.

## References

* [heim-kratzer-1998]
* [beaver-krahmer-2001]
* [blamey-1986]
* [peters-1979]
-/

@[expose] public section

namespace Trivalent

open Bilattice

/-- A value as a partial proposition: `undefined` is `Part.none`. -/
def toPart : Trivalent → Part Prop
  | .false => Part.some False
  | .undefined => Part.none
  | .true => Part.some True

open Classical in
/-- The three-valued value of a partial proposition is `undefined` where it is undefined and
its classical value elsewhere. -/
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

@[simp] theorem ofPart_toPart (a : Trivalent) : ofPart (toPart a) = a := by
  cases a <;> simp [toPart]

@[simp] theorem toPart_ofPart (p : Part Prop) : toPart (ofPart p) = p := by
  cases h : ofPart p
  · obtain ⟨a, ha, hna⟩ := ofPart_eq_false_iff.1 h
    exact (Part.eq_some_iff.2 (eq_false hna ▸ ha)).symm
  · exact (Part.eq_none_iff'.2 (ofPart_eq_undefined_iff.1 h)).symm
  · obtain ⟨a, ha, hya⟩ := ofPart_eq_true_iff.1 h
    exact (Part.eq_some_iff.2 (eq_true hya ▸ ha)).symm

/-- A trivalent value that depends on a partial one is undefined where that one is: the bind of
partial values, read back as a truth value. -/
noncomputable def bindPart {α : Type*} (o : Part α) (f : α → Trivalent) : Trivalent :=
  ofPart (o.bind fun a ↦ toPart (f a))

theorem bindPart_of_mem {α : Type*} {o : Part α} {a : α} (h : a ∈ o) (f : α → Trivalent) :
    bindPart o f = f a := by
  rw [bindPart, Part.eq_some_iff.2 h, Part.bind_some, ofPart_toPart]

theorem bindPart_of_not_dom {α : Type*} {o : Part α} (h : ¬ o.Dom) (f : α → Trivalent) :
    bindPart o f = .undefined := by
  rw [bindPart, Part.eq_none_iff'.2 h, Part.bind_none, ofPart_none]

/-- With a function that is defined everywhere, the bind is defined exactly where the partial
value is. -/
theorem bindPart_ne_undefined_iff {α : Type*} {o : Part α} {f : α → Trivalent}
    (hf : ∀ a, f a ≠ .undefined) : bindPart o f ≠ .undefined ↔ o.Dom := by
  by_cases h : o.Dom
  · obtain ⟨a, ha⟩ := Part.dom_iff_mem.1 h
    rw [bindPart_of_mem ha]
    exact iff_of_true (hf a) h
  · rw [bindPart_of_not_dom h]
    exact iff_of_false (fun h' ↦ h' rfl) h

/-- Three-valued truth and partial propositions are equivalent carriers. -/
noncomputable def equivPart : Trivalent ≃ Part Prop where
  toFun := toPart
  invFun := ofPart
  left_inv := ofPart_toPart
  right_inv := toPart_ofPart

/-- The knowledge order is `Part`'s order on partial propositions. -/
theorem toPart_le_toPart {a b : Trivalent} : toPart a ≤ toPart b ↔ a ≤ₖ b := by
  show (∀ i, i ∈ toPart a → i ∈ toPart b) ↔ _
  cases a <;> cases b <;> simp [toPart, kLE_iff] <;>
    first | exact ⟨False, id⟩ | exact ⟨True, trivial⟩

/-- The knowledge order on three-valued truth is `Part`'s order on partial propositions. -/
noncomputable def orderIsoPart : Know Trivalent ≃o Part Prop where
  toEquiv := ofKnow.trans equivPart
  map_rel_iff' := toPart_le_toPart

/-- Transplication is the partiality monad's assertion: require the presupposition, then return
the value. -/
theorem toPart_transplication (a b : Trivalent) :
    toPart (transplication a b) = Part.assert (a = .true) fun _ ↦ toPart b := by
  cases a
  · rw [Part.assert_neg (by decide)]; rfl
  · rw [Part.assert_neg (by decide)]; rfl
  · rw [Part.assert_pos rfl]; rfl

open Classical in
/-- Middle Kleene conjunction evaluates left to right, consulting the second operand only once
the first is true. -/
theorem toPart_meetMiddle (a b : Trivalent) :
    toPart (meetMiddle a b) = toPart a >>= fun p ↦ if p then toPart b else pure False := by
  cases a <;> cases b <;> simp [toPart, meetMiddle, Part.bind_some, Part.bind_none]

/-- Weak Kleene conjunction evaluates both operands. -/
theorem toPart_meetWeak (a b : Trivalent) :
    toPart (meetWeak a b) = (· ∧ ·) <$> toPart a <*> toPart b := by
  cases a <;> cases b <;> simp [toPart, meetWeak, Seq.seq]

/-- Pointwise, the gap of a partial proposition's three-valued value is where it is undefined. -/
theorem gapExt_ofPart {W : Type*} (p : W → Part Prop) :
    gapExt (fun w ↦ ofPart (p w)) = {w | ¬ (p w).Dom} := by
  ext w; simp

end Trivalent
