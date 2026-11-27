/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Proposition
public import Mathlib.Data.Part

/-!
# Partial propositions and three-valued truth

Semantic accounts of presupposition take two forms. In one a presupposition trigger denotes a
partial function, and a sentence whose presupposition fails has no value at all. In the other such a
sentence has a third truth value. The first uses the undefined value implicitly, as Potts observes,
and the two are the same: a partial proposition has its classical value where it is defined and the
third value where it is not, and nothing is lost either way.

Partiality also shows the Kleene connectives as ways of computing. Middle Kleene conjunction
evaluates its first operand and consults the second only once the first is true; Weak Kleene
conjunction evaluates both. Strong Kleene conjunction is neither, since an undefined first operand
need not make the whole undefined.

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

## Implementation notes

Heim and Kratzer's composition engine carries a presuppositional meaning as a `Part Prop`. The
translation is an equivalence that carries the knowledge order on truth values to the order of
`Part`, so a theorem proved over either carrier transfers to the other. Read in `Part`,
transplication is the assertion of the partiality monad, Middle Kleene conjunction its bind and Weak
Kleene conjunction its applicative lift.

## References

* [heim-kratzer-1998]
* [beaver-krahmer-2001]
* [blamey-1986]
* [peters-1979]
* [potts-2015]
-/

@[expose] public section

namespace Trivalent

open Bilattice

/-- The **partial proposition** of a truth value is the true proposition for true, the false
proposition for false, and no value at all for undefined. -/
def toPart : Trivalent → Part Prop
  | .false => Part.some False
  | .undefined => Part.none
  | .true => Part.some True

open Classical in
/-- The **truth value** of a partial proposition is undefined if the proposition has no value, and
otherwise true or false according to whether its value holds. -/
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

/-- The truth value of a negated partial proposition is the Kleene negation of its truth value. -/
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

/-- If a partial proposition is replaced by plain falsity wherever a condition fails, the truth
value of the result is the Strong Kleene conjunction of the condition's value with the
proposition's. -/
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

/-- The **value at a partial argument** of a function into the truth values is undefined when the
argument has no value, and is otherwise the function's value at the argument. -/
noncomputable def bindPart {α : Type*} (o : Part α) (f : α → Trivalent) : Trivalent :=
  ofPart (o.bind fun a ↦ toPart (f a))

theorem bindPart_of_mem {α : Type*} {o : Part α} {a : α} (h : a ∈ o) (f : α → Trivalent) :
    bindPart o f = f a := by
  rw [bindPart, Part.eq_some_iff.2 h, Part.bind_some, ofPart_toPart]

theorem bindPart_of_not_dom {α : Type*} {o : Part α} (h : ¬ o.Dom) (f : α → Trivalent) :
    bindPart o f = .undefined := by
  rw [bindPart, Part.eq_none_iff'.2 h, Part.bind_none, ofPart_none]

/-- If the function never returns undefined, its value at a partial argument is defined exactly when
the argument has a value. -/
theorem bindPart_ne_undefined_iff {α : Type*} {o : Part α} {f : α → Trivalent}
    (hf : ∀ a, f a ≠ .undefined) : bindPart o f ≠ .undefined ↔ o.Dom := by
  by_cases h : o.Dom
  · obtain ⟨a, ha⟩ := Part.dom_iff_mem.1 h
    rw [bindPart_of_mem ha]
    exact iff_of_true (hf a) h
  · rw [bindPart_of_not_dom h]
    exact iff_of_false (fun h' ↦ h' rfl) h

/-- Truth values and partial propositions correspond one to one. -/
noncomputable def equivPart : Trivalent ≃ Part Prop where
  toFun := toPart
  invFun := ofPart
  left_inv := ofPart_toPart
  right_inv := toPart_ofPart

/-- One truth value carries at most the information of another exactly when the second's partial
proposition extends the first's. -/
theorem toPart_le_toPart {a b : Trivalent} : toPart a ≤ toPart b ↔ a ≤ₖ b := by
  show (∀ i, i ∈ toPart a → i ∈ toPart b) ↔ _
  cases a <;> cases b <;> simp [toPart, kLE_iff] <;>
    first | exact ⟨False, id⟩ | exact ⟨True, trivial⟩

/-- Ordered by information, the truth values correspond exactly to the partial propositions ordered
by extension. -/
noncomputable def orderIsoPart : Know Trivalent ≃o Part Prop where
  toEquiv := ofKnow.trans equivPart
  map_rel_iff' := toPart_le_toPart

/-- The partial proposition of *φ* presupposing *π* has no value unless *π* is true, and is then the
partial proposition of *φ*. -/
theorem toPart_transplication (a b : Trivalent) :
    toPart (transplication a b) = Part.assert (a = .true) fun _ ↦ toPart b := by
  cases a
  · rw [Part.assert_neg (by decide)]; rfl
  · rw [Part.assert_neg (by decide)]; rfl
  · rw [Part.assert_pos rfl]; rfl

open Classical in
/-- Middle Kleene conjunction evaluates from left to right. If the first conjunct has no value,
neither does the conjunction; if it is false, the conjunction is false; and only if it is true is
the second conjunct consulted. -/
theorem toPart_meetMiddle (a b : Trivalent) :
    toPart (meetMiddle a b) = toPart a >>= fun p ↦ if p then toPart b else pure False := by
  cases a <;> cases b <;> simp [toPart, meetMiddle, Part.bind_some, Part.bind_none]

/-- Weak Kleene conjunction evaluates both conjuncts, and has a value only if both do. -/
theorem toPart_meetWeak (a b : Trivalent) :
    toPart (meetWeak a b) = (· ∧ ·) <$> toPart a <*> toPart b := by
  cases a <;> cases b <;> simp [toPart, meetWeak, Seq.seq]

/-- For a family of partial propositions, one at each world, the gap of the resulting trivalent
proposition is the set of worlds where the partial proposition has no value. -/
theorem gapExt_ofPart {W : Type*} (p : W → Part Prop) :
    gapExt (fun w ↦ ofPart (p w)) = {w | ¬ (p w).Dom} := by
  ext w; simp

end Trivalent
