/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Number.Basic
public import Linglib.Semantics.Plurality.Number

/-!
# Signed number bundles

Harbour's number features are bivalent, and a bundle is the set of its signed values, so the empty
bundle, which carries no number, differs from `[−atomic, −minimal]`. Which values a bundle carries
depends on the number system: the plural of English is `[−atomic]`, that of a language with a dual
`[−atomic, −minimal]`. A bundle [denotes a region](##Number.Bundle.exact) by applying the region
operators of its features in a fixed order. The containment of `[+atomic]` in `[+minimal]` then
follows from the semantics: [`[+atomic, −minimal]` denotes
nothing](##Number.Bundle.not_exact_atomic_nonMinimal), as Harbour observes.

## Implementation notes

`Bundle.ofNumber` gives the bundles of the singular, the dual and the plural in a system with both
`[±atomic]` and `[±minimal]`. `Number.dom` reads their positive values alone. The features of person
and gender are still the privative chains of `Person.Features` and `Gender.Features`.

## References

* [harbour-2014], §5.1, p. 213
* [harbour-2016], §9.5, pp. 222–223
-/

@[expose] public section

namespace Number

open Mereology (Atom atomize)

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

/-- The singular of a system with a dual, `[+atomic, +minimal]`. -/
def singular : Bundle := {(.atomic, true), (.minimal, true)}

/-- The dual, `[−atomic, +minimal]`. -/
def dual : Bundle := {(.atomic, false), (.minimal, true)}

/-- The plural of a system with a dual, `[−atomic, −minimal]`. -/
def plural : Bundle := {(.atomic, false), (.minimal, false)}

/-- The bundle of a basic number value; the values that need feature recursion or additivity have
none. -/
def ofNumber : Number → Option Bundle
  | .singular => some singular
  | .dual => some dual
  | .plural => some plural
  | _ => none

/-- `b.step v f` applies `f` when the bundle `b` carries the signed feature `v`. -/
def step {X : Type*} (b : Bundle) (v : Feature × Bool) (f : X → X) (x : X) : X :=
  if v ∈ b then f x else x

variable {D : Type*} [PartialOrder D]

/-- The region a bundle's `[±atomic]` and `[±minimal]` values select from `P`, the former first. -/
def exact (b : Bundle) (P : D → Prop) : D → Prop :=
  b.step (.minimal, true) atomize <| b.step (.minimal, false) nonMinimalOf <|
    b.step (.atomic, true) atomsOf <| b.step (.atomic, false) nonAtomsOf P

theorem exact_le (b : Bundle) (P : D → Prop) {x : D} (h : b.exact P x) : P x := by
  have step_le : ∀ v (f : (D → Prop) → D → Prop), (∀ P x, f P x → P x) →
      ∀ P x, b.step v f P x → P x := by
    intro v f hf P x h; unfold step at h; split_ifs at h; exacts [hf _ _ h, h]
  exact step_le _ _ (fun _ _ h ↦ h.1) _ _ <| step_le _ _ (fun _ _ h ↦ h.1) _ _ <|
    step_le _ _ (fun _ _ h ↦ h.1) _ _ <| step_le _ _ (fun _ _ h ↦ h.1) _ _ h

/-- The `[+atomic]` region of a bundle carrying that value holds only atoms. -/
theorem atom_of_exact {b : Bundle} (hb : (.atomic, true) ∈ b) {P : D → Prop} {x : D}
    (h : b.exact P x) : Atom x := by
  have step_le : ∀ v (f : (D → Prop) → D → Prop), (∀ P x, f P x → P x) →
      ∀ P x, b.step v f P x → P x := by
    intro v f hf P x h; unfold step at h; split_ifs at h; exacts [hf _ _ h, h]
  have h₁ := step_le _ _ (fun _ _ h ↦ h.1) _ _ <| step_le _ _ (fun _ _ h ↦ h.1) _ _ h
  simp only [step, hb, ↓reduceIte] at h₁
  exact h₁.2

/-- `[+atomic, −minimal]` denotes nothing: the atoms of a region are all minimal in them. -/
theorem not_exact_atomic_nonMinimal (P : D → Prop) (x : D) :
    ¬ exact {(.atomic, true), (.minimal, false)} P x := by
  simp only [exact, step, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, reduceCtorEq,
    Bool.true_eq_false, Bool.false_eq_true, and_self, and_false, or_self, or_false, or_true,
    ↓reduceIte, and_true]
  exact fun h ↦ h.2 (by rw [atomize_eq_of_atoms fun _ h ↦ h.2]; exact h.1)

end Bundle

end Number
