/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Number.Decomposition
public import Linglib.Semantics.Plurality.Number

/-!
# The region of a number bundle

A bundle of Harbour's number features denotes a region of a noun's lattice, `Number.Bundle.exact`,
by applying the region operators of its `[±atomic]` values and then those of its `[±minimal]`
values. The containment of `[+atomic]` in `[+minimal]` follows from the semantics:
`[+atomic, −minimal]` denotes nothing (`Number.Bundle.not_exact_atomic_nonMinimal`).

## References

* [harbour-2011]
* [harbour-2014]
-/

@[expose] public section

namespace Number

open Mereology (Atom atomize)

namespace Bundle

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
