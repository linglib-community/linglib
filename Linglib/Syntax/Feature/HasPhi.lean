/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Bundle

/-!
# Agreement in φ-features

An expression bears φ-features when it carries an agreement bundle, `HasPhi.phi a`; token
features bear the bundle of their agreement dimensions. Two such
expressions agree, `HasPhi.Agree a b`, when their bundles are compatible at each φ-feature
(`Agreement.Dimension.phi`), the two slots there having a common extension, so that a slot left
unspecified agrees with every value. Agreement is reflexive and symmetric, and it is not
transitive (`Morphology.Word.not_isTrans_agree`).

## Implementation notes

Agreement is compatibility, not identity of values: the controller and the target each
contribute partial information, and they agree when the two unify, a clash of values being a
failure of unification [shieber-1986] [corbett-2006]. The relation is therefore symmetric and does
not represent the asymmetry of controller and target. Case and definiteness are slots of the
bundle but not φ-features, so they do not enter agreement: a pronoun agrees with an antecedent of
another case.

## References

* [corbett-2006]
* [shieber-1986]
-/

@[expose] public section

/-- A φ-bearer is an expression that exposes its agreement features as a bundle. -/
class HasPhi (α : Type*) where
  /-- The agreement features. -/
  phi : α → Agreement.Bundle

export HasPhi (phi)

/-- A token's features bear their agreement dimensions. -/
instance : HasPhi Morphology.Features := ⟨Agreement.Bundle.ofFeatures⟩

namespace HasPhi

variable {α β : Type*} [HasPhi α] [HasPhi β]

/-- Two φ-bearers agree when their bundles are compatible at each φ-feature. -/
def Agree (a : α) (b : β) : Prop :=
  ∀ d ∈ Agreement.Dimension.phi, Compat (phi a d) (phi b d)

instance (a : α) (b : β) : Decidable (Agree a b) := inferInstanceAs (Decidable (∀ d ∈ _, _))

@[refl] theorem Agree.refl (a : α) : Agree a a := fun _ _ ↦ compat_self _

@[symm] theorem Agree.symm {a : α} {b : β} (h : Agree a b) : Agree b a := fun d hd ↦ (h d hd).symm

/-- Agreement compares the φ-features alone: token features that differ only in case agree. -/
example (f : Morphology.Features) (c c' : Flat Case) :
    Agree (Function.update f .case c) (Function.update f .case c') := by
  rintro d hd
  simp only [Agreement.Dimension.phi, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl <;> exact compat_self _

end HasPhi
