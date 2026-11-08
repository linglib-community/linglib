/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Set.Semiring
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Computability.Language

/-!
# Languages as sets of words, and string homomorphisms

Mirror of `Mathlib/Computability/Language.lean`. A language over `α` is a subset of the free
monoid on `α`, added by union and multiplied by concatenation, so [`Language α` is
`SetSemiring (FreeMonoid α)`](##Language.equivSetSemiring). A string homomorphism
`φ : FreeMonoid α →* FreeMonoid β` then [acts on languages](##Language.stringMap) by
`SetSemiring.imageHom φ` read through that identification. It inherits the functor laws of
`imageHom`, and on a map of letters it is `Language.map`. [UPSTREAM]

## References

* [hopcroft-motwani-ullman-2000]
-/

@[expose] public section

variable {α β γ : Type*}

namespace Language

/-- A language over `α` is a subset of the free monoid on `α`, with union as addition and
concatenation as multiplication. -/
def equivSetSemiring : Language α ≃+* SetSemiring (FreeMonoid α) where
  toFun L := (FreeMonoid.toList ⁻¹' L).up
  invFun s := FreeMonoid.ofList ⁻¹' s.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The image of a language under a string homomorphism `φ`: `SetSemiring.imageHom φ` read through
`Language.equivSetSemiring`. -/
noncomputable def stringMap (φ : FreeMonoid α →* FreeMonoid β) : Language α →+* Language β :=
  equivSetSemiring.symm.toRingHom.comp ((SetSemiring.imageHom φ).comp equivSetSemiring.toRingHom)

@[simp] theorem mem_stringMap {φ : FreeMonoid α →* FreeMonoid β} {L : Language α}
    {w : List β} : w ∈ stringMap φ L ↔ ∃ v ∈ L, (φ (.ofList v)).toList = w :=
  Iff.rfl

@[simp] theorem stringMap_id : stringMap (MonoidHom.id (FreeMonoid α)) = RingHom.id _ := by
  simp [stringMap]

theorem stringMap_comp (ψ : FreeMonoid β →* FreeMonoid γ) (φ : FreeMonoid α →* FreeMonoid β) :
    stringMap (ψ.comp φ) = (stringMap ψ).comp (stringMap φ) :=
  RingHom.ext fun _ ↦ by simp [stringMap, SetSemiring.imageHom_comp]

/-- On a map of letters, `stringMap` is `Language.map`. -/
@[simp] theorem stringMap_map (f : α → β) : stringMap (FreeMonoid.map f) = map f :=
  RingHom.ext fun _ ↦ rfl

end Language
