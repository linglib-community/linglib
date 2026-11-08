/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Semiring

/-!
# Taking images is functorial

Mirror of `Mathlib/Data/Set/Semiring.lean`: `SetSemiring.imageHom` sends the identity
homomorphism to the identity and a composite to the composite, so taking images is a functor from
monoids to semirings. [UPSTREAM]
-/

public section

namespace SetSemiring

variable {α β γ : Type*} [MulOneClass α] [MulOneClass β] [MulOneClass γ]

@[simp] theorem imageHom_id : imageHom (MonoidHom.id α) = RingHom.id (SetSemiring α) :=
  RingHom.ext fun s ↦ congrArg Set.up (Set.image_id s.down)

theorem imageHom_comp (g : β →* γ) (f : α →* β) :
    imageHom (g.comp f) = (imageHom g).comp (imageHom f) :=
  RingHom.ext fun s ↦ congrArg Set.up (Set.image_comp g f s.down)

end SetSemiring
