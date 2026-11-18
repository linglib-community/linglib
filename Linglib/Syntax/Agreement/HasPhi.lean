/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Agreement.Bundle

/-!
# The φ-bundle capability

`HasPhi` equips a carrier with its agreement features as an `Agreement.Bundle`;
`HasPhi.Agree` is the induced agreement relation, compatibility of the bundles,
an unspecified dimension acting as a wildcard.
-/

@[expose] public section

/-- A φ-bearer is an expression that exposes its agreement features as a bundle. -/
class HasPhi (α : Type*) where
  /-- The agreement features. -/
  phi : α → Agreement.Bundle

export HasPhi (phi)

/-- A bundle bears itself. -/
instance : HasPhi Agreement.Bundle := ⟨id⟩

/-- A token's features bear their agreement dimensions. -/
instance : HasPhi Morphology.Features := ⟨Agreement.Bundle.ofFeatures⟩

/-- Two φ-bearers agree when their bundles are compatible, an unspecified dimension acting
as a wildcard. -/
def HasPhi.Agree {α β : Type*} [HasPhi α] [HasPhi β] (a : α) (b : β) : Prop :=
  Compat (phi a) (phi b)

instance {α β : Type*} [HasPhi α] [HasPhi β] (a : α) (b : β) :
    Decidable (HasPhi.Agree a b) := by
  unfold HasPhi.Agree; infer_instance

namespace HasPhi.Agree

variable {α β : Type*} [HasPhi α] [HasPhi β]

@[refl] theorem refl (a : α) : HasPhi.Agree a a := compat_self _

theorem symm {a : α} {b : β} (h : HasPhi.Agree a b) : HasPhi.Agree b a := Compat.symm h

end HasPhi.Agree
