/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Minimalist.Feature.Basic

/-!
# Nominals as goals of φ-probes

The goals of a φ-probe are nominals. The bundle of a nominal carries its φ-cell and a checking slot
for its case, and the nominal is active, visible to Agree, when that slot is unvalued: an unvalued
structural case feature makes a goal active ([chomsky-2000]).

## Main definitions

* `Minimalist.FeatureBundle.nominal`: the bundle of a nominal with a φ-cell and a case slot.
* `Minimalist.FeatureBundle.IsActive`: a bundle whose case slot is unvalued.

## References

* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

namespace FeatureBundle

/-- The bundle of a nominal with φ-cell `c` and case slot `k`. -/
def nominal (c : Agreement.Bundle) (k : FeatureSlot (Flat Case)) : FeatureBundle :=
  Function.update (ofAgreement c) .case k

/-- A bundle is active when its case slot is unvalued. -/
def IsActive (b : FeatureBundle) : Prop := b .case = .unvalued

instance (b : FeatureBundle) : Decidable b.IsActive := inferInstanceAs (Decidable (_ = _))

variable {c : Agreement.Bundle} {k : FeatureSlot (Flat Case)}

@[simp] theorem nominal_case : nominal c k .case = k := Function.update_self ..

@[simp] theorem isActive_nominal : (nominal c k).IsActive ↔ k = .unvalued := by
  simp [IsActive]

@[simp] theorem agreement_nominal :
    (nominal c k).agreement = Function.update c .case (k.unbotD ⊥) := by
  rw [nominal, agreement_update_agr, agreement_ofAgreement]

theorem update_case_nominal (k' : FeatureSlot (Flat Case)) :
    Function.update (nominal c k) .case k' = nominal c k' :=
  Function.update_idem ..

end FeatureBundle

end Minimalist
