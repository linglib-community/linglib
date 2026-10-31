module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Minimalist.Feature.Basic

/-!
# φ-probes

This file specializes `Probe` to φ-features. A relativized φ-probe seeks one feature and skips the
φ-cells (`Agreement.Bundle`) that lack it. Preminger's person probe π⁰ seeks [participant], and his
number probe #⁰ seeks [plural].

The goals of a φ-probe are nominals. The bundle of a nominal carries its φ-cell and a checking slot
for its case, and the nominal is active, visible to Agree, when that slot is unvalued: an unvalued
structural case feature makes a goal active ([chomsky-2000]).

## Main definitions

* `Minimalist.Probe.Target`: the feature a relativized φ-probe seeks.
* `Agreement.Bundle.visibleTo`: a φ-cell bears the feature a probe seeks.
* `Minimalist.Probe.Target.toProbe`: the probe over φ-cells that a target denotes.
* `Minimalist.FeatureBundle.nominal`: the bundle of a nominal with a φ-cell and a case slot.
* `Minimalist.FeatureBundle.IsActive`: a bundle whose case slot is unvalued.

## References

* [preminger-2014]
* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

/-- The feature a relativized φ-probe seeks. -/
inductive Probe.Target where
  /-- π⁰, the person probe, seeks [participant]. -/
  | participant
  /-- #⁰, the number probe, seeks [plural]. -/
  | plural
  deriving DecidableEq, Repr

/-- A φ-cell is visible to a relativized probe when it bears the feature the probe seeks. -/
def _root_.Agreement.Bundle.visibleTo (c : Agreement.Bundle) : Probe.Target → Bool
  | .participant => decide c.IsSAP
  | .plural => decide c.IsPlural

/-- The probe over φ-cells relativized to the feature a target seeks. -/
def Probe.Target.toProbe (t : Probe.Target) : Probe Agreement.Bundle :=
  .relativized (·.visibleTo t)

namespace FeatureBundle

/-- The bundle of a nominal with φ-cell `c` and case slot `k`. -/
def nominal (c : Agreement.Bundle) (k : FeatureSlot Case) : FeatureBundle :=
  Function.update (ofAgreement c) .case k

/-- A bundle is active when its case slot is unvalued. -/
def IsActive (b : FeatureBundle) : Prop := b .case = .unvalued

instance (b : FeatureBundle) : Decidable b.IsActive := inferInstanceAs (Decidable (_ = _))

variable {c : Agreement.Bundle} {k : FeatureSlot Case}

@[simp] theorem nominal_case : nominal c k .case = k := Function.update_self ..

@[simp] theorem isActive_nominal : (nominal c k).IsActive ↔ k = .unvalued := by
  simp [IsActive]

@[simp] theorem agreement_nominal : (nominal c k).agreement = Function.update c .case k.toFlat := by
  rw [nominal, agreement_update_agr, agreement_ofAgreement]

theorem update_case_nominal (k' : FeatureSlot Case) :
    Function.update (nominal c k) .case k' = nominal c k' :=
  Function.update_idem ..

end FeatureBundle

@[simp] theorem _root_.Agreement.Bundle.isSAP_update_case {c : Agreement.Bundle}
    {x : Flat Case} : Agreement.Bundle.IsSAP (Function.update c .case x) ↔ c.IsSAP := by
  simp [Agreement.Bundle.IsSAP, Agreement.Bundle.person]

end Minimalist
