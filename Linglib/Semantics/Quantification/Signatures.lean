/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Natural.Soundness

/-!
# Signature profiles of generalized quantifiers

This file instantiates the natural-logic signature calculus at determiner denotations: *every*
and *no* receive certified `Signature₂` profiles, read off the anti-additivity and monotonicity
of their sections, and *not every* is derived by profile composition.

## Main results

* `soundFor_every`, `soundFor_no`: the certified determiner profiles.

## References

* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier.Det

open NaturalLogic

variable {α : Type*}

/-! ### Certified determiner profiles -/

/-- *Every* realizes ↓MON↑ as a certified profile, the restrictor side
derived from left anti-additivity (`leftAntiAdditive_every`). -/
theorem soundFor_every :
    Signature₂.SoundFor ⟨.anti, .mono⟩ (every (α := α)) :=
  ⟨fun S => soundFor_anti_iff.mpr
      ((leftAntiAdditive_every S).antitone),
   fun R => soundFor_mono_iff.mpr
      (scopeMonotone_every R)⟩

/-- *No* realizes ↓MON↓, both positions via anti-additivity (`leftAntiAdditive_no`,
`rightAntiAdditive_no`). -/
theorem soundFor_no :
    Signature₂.SoundFor ⟨.anti, .anti⟩ (no (α := α)) :=
  ⟨fun S => soundFor_anti_iff.mpr
      ((leftAntiAdditive_no S).antitone),
   fun R => soundFor_anti_iff.mpr
      ((rightAntiAdditive_no R).antitone)⟩

/-- *Not every* is obtained by composition, since negating *every* composes the anti-morphism
row into both positions of *every*'s profile; the scope component `.antiAddMult * .mono = .anti`
records that *any* is licensed in *not every*'s scope. -/
example : Signature₂.SoundFor ⟨.antiAddMult * .anti, .antiAddMult * .mono⟩
    (fun R S => ¬ every (α := α) R S) :=
  not_soundFor_antiAddMult.comp₂ (σ := ⟨.anti, .mono⟩) soundFor_every

end Quantifier.Det
