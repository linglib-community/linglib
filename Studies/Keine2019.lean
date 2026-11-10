module

public import Linglib.Syntax.Minimalist.Probe.Profile
public import Linglib.Syntax.Minimalist.Clause.Spine

/-!
# Keine (2019): Selective Opacity

This file formalizes the horizons account of selective opacity of [keine-2019]: a syntactic
domain may be opaque to some operations and transparent to others (their (1)), and the constraint
is on the searches of probes, each terminated by a category of its own, its horizon ((38)),
rather than on domains or on the moving element. With category inheritance within an extended
projection ((43)) a clause's label collects the categories it projects, so a clause is opaque to a
probe exactly when its label contains the horizon, and Upward Entailment ((40)), that larger
clauses are at least as opaque, is the Horizon Inheritance Theorem ((45), (46)), transparency
antitone in the extension order of clause sizes (`sizes_le`). The Hindi probes of (48) and (57),
φ-agreement and A-movement on T⁰ with
horizon T, wh-licensing on C⁰ with horizon C and Ā-movement on C⁰ without one, derive the
transparency table (58) with its three locality types (`transparency_table`) and with it the
generalizations (21) and (23) on long-distance agreement; English hyperraising is A-movement
with horizon C (Section 4.2.3), and its availability elsewhere is the absence of that horizon
(`hyperraising_iff`).

The Height-Locality Connection ((33), (62)), that higher probes search into more kinds of
structure, is derived rather than stipulated: a probe whose horizon lies below its position finds
it in its sister and is vacuous ((63)), so for a nonvacuous probe the position bounds the horizon
and the horizon bounds the position, the Height-Locality Theorem ((65)) instantiated for Hindi in
(66) and (67).

## Implementation notes

Clauses are the substrate's `ClauseSpine`s and transparency is `Probe.Profile.TransparentTo`; the
article's probes are defined here, and vacuity is `Probe.Profile.IsVacuousIn` the finite clause,
where the sister of a probe on C⁰ is TP and of one on T⁰ is vP.

## References

* [keine-2019]
-/

@[expose] public section

namespace Keine2019

open Minimalist

/-! ### Horizons and Upward Entailment (Section 4.1) -/

/-- The clause sizes are ordered vP ≤ TP ≤ CP, so a probe blocked by a clause is blocked by every
larger one ((45), (46)). -/
theorem sizes_le : ClauseSpine.vP ≤ .tP ∧ ClauseSpine.tP ≤ .cP :=
  ⟨ClauseSpine.vP_le_tP, ClauseSpine.tP_le_cP⟩

/-! ### The Hindi probes (Section 4.2) -/

/-- The φ-agreement probe `[∗φ∗]` of (48b), on T⁰ with horizon T. -/
def phiProbe : Probe.Profile := ⟨.T, some .T⟩

/-- The A-movement probe `[•A•]` of (48a), on T⁰ with horizon T. -/
def aProbe : Probe.Profile := ⟨.T, some .T⟩

/-- The wh-licensing probe `[∗wh∗]` of (57), on C⁰ with horizon C. -/
def whLicensing : Probe.Profile := ⟨.C, some .C⟩

/-- The Ā-movement probe `[•Ā•]` of (48c), on C⁰ without horizon. -/
def ābarProbe : Probe.Profile := ⟨.C, none⟩

/-- A probe's row of the transparency table over the finite, large nonfinite and small
nonfinite clauses. -/
def row (p : Probe.Profile) : List Bool :=
  [ClauseSpine.cP, .tP, .vP].map fun s ↦ decide (p.TransparentTo s)

/-- (58): φ-agreement and A-movement search only into vP clauses, wh-licensing into TP and vP
clauses, Ā-movement into all three. -/
theorem transparency_table :
    row phiProbe = [false, false, true] ∧ row aProbe = [false, false, true] ∧
      row whLicensing = [false, true, true] ∧ row ābarProbe = [true, true, true] := by
  decide

theorem three_locality_types :
    row phiProbe ≠ row whLicensing ∧ row whLicensing ≠ row ābarProbe ∧
      row phiProbe ≠ row ābarProbe := by
  decide

-- (23), (49)
theorem finite_clauses_selectively_opaque :
    ¬ aProbe.TransparentTo .cP ∧ ¬ phiProbe.TransparentTo .cP ∧
      ābarProbe.TransparentTo .cP := by
  decide

-- (21), (50), (51)
theorem a_extraction_forces_lda :
    (∀ s ∈ [ClauseSpine.tP, .vP], aProbe.TransparentTo s → s = .vP ∧ phiProbe.TransparentTo s) ∧
      ābarProbe.TransparentTo .tP ∧ ¬ phiProbe.TransparentTo .tP := by
  decide

/-! ### Hyperraising (Section 4.2.3) -/

/-- The English A-probe, on T⁰ with horizon C. -/
def englishAProbe : Probe.Profile := ⟨.T, some .C⟩

/-- The English extraposition probe, on T⁰ with horizon T. -/
def extrapositionProbe : Probe.Profile := ⟨.T, some .T⟩

-- (59)
theorem hyperraising_blocked :
    ¬ englishAProbe.TransparentTo .cP ∧ ābarProbe.TransparentTo .cP ∧
      ¬ extrapositionProbe.TransparentTo .tP := by
  decide

theorem hyperraising_iff (h : Option Cat) :
    (⟨.T, h⟩ : Probe.Profile).TransparentTo .cP ↔ ∀ c ∈ ClauseSpine.cP, h ≠ some c := by
  simp only [Probe.Profile.TransparentTo, Option.mem_def, ne_eq]
  exact ⟨fun H c hc e ↦ H c e hc, fun H c e hc ↦ H c hc e⟩

/-! ### The Height-Locality Connection (Section 5) -/

-- (63)
theorem vacuous_example : (⟨.C, some .T⟩ : Probe.Profile).IsVacuousIn .cP := by decide

-- (65a)
theorem height_to_locality (h : Cat) :
    (¬ (⟨.C, some h⟩ : Probe.Profile).IsVacuousIn .cP → h ∉ ClauseSpine.tP) ∧
      (¬ (⟨.T, some h⟩ : Probe.Profile).IsVacuousIn .cP → h ∉ ClauseSpine.vP) := by
  simp

-- (65b)
theorem locality_to_height :
    (⟨.C, some .T⟩ : Probe.Profile).IsVacuousIn .cP ∧
      (⟨.T, some .v⟩ : Probe.Profile).IsVacuousIn .cP ∧
      (⟨.C, some .v⟩ : Probe.Profile).IsVacuousIn .cP :=
  have h : (⟨.T, some .v⟩ : Probe.Profile).IsVacuousIn .cP := by decide
  ⟨by decide, h, h.of_mem_below (by decide)⟩

theorem nonvacuous_transparent (h : Option Cat) :
    (¬ (⟨.C, h⟩ : Probe.Profile).IsVacuousIn .cP →
        (⟨.C, h⟩ : Probe.Profile).TransparentTo .tP ∧
          (⟨.C, h⟩ : Probe.Profile).TransparentTo .vP) ∧
      (¬ (⟨.T, h⟩ : Probe.Profile).IsVacuousIn .cP →
        (⟨.T, h⟩ : Probe.Profile).TransparentTo .vP) :=
  ⟨fun hp ↦ ⟨.of_not_isVacuousIn hp (by simp),
      .of_not_isVacuousIn hp (by simpa using ClauseSpine.vP_le_tP)⟩,
    fun hp ↦ .of_not_isVacuousIn hp (by simp)⟩

-- (21), (66), (67)
theorem hindi_consequences :
    (∀ p ∈ [phiProbe, aProbe, whLicensing, ābarProbe], ¬ p.IsVacuousIn .cP) ∧
      (∀ p ∈ [whLicensing, ābarProbe], p.TransparentTo .tP ∧ p.TransparentTo .vP) ∧
      (∀ p ∈ [phiProbe, aProbe], p.TransparentTo .vP) ∧
      (⟨.C, aProbe.horizon⟩ : Probe.Profile).IsVacuousIn .cP := by
  decide

end Keine2019
