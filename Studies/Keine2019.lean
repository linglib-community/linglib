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

Labels are the bilateral labels of the substrate's `ClauseSpine`s and transparency is
`Probe.Profile.TransparentTo`; the article's probes are defined here, and vacuity is
`Probe.Profile.IsVacuous`, which takes the sister of a probe on C⁰ to be TP and of one on T⁰ to
be vP.

## References

* [keine-2019]
-/

@[expose] public section

namespace Keine2019

open Minimalist

/-- The label of a finite clause, the categories inherited up its extended projection ((44)). -/
def cpLabel : Finset Cat := ClauseSpine.cP.label

/-- The label of a large nonfinite clause. -/
def tpLabel : Finset Cat := ClauseSpine.tP.label

/-- The label of a small nonfinite clause. -/
def vpLabel : Finset Cat := ClauseSpine.vP.label

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
  [cpLabel, tpLabel, vpLabel].map fun L ↦ decide (p.TransparentTo L)

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

/-- Finite clauses, edge included, are opaque to A-movement and φ-agreement but not to
Ā-movement, (23) for the finite clause embedding (49). -/
theorem finite_clauses_selectively_opaque :
    ¬ aProbe.TransparentTo cpLabel ∧ ¬ phiProbe.TransparentTo cpLabel ∧
      ābarProbe.TransparentTo cpLabel := by
  decide

/-- A nonfinite clause small enough for A-extraction is a vP and transparent to φ-agreement, while
Ā-movement also enters TP ((21), (50), (51)). -/
theorem a_extraction_forces_lda :
    (∀ L ∈ [tpLabel, vpLabel], aProbe.TransparentTo L → L = vpLabel ∧ phiProbe.TransparentTo L) ∧
      ābarProbe.TransparentTo tpLabel ∧ ¬ phiProbe.TransparentTo tpLabel := by
  decide

/-! ### Hyperraising (Section 4.2.3) -/

/-- The English A-probe, on T⁰ with horizon C. -/
def englishAProbe : Probe.Profile := ⟨.T, some .C⟩

/-- The English extraposition probe, on T⁰ with horizon T. -/
def extrapositionProbe : Probe.Profile := ⟨.T, some .T⟩

/-- No A-probe search enters a finite clause in English, while Ā-extraction is unaffected, and
extraposition, with horizon T, cannot leave even a nonfinite clause (59). -/
theorem hyperraising_blocked :
    ¬ englishAProbe.TransparentTo cpLabel ∧ ābarProbe.TransparentTo cpLabel ∧
      ¬ extrapositionProbe.TransparentTo tpLabel := by
  decide

theorem hyperraising_iff (h : Option Cat) :
    (⟨.T, h⟩ : Probe.Profile).TransparentTo cpLabel ↔ ∀ c ∈ cpLabel, h ≠ some c := by
  simp only [Probe.Profile.TransparentTo, Option.mem_def, ne_eq]
  exact ⟨fun H c hc e ↦ H c e hc, fun H c e hc ↦ H c hc e⟩

/-! ### The Height-Locality Connection (Section 5) -/

/-- A probe on C⁰ with horizon T finds its horizon in its sister and has no search space (63). -/
theorem vacuous_example : (⟨.C, some .T⟩ : Probe.Profile).IsVacuous := by decide

/-- A nonvacuous probe on C⁰ has no horizon within TP, and one on T⁰ none within vP (65a). -/
theorem height_to_locality (h : Cat) :
    (¬ (⟨.C, some h⟩ : Probe.Profile).IsVacuous → h ∉ tpLabel) ∧
      (¬ (⟨.T, some h⟩ : Probe.Profile).IsVacuous → h ∉ vpLabel) := by
  simp [Probe.Profile.IsVacuous, Probe.Profile.sisterLabel, tpLabel, vpLabel]

/-- A probe with horizon T is vacuous on C⁰, and one with horizon v on T⁰ and C⁰ (65b). -/
theorem locality_to_height :
    (⟨.C, some .T⟩ : Probe.Profile).IsVacuous ∧ (⟨.T, some .v⟩ : Probe.Profile).IsVacuous ∧
      (⟨.C, some .v⟩ : Probe.Profile).IsVacuous := by
  decide

theorem nonvacuous_transparent (h : Option Cat) :
    (¬ (⟨.C, h⟩ : Probe.Profile).IsVacuous →
        (⟨.C, h⟩ : Probe.Profile).TransparentTo tpLabel ∧
          (⟨.C, h⟩ : Probe.Profile).TransparentTo vpLabel) ∧
      (¬ (⟨.T, h⟩ : Probe.Profile).IsVacuous →
        (⟨.T, h⟩ : Probe.Profile).TransparentTo vpLabel) := by
  simp only [Probe.Profile.IsVacuous, Probe.Profile.sisterLabel, not_not, tpLabel, vpLabel]
  exact ⟨fun ht ↦ ⟨ht, ht.anti (ClauseSpine.le_def.1 ClauseSpine.vP_le_tP)⟩, id⟩

/-- The four Hindi probes are nonvacuous, so the two on C⁰ search into TP and vP clauses and the two
on T⁰ into vP clauses ((21), (66), (67)). -/
theorem hindi_consequences :
    (∀ p ∈ [phiProbe, aProbe, whLicensing, ābarProbe], ¬ p.IsVacuous) ∧
      (∀ p ∈ [whLicensing, ābarProbe], p.TransparentTo tpLabel ∧ p.TransparentTo vpLabel) ∧
      (∀ p ∈ [phiProbe, aProbe], p.TransparentTo vpLabel) ∧
      (⟨.C, aProbe.horizon⟩ : Probe.Profile).IsVacuous := by
  decide

end Keine2019
