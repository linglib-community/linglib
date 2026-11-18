module

public import Linglib.Syntax.Minimalist.Probe.Horizon
public import Linglib.Syntax.Minimalist.Clause.Spine
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject

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

Clauses are the substrate's `ClauseSpine`s and transparency is `HorizonSetting.TransparentTo`; the
article's probes are defined here, and vacuity is `HorizonSetting.IsVacuousIn` the finite clause,
where the sister of a probe on C⁰ is TP and of one on T⁰ is vP.

## References

* [keine-2019]
-/

@[expose] public section

namespace Keine2019

open Minimalist SyntacticObject PlanarSyntacticObject

/-! ### Horizons and Upward Entailment (Section 4.1) -/

/-- The clause sizes are ordered vP ≤ TP ≤ CP, so a probe blocked by a clause is blocked by every
larger one ((45), (46)). -/
theorem sizes_le : ClauseSpine.vP ≤ .tP ∧ ClauseSpine.tP ≤ .cP :=
  ⟨ClauseSpine.vP_le_tP, ClauseSpine.tP_le_cP⟩

/-! ### The Hindi probes (Section 4.2) -/

/-- The φ-agreement probe `[∗φ∗]` of (48b), on T⁰ with horizon T. -/
def phiProbe : HorizonSetting := ⟨.T, some .T⟩

/-- The A-movement probe `[•A•]` of (48a), on T⁰ with horizon T. -/
def aProbe : HorizonSetting := ⟨.T, some .T⟩

/-- The wh-licensing probe `[∗wh∗]` of (57), on C⁰ with horizon C. -/
def whLicensing : HorizonSetting := ⟨.C, some .C⟩

/-- The Ā-movement probe `[•Ā•]` of (48c), on C⁰ without horizon. -/
def ābarProbe : HorizonSetting := ⟨.C, none⟩

/-- A probe's row of the transparency table over the finite, large nonfinite and small
nonfinite clauses. -/
def row (p : HorizonSetting) : List Bool :=
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

/-! ### Search spaces on structures (Sections 4.1 and 4.2.1)

A matrix clause over a finite, a large nonfinite and a small nonfinite complement, with a DP at
the edge of each. A probe's search space is cut at every node it c-commands that inherits its
horizon (`HorizonSetting.cut`), so the edge of an opaque clause is out of reach with the rest. -/

def C₀ : PlanarSyntacticObject := .leaf ⟨.of .C [.T], 1⟩
def T₀ : PlanarSyntacticObject := .leaf ⟨.of .T [.V], 2⟩
def V₀ (c : Cat) : PlanarSyntacticObject := .leaf ⟨.of .V [c], 3⟩
def XP : PlanarSyntacticObject := .leaf ⟨.of .D [], 4⟩
def C₁ : PlanarSyntacticObject := .leaf ⟨.of .C [.T], 5⟩
def Subj : PlanarSyntacticObject := .leaf ⟨.of .D [], 6⟩
def T₁ : PlanarSyntacticObject := .leaf ⟨.of .T [.v], 7⟩
def v₁ : PlanarSyntacticObject := .leaf ⟨.of .v [.D], 8⟩
def Obj : PlanarSyntacticObject := .leaf ⟨.of .D [], 9⟩

/-- The small nonfinite complement, `[vP v DP]`. -/
def embVP : PlanarSyntacticObject := {v₁, Obj}

/-- The large nonfinite complement, `[TP DP [T vP]]`. -/
def embTP : PlanarSyntacticObject := {Subj, {T₁, embVP}}

/-- The finite complement, `[CP XP [C TP]]`. -/
def embCP : PlanarSyntacticObject := {XP, {C₁, embTP}}

/-- The matrix clause over a complement of category `c`. -/
def matrix (c : Cat) (emb : PlanarSyntacticObject) : PlanarSyntacticObject :=
  {C₀, {T₀, {V₀ c, emb}}}

/-- The DPs a probe with setting `p` on `host` finds in `t`, searching short of its horizon. -/
def found (p : HorizonSetting) (host t : PlanarSyntacticObject) : Finset SyntacticObject :=
  t.goalsUnder (t.leafProbe .D) host (p.cut headIndex? t)

/-- (47), (58): the A-probe reaches into a vP complement only, wh-licensing into TP and vP, and
the Ā-probe into all three; an opaque clause hides the DP at its edge as well. -/
theorem found_table :
    (found aProbe T₀ (matrix .C embCP) = ∅ ∧ found aProbe T₀ (matrix .T embTP) = ∅ ∧
        found aProbe T₀ (matrix .v embVP) = {↑Obj}) ∧
      (found whLicensing C₀ (matrix .C embCP) = ∅ ∧
        found whLicensing C₀ (matrix .T embTP) = {↑Subj} ∧
        found whLicensing C₀ (matrix .v embVP) = {↑Obj}) ∧
      found ābarProbe C₀ (matrix .C embCP) = {↑XP} ∧
        found ābarProbe C₀ (matrix .T embTP) = {↑Subj} ∧
        found ābarProbe C₀ (matrix .v embVP) = {↑Obj} := by
  decide +kernel

/-- (63): a probe on C⁰ with horizon T finds no DP whatever the complement, since its sister TP is
already a horizon. -/
theorem vacuous_finds_nothing :
    ∀ emb ∈ [(Cat.C, embCP), (.T, embTP), (.v, embVP)],
      found ⟨.C, some .T⟩ C₀ (matrix emb.1 emb.2) = ∅ := by
  decide +kernel

/-! ### Hyperraising (Section 4.2.3) -/

/-- The English A-probe, on T⁰ with horizon C. -/
def englishAProbe : HorizonSetting := ⟨.T, some .C⟩

/-- The English extraposition probe, on T⁰ with horizon T. -/
def extrapositionProbe : HorizonSetting := ⟨.T, some .T⟩

-- (59)
theorem hyperraising_blocked :
    ¬ englishAProbe.TransparentTo .cP ∧ ābarProbe.TransparentTo .cP ∧
      ¬ extrapositionProbe.TransparentTo .tP := by
  decide

theorem hyperraising_iff (h : Option Cat) :
    (⟨.T, h⟩ : HorizonSetting).TransparentTo .cP ↔ ∀ c ∈ ClauseSpine.cP, h ≠ some c := by
  rw [HorizonSetting.transparentTo_iff]
  exact ⟨fun H c hc e ↦ H c e hc, fun H c e hc ↦ H c hc e⟩

/-! ### The Height-Locality Connection (Section 5) -/

-- (63)
theorem vacuous_example : (⟨.C, some .T⟩ : HorizonSetting).IsVacuousIn .cP := by decide

-- (65a)
theorem height_to_locality (h : Cat) :
    (¬ (⟨.C, some h⟩ : HorizonSetting).IsVacuousIn .cP → h ∉ ClauseSpine.tP) ∧
      (¬ (⟨.T, some h⟩ : HorizonSetting).IsVacuousIn .cP → h ∉ ClauseSpine.vP) := by
  simp

-- (65b)
theorem locality_to_height :
    (⟨.C, some .T⟩ : HorizonSetting).IsVacuousIn .cP ∧
      (⟨.T, some .v⟩ : HorizonSetting).IsVacuousIn .cP ∧
      (⟨.C, some .v⟩ : HorizonSetting).IsVacuousIn .cP :=
  have h : (⟨.T, some .v⟩ : HorizonSetting).IsVacuousIn .cP := by decide
  ⟨by decide, h, h.of_mem_below (by decide)⟩

theorem nonvacuous_transparent (h : Option Cat) :
    (¬ (⟨.C, h⟩ : HorizonSetting).IsVacuousIn .cP →
        (⟨.C, h⟩ : HorizonSetting).TransparentTo .tP ∧
          (⟨.C, h⟩ : HorizonSetting).TransparentTo .vP) ∧
      (¬ (⟨.T, h⟩ : HorizonSetting).IsVacuousIn .cP →
        (⟨.T, h⟩ : HorizonSetting).TransparentTo .vP) :=
  ⟨fun hp ↦ ⟨.of_not_isVacuousIn hp (by simp),
      .of_not_isVacuousIn hp (by simpa using ClauseSpine.vP_le_tP)⟩,
    fun hp ↦ .of_not_isVacuousIn hp (by simp)⟩

-- (21), (66), (67)
theorem hindi_consequences :
    (∀ p ∈ [phiProbe, aProbe, whLicensing, ābarProbe], ¬ p.IsVacuousIn .cP) ∧
      (∀ p ∈ [whLicensing, ābarProbe], p.TransparentTo .tP ∧ p.TransparentTo .vP) ∧
      (∀ p ∈ [phiProbe, aProbe], p.TransparentTo .vP) ∧
      (⟨.C, aProbe.horizon⟩ : HorizonSetting).IsVacuousIn .cP := by
  decide

end Keine2019
