module

public import Linglib.Logic.ComparativeProbability.Defs
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic.Linarith

/-!
# Measures, qualitatively additive contents, and the orders they induce

This file defines the order a set function induces and qualitatively additive measures. A set
function `f` orders events by `A ≿ B ↔ f B ≤ f A`, and this order is a qualitative probability
exactly when `f ∅ < f Set.univ`, `f ∅ ≤ f A` for every `A`, and `f` compares two events as it
compares their differences. A probability measure on a space in which every event is measurable
meets these conditions. A qualitatively additive measure is a normalized function that meets
them without adding over disjoint unions; a probability measure is one through its real values.

## Main definitions

* `inducedGe`: the order a set function induces.
* `QualAddMeasure`: qualitatively additive contents, applied as functions `m A`.
* `QualAddMeasure.ofRepr`: a normalized function inducing a qualitative probability.
* `MeasureTheory.Measure.toQualAdd`: a probability measure as a qualitatively additive measure.

## Main statements

* `isQualitativeProbability_inducedGe_iff`: when the order a set function induces is a
  qualitative probability.

## Implementation notes

Events are arbitrary subsets, so the carrier is a `DiscreteMeasurableSpace`, as every finite
type with measurable singletons is. A qualitatively additive measure is not a measure, so it
stays a structure valued in an ordered field.
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

/-! ### The order a set function induces -/

section Induced

variable {W β : Type*}

/-- `inducedGe f A B` is the comparative likelihood `A ≿ B ↔ f B ≤ f A` that a set function `f`
    induces, the preimage `f ⁻¹'o (· ≥ ·)`. -/
def inducedGe [LE β] (f : Set W → β) (A B : Set W) : Prop := f B ≤ f A

/-- The order a set function `f` induces is a qualitative probability iff `f ∅ < f Set.univ`,
    `f ∅ ≤ f A` for every `A`, and `f` compares two events as it compares their differences.
    These are de Finetti's axioms (i), (ii) and (v) read through `f`; every induced order is
    total and transitive. -/
theorem isQualitativeProbability_inducedGe_iff [LinearOrder β] {f : Set W → β} :
    IsQualitativeProbability (inducedGe f) ↔
      f ∅ < f Set.univ ∧ (∀ A, f ∅ ≤ f A) ∧ ∀ A B, f A ≤ f B ↔ f (A \ B) ≤ f (B \ A) :=
  ⟨fun _ ↦ ⟨lt_of_not_ge (IsNontrivial.bot_not_ge_top (r := inducedGe f)),
      rel_bot (r := inducedGe f), fun A B ↦ qadd (r := inducedGe f) B A⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦
      { trans _ _ _ hab hbc := hbc.trans hab
        total A B := le_total (f B) (f A)
        rel_bot' := h₂
        qadd A B := h₃ B A
        bot_not_ge_top := not_le.mpr h₁ }⟩

end Induced

/-! ### Qualitatively additive measures -/

/-- A qualitatively additive measure on subsets of `W` need not add over disjoint unions; it
    satisfies only the weaker **qualitative additivity**
    `μ(A) ≥ μ(B) ↔ μ(A \ B) ≥ μ(B \ A)`. Every qualitative probability order on a finite
    carrier is represented by one (`exists_qualAddMeasure_repr`). -/
structure QualAddMeasure (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (W : Type*) where
  /-- `toFun A` is the measure of `A`. Apply the measure itself, `m A`. -/
  toFun : Set W → K
  /-- Every event has nonnegative measure. Use the lemma `nonneg`. -/
  nonneg' : ∀ A, 0 ≤ toFun A
  /-- The impossible proposition has measure zero. Use the lemma `mu_empty`. -/
  empty' : toFun ∅ = 0
  /-- The sure event has measure one. Use the lemma `total`. -/
  total' : toFun Set.univ = 1
  /-- Two events compare as their differences do. Use the lemma `qualAdd`. -/
  qualAdd' : ∀ A B, toFun A ≤ toFun B ↔ toFun (A \ B) ≤ toFun (B \ A)

namespace QualAddMeasure

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}

instance : FunLike (QualAddMeasure K W) (Set W) K where
  coe := toFun
  coe_injective m m' _ := by cases m; cases m'; congr

@[simp] theorem coe_mk (f : Set W → K) (h₁ h₂ h₃ h₄) :
    ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : QualAddMeasure K W) = f := rfl

@[ext] theorem ext {m m' : QualAddMeasure K W} (h : ∀ A, m A = m' A) : m = m' :=
  DFunLike.ext m m' h

theorem nonneg (m : QualAddMeasure K W) (A : Set W) : 0 ≤ m A := m.nonneg' A

@[simp] theorem mu_empty (m : QualAddMeasure K W) : m ∅ = 0 := m.empty'

@[simp] theorem total (m : QualAddMeasure K W) : m Set.univ = 1 := m.total'

theorem qualAdd (m : QualAddMeasure K W) (A B : Set W) :
    m A ≤ m B ↔ m (A \ B) ≤ m (B \ A) := m.qualAdd' A B

/-- A qualitatively additive measure induces a qualitative probability. -/
instance (m : QualAddMeasure K W) : IsQualitativeProbability (inducedGe m) :=
  isQualitativeProbability_inducedGe_iff.mpr
    ⟨by simp, fun A ↦ by simpa using m.nonneg A, m.qualAdd⟩

variable {r : Set W → Set W → Prop} [IsQualitativeProbability r]

/-- A function inducing a qualitative probability and normalized to `0` on `∅` and `1` on the
    whole space is a qualitatively additive measure. -/
def ofRepr (f : Set W → K) (hf : inducedGe f = r) (h0 : f ∅ = 0) (h1 : f Set.univ = 1) :
    QualAddMeasure K W :=
  have h := isQualitativeProbability_inducedGe_iff.mp
    (hf ▸ ‹_› : IsQualitativeProbability (inducedGe f))
  { toFun := f
    nonneg' A := h0 ▸ h.2.1 A
    empty' := h0
    total' := h1
    qualAdd' := h.2.2 }

theorem inducedGe_ofRepr (f : Set W → K) (hf : inducedGe f = r) (h0 : f ∅ = 0)
    (h1 : f Set.univ = 1) : inducedGe (ofRepr f hf h0 h1) = r :=
  hf

end QualAddMeasure

end ComparativeProbability

/-! ### Probability measures -/

namespace MeasureTheory.Measure

open ComparativeProbability

variable {W : Type*} [MeasurableSpace W]

theorem inducedGe_iff_real (μ : Measure W) [IsFiniteMeasure μ] {A B : Set W} :
    inducedGe μ A B ↔ μ.real B ≤ μ.real A :=
  (ENNReal.toReal_le_toReal (measure_ne_top μ B) (measure_ne_top μ A)).symm

/-- A finite measure and its real values induce the same order. -/
theorem inducedGe_real (μ : Measure W) [IsFiniteMeasure μ] : inducedGe μ.real = inducedGe μ :=
  funext₂ fun _ _ ↦ propext μ.inducedGe_iff_real.symm

theorem strict_inducedGe_iff_real (μ : Measure W) [IsFiniteMeasure μ] {A B : Set W} :
    AsymmRel (inducedGe μ) A B ↔ μ.real B < μ.real A := by
  rw [AsymmRel, μ.inducedGe_iff_real, μ.inducedGe_iff_real, not_le]
  exact ⟨And.right, fun h ↦ ⟨h.le, h⟩⟩

theorem measure_le_iff_sdiff_le [DiscreteMeasurableSpace W] (μ : Measure W) [IsFiniteMeasure μ]
    (A B : Set W) : μ A ≤ μ B ↔ μ (A \ B) ≤ μ (B \ A) := by
  rw [← measure_sdiff_add_inter A (.of_discrete : MeasurableSet B),
    ← measure_sdiff_add_inter B (.of_discrete : MeasurableSet A), Set.inter_comm B A]
  exact ENNReal.add_le_add_iff_right (measure_ne_top μ _)

/-- A probability measure is qualitatively additive through its real values, since
    `μ(A) = μ(A \ B) + μ(A ∩ B)` and `μ(B) = μ(B \ A) + μ(A ∩ B)`. -/
noncomputable def toQualAdd [DiscreteMeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ] :
    QualAddMeasure ℝ W where
  toFun := μ.real
  nonneg' _ := measureReal_nonneg
  empty' := measureReal_empty
  total' := probReal_univ
  qualAdd' A B := by
    have key (X Y : Set W) : μ.real X = μ.real (X \ Y) + μ.real (X ∩ Y) :=
      (measureReal_sdiff_add_inter (.of_discrete)).symm
    rw [key A B, key B A, Set.inter_comm B A, add_le_add_iff_right]

variable [DiscreteMeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]

@[simp] theorem coe_toQualAdd : ⇑μ.toQualAdd = μ.real := rfl

/-- A probability measure on a discrete space induces a qualitative probability. -/
instance : IsQualitativeProbability (inducedGe μ) :=
  isQualitativeProbability_inducedGe_iff.mpr ⟨by simp, fun _ ↦ by simp, μ.measure_le_iff_sdiff_le⟩

end MeasureTheory.Measure
