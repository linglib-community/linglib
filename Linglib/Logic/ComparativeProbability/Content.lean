module

public import Linglib.Logic.ComparativeProbability.Defs
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic.Linarith

/-!
# Measures, qualitatively additive contents, and the orders they induce

A probability measure `μ` on a space in which every event is measurable orders events by
`A ≿ B ↔ μ B ≤ μ A` (`Measure.inducedGe`). A qualitatively additive measure (`QualAddMeasure`)
need not add over disjoint unions: it fixes the comparison of two events only through their
differences. A probability measure is a qualitatively additive measure through its real values
`μ.real` (`Measure.toQualAdd`), and each kind induces a qualitative probability order.

## Main definitions

* `QualAddMeasure`: qualitatively additive contents, applied as functions `m A`.
* `QualAddMeasure.ofRepr`: a normalized function representing a qualitative probability.
* `MeasureTheory.Measure.inducedGe`: the order a measure induces.
* `MeasureTheory.Measure.toQualAdd`: a probability measure as a qualitatively additive measure.

## Implementation notes

Events are arbitrary subsets, so the carrier is a `DiscreteMeasurableSpace`, as every finite
type with measurable singletons is. A qualitatively additive measure is not a measure, so it
stays a structure valued in an ordered field.
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

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

/-- `m.inducedGe A B` is the comparative likelihood `A ≿ B ↔ μ(A) ≥ μ(B)` that the measure
    induces. -/
def inducedGe (m : QualAddMeasure K W) (A B : Set W) : Prop := m A ≥ m B

theorem mu_mono (m : QualAddMeasure K W) {A B : Set W} (h : A ⊆ B) :
    m A ≤ m B := by
  rw [m.qualAdd A B, Set.sdiff_eq_empty.mpr h, m.mu_empty]; exact m.nonneg (B \ A)

/-- A qualitatively additive measure induces a qualitative probability. -/
instance (m : QualAddMeasure K W) : IsQualitativeProbability m.inducedGe where
  refl _ := le_rfl
  trans _ _ _ hab hbc := le_trans hbc hab
  total A B := le_total (m B) (m A)
  mono _ _ h := m.mu_mono h
  qadd A B := m.qualAdd B A
  bot_not_ge_top := by simp [inducedGe]

variable {r : Set W → Set W → Prop} [IsQualitativeProbability r]

/-- A function representing a qualitative probability and normalized to `0` on `∅` and `1` on
    the whole space is a qualitatively additive measure, nonnegative by monotonicity and
    qualitatively additive because the order is. -/
def ofRepr (f : Set W → K) (hf : ∀ A B, r A B ↔ f B ≤ f A) (h0 : f ∅ = 0)
    (h1 : f Set.univ = 1) : QualAddMeasure K W where
  toFun := f
  nonneg' A := by rw [← h0]; exact (hf A ∅).mp (rel_bot A)
  empty' := h0
  total' := h1
  qualAdd' A B := by rw [← hf, ← hf]; exact qadd B A

theorem inducedGe_ofRepr (f : Set W → K) (hf : ∀ A B, r A B ↔ f B ≤ f A) (h0 : f ∅ = 0)
    (h1 : f Set.univ = 1) : (ofRepr f hf h0 h1).inducedGe = r :=
  funext₂ fun A B ↦ propext (hf A B).symm

end QualAddMeasure

end ComparativeProbability

/-! ### Probability measures -/

namespace MeasureTheory.Measure

open ComparativeProbability

variable {W : Type*} [MeasurableSpace W]

/-- `μ.inducedGe A B` is the comparative likelihood `A ≿ B ↔ μ(A) ≥ μ(B)` that the measure
    induces. -/
def inducedGe (μ : Measure W) (A B : Set W) : Prop := μ B ≤ μ A

theorem inducedGe_iff_real (μ : Measure W) [IsFiniteMeasure μ] {A B : Set W} :
    μ.inducedGe A B ↔ μ.real B ≤ μ.real A :=
  (ENNReal.toReal_le_toReal (measure_ne_top μ B) (measure_ne_top μ A)).symm

theorem strict_inducedGe_iff_real (μ : Measure W) [IsFiniteMeasure μ] {A B : Set W} :
    Strict μ.inducedGe A B ↔ μ.real B < μ.real A := by
  rw [Strict, μ.inducedGe_iff_real, μ.inducedGe_iff_real, not_le]
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

@[simp] theorem toQualAdd_apply (A : Set W) : μ.toQualAdd A = μ.real A := rfl

theorem inducedGe_eq_toQualAdd : μ.inducedGe = μ.toQualAdd.inducedGe := by
  funext A B
  exact propext μ.inducedGe_iff_real

/-- A probability measure on a discrete space induces a qualitative probability. -/
instance : IsQualitativeProbability μ.inducedGe where
  refl _ := le_rfl
  trans _ _ _ hab hbc := le_trans hbc hab
  total A B := le_total (μ B) (μ A)
  mono _ _ h := measure_mono h
  qadd A B := μ.measure_le_iff_sdiff_le B A
  bot_not_ge_top := by simp [inducedGe]

end MeasureTheory.Measure
