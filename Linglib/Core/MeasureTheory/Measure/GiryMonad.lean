/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Prod
public import Linglib.Core.Order.CompleteLattice
public import Linglib.Core.Order.OmegaCompletePartialOrder

/-!
# Monotonicity and ω-continuity of the Giry monad

`Measure.bind` is monotone in both arguments and commutes with suprema of monotone sequences in
both arguments. Together with the complete lattice structure on `Measure α`, this makes an
operator built from `bind` ω-Scott-continuous, so its least fixed point is the supremum of its
Kleene iterates (`fixedPoints.lfp_eq_sSup_iterate`). This is the least-fixed-point semantics of
recursive probabilistic programs of [kozen-1981], stated on the monad of [giry-1982].
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/GiryMonad.lean`.

## Main results

* `MeasureTheory.Measure.bind_mono`: `bind` is monotone in the measure and in the kernel.
* `MeasureTheory.Measure.iSup_apply_of_monotone`: the supremum of a monotone sequence of measures
  is computed pointwise on measurable sets.
* `MeasureTheory.lintegral_iSup_measure_of_monotone`: Lebesgue integrals commute with monotone
  suprema of measures.
* `MeasureTheory.Measure.iSup_bind_of_monotone`, `MeasureTheory.Measure.bind_iSup_of_monotone`:
  `bind` commutes with monotone suprema in each argument.
* `MeasureTheory.Measure.ωScottContinuous_bind`, `MeasureTheory.Measure.ωScottContinuous_map`,
  `MeasureTheory.Measure.ωScottContinuous_prod`: `bind` is ω-Scott-continuous jointly in the
  measure and the kernel, `map` in the measure and `prod` in both factors, so operators built
  from them have Kleene least fixed points.

## Implementation notes

`Measure α` is an ω-complete partial order through its complete lattice, while a Pi type of
measures also carries the product ω-CPO instance; the two agree but not reducibly, so continuity
proofs are pinned to explicit suprema through `CompleteLattice.ωSup_eq_iSup` and
`Pi.ωSup_eq_iSup` rather than to `ωSup`.

## References

* [giry-1982]
* [kozen-1981]
-/

@[expose] public section

open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

namespace ENNReal

theorem iSup_tsum_of_monotone {ι : Type*} {g : ℕ → ι → ℝ≥0∞} (hg : Monotone g) :
    ⨆ n, ∑' i, g n i = ∑' i, ⨆ n, g n i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  exact iSup_congr fun s => (ENNReal.finsetSum_iSup fun m n =>
    ⟨max m n, fun i => ⟨hg (le_max_left m n) i, hg (le_max_right m n) i⟩⟩).symm

end ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Measure

theorem bind_mono_left {μ ν : Measure α} {f : α → Measure β} (hμν : μ ≤ ν)
    (hf : AEMeasurable f ν) : μ.bind f ≤ ν.bind f := by
  refine le_iff.2 fun s hs => ?_
  rw [bind_apply hs (hf.mono_measure hμν), bind_apply hs hf]
  exact lintegral_mono' hμν le_rfl

theorem bind_mono_right {μ : Measure α} {f g : α → Measure β} (hfg : ∀ a, f a ≤ g a)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : μ.bind f ≤ μ.bind g := by
  refine le_iff.2 fun s hs => ?_
  rw [bind_apply hs hf, bind_apply hs hg]
  exact lintegral_mono fun a => le_iff'.1 (hfg a) s

theorem bind_mono {μ ν : Measure α} {f g : α → Measure β} (hμν : μ ≤ ν)
    (hfg : ∀ a, f a ≤ g a)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) : μ.bind f ≤ ν.bind g :=
  (bind_mono_right hfg hf (hg.mono_measure hμν)).trans (bind_mono_left hμν hg)

/-- The supremum of a monotone sequence of measures is computed pointwise on measurable sets. -/
theorem iSup_apply_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) {s : Set α}
    (hs : MeasurableSet s) : (⨆ n, μ n) s = ⨆ n, μ n s := by
  let ν : Measure α := ofMeasurable (fun s _ => ⨆ n, μ n s) (by simp) fun f hf hd => by
    simp_rw [measure_iUnion hd hf]
    exact ENNReal.iSup_tsum_of_monotone fun m n h i => le_iff.1 (hμ h) _ (hf i)
  have hν : (⨆ n, μ n) = ν := by
    refine le_antisymm (iSup_le fun n => le_iff.2 fun s hs => ?_) (le_iff.2 fun s hs => ?_)
    · rw [ofMeasurable_apply s hs]
      exact le_iSup (fun n => μ n s) n
    · rw [ofMeasurable_apply s hs]
      exact iSup_le fun n => le_iff.1 (le_iSup μ n) s hs
  rw [hν, ofMeasurable_apply s hs]

end Measure

/-- Simple-function integrals commute with monotone suprema of measures. -/
theorem SimpleFunc.lintegral_iSup_measure_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ)
    (g : SimpleFunc α ℝ≥0∞) : g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) := by
  simp only [SimpleFunc.lintegral]
  simp_rw [Measure.iSup_apply_of_monotone hμ (g.measurableSet_preimage _), ENNReal.mul_iSup]
  refine ENNReal.finsetSum_iSup fun i j => ⟨max i j, fun x => ⟨?_, ?_⟩⟩ <;> gcongr
  exacts [hμ (le_max_left i j), hμ (le_max_right i j)]

/-- Lebesgue integrals commute with monotone suprema of measures. -/
theorem lintegral_iSup_measure_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ)
    (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  simp_rw [lintegral_def, SimpleFunc.lintegral_iSup_measure_of_monotone hμ]
  rw [iSup_comm]
  exact iSup_congr fun g => iSup_comm

namespace Measure

theorem iSup_bind_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) {f : α → Measure β}
    (hf : Measurable f) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  ext s hs
  rw [bind_apply hs hf.aemeasurable,
    iSup_apply_of_monotone (fun m n h => bind_mono_left (hμ h) hf.aemeasurable) hs,
    lintegral_iSup_measure_of_monotone hμ]
  simp_rw [bind_apply hs hf.aemeasurable]

theorem measurable_iSup_measure_of_monotone {f : ℕ → α → Measure β} (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f) : Measurable fun a => ⨆ n, f n a :=
  measurable_of_measurable_coe _ fun s hs => by
    simp_rw [iSup_apply_of_monotone (fun m n h => hmono h _) hs]
    exact Measurable.iSup fun n => (measurable_coe hs).comp (hf n)

theorem bind_iSup_of_monotone {μ : Measure α} {f : ℕ → α → Measure β}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    μ.bind (fun a => ⨆ n, f n a) = ⨆ n, μ.bind (f n) := by
  have hpt : ∀ a, ∀ {s : Set β}, MeasurableSet s → (⨆ n, f n a) s = ⨆ n, f n a s :=
    fun a _ hs => iSup_apply_of_monotone (fun m n h => hmono h a) hs
  ext s hs
  rw [bind_apply hs (measurable_iSup_measure_of_monotone hf hmono).aemeasurable,
    iSup_apply_of_monotone
      (fun m n h => bind_mono_right (fun a => hmono h a) (hf m).aemeasurable
        (hf n).aemeasurable) hs]
  simp_rw [bind_apply hs (hf _).aemeasurable, hpt _ hs]
  exact lintegral_iSup (fun n => (measurable_coe hs).comp (hf n))
    fun m n h a => le_iff'.1 (hmono h a) s

/-! ### ω-Scott continuity -/

variable {γ : Type*} [OmegaCompletePartialOrder γ]

/-- `bind` is ω-Scott-continuous jointly in the measure and the kernel. -/
theorem ωScottContinuous_bind {M : γ → Measure α} {F : γ → α → Measure β}
    (hM : ωScottContinuous M) (hF : ∀ a, ωScottContinuous (F · a))
    (hmeas : ∀ x, Measurable (F x)) : ωScottContinuous fun x => (M x).bind (F x) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨fun x y h =>
    bind_mono (hM.monotone h) (fun a => (hF a).monotone h) (hmeas x).aemeasurable
      (hmeas y).aemeasurable, fun c => ?_⟩
  have hMc : Monotone fun n => M (c n) := fun m n h => hM.monotone (c.monotone h)
  have hFc : Monotone fun n => F (c n) := fun m n h a => (hF a).monotone (c.monotone h)
  have hM' : M (ωSup c) = ⨆ n, M (c n) := by
    rw [hM.map_ωSup, CompleteLattice.ωSup_eq_iSup]; rfl
  have hF' : F (ωSup c) = fun a => ⨆ n, F (c n) a := by
    funext a; rw [(hF a).map_ωSup, CompleteLattice.ωSup_eq_iSup]; rfl
  rw [CompleteLattice.ωSup_eq_iSup, hM', hF',
    iSup_bind_of_monotone hMc (measurable_iSup_measure_of_monotone (fun n => hmeas (c n)) hFc)]
  simp_rw [bind_iSup_of_monotone (fun n => hmeas (c n)) hFc]
  rw [iSup_iSup_eq_iSup_diag fun m n m' n' hm hn =>
    bind_mono (hMc hm) (fun a => hFc hn a) (hmeas (c n)).aemeasurable (hmeas (c n')).aemeasurable]
  rfl

theorem ωScottContinuous_map {M : γ → Measure α} (hM : ωScottContinuous M) {g : α → β}
    (hg : Measurable g) : ωScottContinuous fun x => (M x).map g := by
  simp_rw [← bind_dirac_eq_map _ hg]
  exact ωScottContinuous_bind hM (fun _ => ωScottContinuous.const) fun _ => measurable_dirac.comp hg

theorem ωScottContinuous_prod {M : γ → Measure α} {N : γ → Measure β} (hM : ωScottContinuous M)
    (hN : ωScottContinuous N) [∀ x, SFinite (N x)] :
    ωScottContinuous fun x => (M x).prod (N x) := by
  simp_rw [prod_eq_of_sfinite]
  exact ωScottContinuous_bind hM (fun a => ωScottContinuous_map hN measurable_prodMk_left)
    fun _ => Measurable.map_prodMk_left

theorem ωScottContinuous_bind_left {f : α → Measure β} (hf : Measurable f) :
    ωScottContinuous fun μ : Measure α => μ.bind f :=
  ωScottContinuous_bind ωScottContinuous.id (fun _ => ωScottContinuous.const) fun _ => hf

theorem ωScottContinuous_bind_right {μ : Measure α} {F : γ → α → Measure β}
    (hF : ∀ a, ωScottContinuous (F · a)) (hmeas : ∀ x, Measurable (F x)) :
    ωScottContinuous fun x => μ.bind (F x) :=
  ωScottContinuous_bind ωScottContinuous.const hF hmeas

end Measure

end MeasureTheory
