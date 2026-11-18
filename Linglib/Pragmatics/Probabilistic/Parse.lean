module

public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Pragmatics.Probabilistic.Maximin

/-!
# Uncertainty about the parse

A speaker unsure how the listener will parse her utterance addresses the listeners of the parses
as [one listener on pairs of a parse and a state](##RSA.parseListener).

## References

* [spector-2025]
* [M. Franke and L. Bergen, *Theory-Driven Statistical Modeling for Semantics and Pragmatics: A
  Case Study on Grammatically Generated Implicature Readings* (2020)][franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

/-! #### Uncertainty about the parse

A speaker unsure how the listener will parse her utterance addresses the literal listeners of the
parses as one listener on pairs of a parse and a state. Knowing the state `w` and holding a prior
`ν` over the parses, she believes `ν.prod (dirac w)`: the expected-utility speaker then weighs the
parses' listeners by their geometric mean under `ν`, the MaxiMin speaker by their least value over
the parses `ν` allows, and neither uses an utterance that one of those parses rules out at `w`. -/

section Parse

variable {ι : Type*} [MeasurableSpace ι]

/-- The literal listeners of a family of parses, as one listener on pairs of a parse and a
state. -/
noncomputable def parseListener (L : ι → U → Measure W) (u : U) : Measure (ι × W) :=
  Measure.sum fun i ↦ (L i u).map (Prod.mk i)

instance [Fintype ι] (L : ι → U → Measure W) [∀ i u, IsFiniteMeasure (L i u)] (u : U) :
    IsFiniteMeasure (parseListener L u) := by
  unfold parseListener; infer_instance

variable [MeasurableSingletonClass ι] [MeasurableSingletonClass W] {L : ι → U → Measure W}
  {ν : Measure ι} {u : U} {w : W}

omit [MeasurableSpace U] in
@[simp] theorem parseListener_apply_singleton (L : ι → U → Measure W) (u : U) (i : ι) (w : W) :
    parseListener L u {(i, w)} = L i u {w} := by
  rw [parseListener, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single i]
  · rw [Measure.map_apply measurable_prodMk_left (measurableSet_singleton _)]
    congr 1; ext; simp
  · intro j hji
    rw [Measure.map_apply measurable_prodMk_left (measurableSet_singleton _)]
    convert measure_empty (μ := L j u)
    ext; simp [hji]

omit [MeasurableSpace U] in
/-- Under the belief `ν.prod (dirac w)` the geometric mean of the listener's mass is that of the
parses' listeners at `w` under `ν`. -/
theorem geomMean_prod_dirac_parseListener [Fintype ι] [Fintype W] :
    (ν.prod (Measure.dirac w)).geomMean (fun p ↦ parseListener L u {p}) =
      ν.geomMean fun i ↦ L i u {w} := by
  simp only [Measure.geomMean_prod, Measure.geomMean_dirac, parseListener_apply_singleton]

omit [MeasurableSpace U] in
/-- Under the belief `ν.prod (dirac w)` the essential infimum of the listener's mass is that of
the parses' listeners at `w` under `ν`. -/
theorem essInf_prod_dirac_parseListener [SFinite ν] :
    essInf (fun p ↦ parseListener L u {p}) (ν.prod (Measure.dirac w)) =
      essInf (fun i ↦ L i u {w}) ν := by
  rw [Measure.prod_dirac]
  refine ((measurableEmbedding_prod_mk_right w).essSup_map_measure (β := ℝ≥0∞ᵒᵈ)).trans ?_
  simp only [Function.comp_def, parseListener_apply_singleton]
  rfl

omit [MeasurableSpace U] in
private theorem exists_prod_dirac_parseListener_eq_zero_iff :
    (∃ p, ν.prod (Measure.dirac w) {p} ≠ 0 ∧ parseListener L u {p} = 0) ↔
      ∃ i, ν {i} ≠ 0 ∧ L i u {w} = 0 := by
  refine ⟨fun ⟨⟨i, v⟩, hp, hL⟩ ↦ ?_, fun ⟨i, hi, hL⟩ ↦
    ⟨(i, w), (Measure.prod_dirac_apply_singleton_ne_zero_iff ν w _).2 ⟨hi, rfl⟩, by simpa⟩⟩
  obtain ⟨hi, rfl⟩ := (Measure.prod_dirac_apply_singleton_ne_zero_iff ν w (i, v)).1 hp
  exact ⟨i, hi, by simpa using hL⟩

variable [Fintype ι] [Fintype W] [Fintype U] [MeasurableSingletonClass U] [Countable O]
  [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} [∀ i u, IsFiniteMeasure (L i u)] {o : O}

/-- The expected-utility speaker never uses an utterance that a parse her prior allows rules out
at her state. -/
theorem speaker_parseListener_apply_singleton_eq_zero_iff [IsFiniteMeasure ν] (f : O → W)
    (hα : 0 < α) :
    speaker α C (parseListener L) (fun o ↦ ν.prod (Measure.dirac (f o))) o {u} = 0 ↔
      ∃ i, ν {i} ≠ 0 ∧ L i u {f o} = 0 := by
  rw [speaker_apply_singleton_eq_zero_iff hα, exists_prod_dirac_parseListener_eq_zero_iff]

/-- Nor does the MaxiMin speaker. -/
theorem maximinSpeaker_parseListener_apply_singleton_eq_zero_iff (f : O → W) (hα : 0 < α)
    (hν : ∃ i, ν {i} ≠ 0) :
    maximinSpeaker α C (parseListener L) (fun o ↦ ν.prod (Measure.dirac (f o))) o {u} = 0 ↔
      ∃ i, ν {i} ≠ 0 ∧ L i u {f o} = 0 := by
  obtain ⟨i, hi⟩ := hν
  rw [maximinSpeaker_apply_singleton_eq_zero_iff (b := fun o ↦ ν.prod (Measure.dirac (f o))) hα
      ⟨(i, f o), (Measure.prod_dirac_apply_singleton_ne_zero_iff ν _ _).2 ⟨hi, rfl⟩⟩,
    exists_prod_dirac_parseListener_eq_zero_iff]

end Parse

end Pipeline

end RSA
