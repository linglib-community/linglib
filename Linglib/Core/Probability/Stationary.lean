/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Probability.IdentDistrib

/-!
# Stationary processes

A process `X : ℕ → Ω → α` is stationary when the law of a block of consecutive values does not
depend on where the block starts. A process that advances by a measure-preserving map of the
sample space is stationary.

## Main definitions

* `ProbabilityTheory.block X a n`: the `n` consecutive values of `X` from time `a`.
* `ProbabilityTheory.IsStationary X μ`: every block has the law of the block of the same length
  at time `0`.

## Main statements

* `MeasureTheory.MeasurePreserving.identDistrib_comp`: a measurable function has the same law
  after a measure-preserving map.
* `ProbabilityTheory.IsStationary.of_measurePreserving`: if `X (t + 1) = X t ∘ T` for a
  measure-preserving `T`, then `X` is stationary.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω α β : Type*} {X : ℕ → Ω → α}

/-- `block X a n` is the block of `n` consecutive values of `X` starting at time `a`. -/
def block (X : ℕ → Ω → α) (a n : ℕ) (ω : Ω) : Fin n → α := fun i ↦ X (i + a) ω

theorem block_zero_succ (t : ℕ) :
    block X 0 (t + 1) = (Fin.snocEquiv fun _ ↦ α) ∘ fun ω ↦ (X t ω, block X 0 t ω) :=
  funext fun _ ↦ (Fin.snoc_init_self _).symm

variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] {μ : Measure Ω}

theorem measurable_block (hX : ∀ t, Measurable (X t)) (a n : ℕ) : Measurable (block X a n) :=
  measurable_pi_iff.mpr fun i ↦ hX (i + a)

/-- A process is stationary when the law of a block does not depend on where it starts. -/
def IsStationary (X : ℕ → Ω → α) (μ : Measure Ω) : Prop :=
  ∀ a n, IdentDistrib (block X a n) (block X 0 n) μ μ

theorem IsStationary.comp (hs : IsStationary X μ) {f : α → β} (hf : Measurable f) :
    IsStationary (fun t ω ↦ f (X t ω)) μ :=
  fun a n ↦ (hs a n).comp (u := fun (v : Fin n → α) i ↦ f (v i)) (by fun_prop)

theorem _root_.MeasureTheory.MeasurePreserving.identDistrib_comp {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → β} (hf : Measurable f) : IdentDistrib (f ∘ T) f μ μ :=
  ⟨(hf.comp hT.measurable).aemeasurable, hf.aemeasurable,
    by rw [← Measure.map_map hf hT.measurable, hT.map_eq]⟩

theorem IsStationary.of_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hX : ∀ t, Measurable (X t)) (h : ∀ t, X (t + 1) = X t ∘ T) : IsStationary X μ := by
  have hblock (a n : ℕ) : block X a n = block X 0 n ∘ T^[a] := by
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [Function.iterate_succ, ← Function.comp_assoc, ← ih]
      funext ω i
      simp only [block, Function.comp_apply, ← add_assoc, h]
  intro a n
  rw [hblock]
  exact (hT.iterate a).identDistrib_comp (measurable_block hX 0 n)

end ProbabilityTheory
