/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Stationary processes

A process `X : ι → Ω → α` is *stationary* when shifting time leaves its law on `ι → α` unchanged,
which says that [every shift of `ι → α` preserves that law](##isStationary_iff_measurePreserving).
The finite-dimensional distributions determine the law, so stationarity can be
[checked on finite sets of times](##isStationary_iff_forall_finset), and over `ℕ` on
[blocks of consecutive values](##isStationary_iff_forall_block), the form in which information
theory defines it. Over `ℕ` [a shift by one is enough](##isStationary_iff_identDistrib_succ), and a
process that [advances by a measure-preserving map](##IsStationary.of_measurePreserving) of the
sample space is stationary.

## Implementation notes

`[UPSTREAM]` candidate: mathlib has no notion of a stationary process.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {ι Ω α β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω}

section Add

variable [Add ι] {X : ι → Ω → α}

/-- A process is (strictly) *stationary* when shifting time does not change its law. -/
def IsStationary (X : ι → Ω → α) (μ : Measure Ω) : Prop :=
  ∀ s, IdentDistrib (fun ω t ↦ X (t + s) ω) (fun ω t ↦ X t ω) μ μ

theorem IsStationary.comp (hs : IsStationary X μ) {f : α → β} (hf : Measurable f) :
    IsStationary (fun t ω ↦ f (X t ω)) μ :=
  fun s ↦ (hs s).comp (u := fun x t ↦ f (x t)) (by fun_prop)

private theorem identDistrib_shift_iff (hX : AEMeasurable (fun ω t ↦ X t ω) μ) (s : ι) :
    IdentDistrib (fun ω t ↦ X (t + s) ω) (fun ω t ↦ X t ω) μ μ ↔
      MeasurePreserving (fun (x : ι → α) t ↦ x (t + s))
        (μ.map fun ω t ↦ X t ω) (μ.map fun ω t ↦ X t ω) := by
  have hm : Measurable fun (x : ι → α) t ↦ x (t + s) := by fun_prop
  have hmap := AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hX
  exact ⟨fun h ↦ ⟨hm, hmap.trans h.map_eq⟩,
    fun h ↦ ⟨hm.comp_aemeasurable hX, hX, hmap.symm.trans h.map_eq⟩⟩

theorem isStationary_iff_measurePreserving (hX : AEMeasurable (fun ω t ↦ X t ω) μ) :
    IsStationary X μ ↔ ∀ s, MeasurePreserving (fun (x : ι → α) t ↦ x (t + s))
      (μ.map fun ω t ↦ X t ω) (μ.map fun ω t ↦ X t ω) :=
  forall_congr' (identDistrib_shift_iff hX)

theorem isStationary_iff_forall_finset [IsFiniteMeasure μ]
    (hX : AEMeasurable (fun ω t ↦ X t ω) μ) :
    IsStationary X μ ↔ ∀ (s : ι) (I : Finset ι),
      IdentDistrib (fun ω ↦ I.restrict fun t ↦ X (t + s) ω) (fun ω ↦ I.restrict (X · ω)) μ μ :=
  forall_congr' fun s ↦ identDistrib_iff_forall_finset_identDistrib
    ((by fun_prop : Measurable fun (x : ι → α) t ↦ x (t + s)).comp_aemeasurable hX) hX

end Add

variable {X : ℕ → Ω → α}

/-- `block X a n` is the block of `n` consecutive values of `X` starting at time `a`. -/
def block (X : ℕ → Ω → α) (a n : ℕ) (ω : Ω) : Fin n → α := fun i ↦ X (i + a) ω

omit [MeasurableSpace α] in
theorem block_zero_succ (t : ℕ) :
    block X 0 (t + 1) = (Fin.snocEquiv fun _ ↦ α) ∘ fun ω ↦ (X t ω, block X 0 t ω) :=
  funext fun _ ↦ (Fin.snoc_init_self _).symm

theorem measurable_block (hX : ∀ t, Measurable (X t)) (a n : ℕ) : Measurable (block X a n) :=
  measurable_pi_iff.mpr fun i ↦ hX (i + a)

theorem IsStationary.identDistrib_block (hs : IsStationary X μ) (a n : ℕ) :
    IdentDistrib (block X a n) (block X 0 n) μ μ := by
  have hu : Measurable fun (x : ℕ → α) (i : Fin n) ↦ x i := by fun_prop
  exact (hs a).comp hu

/-- A process is stationary exactly when a block of `n` consecutive values has the same law wherever
it starts, which is how information theory states the definition. -/
theorem isStationary_iff_forall_block [IsFiniteMeasure μ] :
    IsStationary X μ ↔ ∀ a n, IdentDistrib (block X a n) (block X 0 n) μ μ := by
  refine ⟨fun hs ↦ hs.identDistrib_block, fun h ↦ ?_⟩
  have hX : AEMeasurable (fun ω t ↦ X t ω) μ := aemeasurable_pi_iff.2 fun t ↦ by
    simpa [block, Function.comp_def] using
      (measurable_pi_apply (0 : Fin 1)).comp_aemeasurable (h t 1).aemeasurable_fst
  refine (isStationary_iff_forall_finset hX).2 fun s I ↦ ?_
  have hu : Measurable fun (v : Fin (I.sup id + 1) → α) (i : I) ↦
      v ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.2)⟩ := by fun_prop
  exact (h s _).comp hu

theorem isStationary_iff_identDistrib_succ :
    IsStationary X μ ↔ IdentDistrib (fun ω t ↦ X (t + 1) ω) (fun ω t ↦ X t ω) μ μ := by
  refine ⟨fun hs ↦ hs 1, fun h s ↦ ?_⟩
  induction s with
  | zero => exact .refl h.aemeasurable_snd
  | succ s ih =>
    have hu : Measurable fun (x : ℕ → α) t ↦ x (t + s) := by fun_prop
    exact (h.comp hu).trans ih

theorem IsStationary.of_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hX : ∀ t, Measurable (X t)) (h : ∀ t, X (t + 1) = X t ∘ T) : IsStationary X μ := by
  have hpath : Measurable fun ω t ↦ X t ω := measurable_pi_iff.2 hX
  exact isStationary_iff_identDistrib_succ.2 <| (identDistrib_shift_iff hpath.aemeasurable 1).2 <|
    .of_semiconj ⟨hpath, rfl⟩ hT (fun ω ↦ funext fun t ↦ (congrFun (h t) ω).symm) (by fun_prop)

end ProbabilityTheory
