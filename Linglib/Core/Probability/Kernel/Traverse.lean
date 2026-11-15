/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Core.Probability.Kernel.Composition.Lemmas

/-!
# A kernel applied along a list

`Kernel.traverse κ` sends a list to the law of a list of independent draws, one from `κ` at each
entry: the product `Measure.listProd` of the measures `κ` assigns to the entries. Over countable
types it [commutes with pushing a product of measures
forward](##MeasureTheory.Measure.traverse_comp_listProd), so
[traversing is functorial](##ProbabilityTheory.Kernel.traverse_comp_traverse).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Draw independently from `κ` at each entry of a list. -/
noncomputable def traverse (κ : Kernel α β) : Kernel (List α) (List β) :=
  ⟨fun l ↦ Measure.listProd (l.map κ), .of_discrete⟩

@[simp] theorem traverse_apply (κ : Kernel α β) (l : List α) :
    κ.traverse l = Measure.listProd (l.map κ) := rfl

instance (κ : Kernel α β) [IsMarkovKernel κ] : IsMarkovKernel κ.traverse :=
  ⟨fun l ↦ Measure.isProbabilityMeasure_listProd fun μ hμ ↦ by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hμ
    infer_instance⟩

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable α]
  [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β]

/-- Pushing a product of measures through a traversal pushes each factor through the kernel. -/
theorem traverse_comp_listProd (η : Kernel α β) (μs : List (Measure α)) :
    η.traverse ∘ₘ listProd μs = listProd (μs.map (η ∘ₘ ·)) := by
  induction μs with
  | nil => simp [dirac_bind (Kernel.measurable _)]
  | cons μ μs ih =>
    rw [List.map_cons, listProd_cons, listProd_cons, ← ih, ← parallelComp_comp_prod,
      map_comp _ _ .of_discrete,
      bind_map Measurable.of_discrete.aemeasurable (Kernel.measurable _).aemeasurable]
    congr 1
    funext ⟨a, l⟩
    rw [Function.uncurry_apply_pair, Kernel.traverse_apply, List.map_cons, listProd_cons,
      ← Kernel.traverse_apply, Kernel.map_apply _ .of_discrete, Kernel.parallelComp_apply]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [Countable β] [MeasurableSingletonClass β] [Countable γ] [MeasurableSingletonClass γ]

theorem traverse_comp_traverse_apply (η : Kernel β γ) (κ : Kernel α β) (l : List α) :
    η.traverse ∘ₘ κ.traverse l = Measure.listProd (l.map fun a ↦ η ∘ₘ κ a) := by
  rw [traverse_apply, Measure.traverse_comp_listProd, List.map_map]
  rfl

/-- Traversing with a composition is traversing twice. -/
theorem traverse_comp_traverse (η : Kernel β γ) (κ : Kernel α β) :
    η.traverse ∘ₖ κ.traverse = (η ∘ₖ κ).traverse := by
  ext1 l
  rw [comp_apply, traverse_comp_traverse_apply, traverse_apply]
  exact congrArg _ (List.map_congr_left fun a _ ↦ (comp_apply η κ a).symm)

end ProbabilityTheory.Kernel
