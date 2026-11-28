/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Marginality.Constructions
public import Mathlib.Analysis.Real.Hyperreal

/-!
# Marginal scales on the hyperreals

The hyperreals carry two marginal scales. In [the first](##Hyperreal.infinitesimalScale) a
difference is marginal when it is infinitesimal, the analytic model of [dinis-jacinto-2025]; in
[the second](##Hyperreal.finiteScale) a difference is marginal when it is finite, the scale on
which the nonstandard accounts of the Sorites of [dean-2018] and [itzhaki-2021] place the number
of hairs or of grains. Both are the differences in a subgroup of archimedean classes.

## References

* [dinis-jacinto-2025]
* [dean-2018]
* [itzhaki-2021]
-/

@[expose] public section

namespace Hyperreal

open ArchimedeanClass MarginalScale

variable {x y : ℝ*}

/-- The hyperreals with infinitesimal differences marginal. -/
noncomputable def infinitesimalScale : MarginalScale ℝ* :=
  ofAddSubgroup (ballAddSubgroup 0) (ordConnected_ballAddSubgroup 0)

/-- The hyperreals with finite differences marginal. -/
noncomputable def finiteScale : MarginalScale ℝ* :=
  ofAddSubgroup (closedBallAddSubgroup 0) (ordConnected_closedBallAddSubgroup 0)

theorem isML_infinitesimalScale : infinitesimalScale.IsML :=
  isML_ofAddSubgroup
    (fun h ↦ epsilon_ne_zero <| AddSubgroup.mem_bot.1 <|
      h ▸ (mem_ballAddSubgroup_iff (by simp)).2 archimedeanClassMk_epsilon_pos)
    (fun h ↦ by
      have : (1 : ℝ*) ∈ ballAddSubgroup 0 := h ▸ AddSubgroup.mem_top _
      simp at this)

theorem isML_finiteScale : finiteScale.IsML :=
  isML_ofAddSubgroup
    (fun h ↦ one_ne_zero <| AddSubgroup.mem_bot.1 <|
      h ▸ mem_closedBallAddSubgroup_iff.2 (by simp))
    (fun h ↦ by
      have : ω ∈ closedBallAddSubgroup 0 := h ▸ AddSubgroup.mem_top _
      exact (mem_closedBallAddSubgroup_iff.1 this).not_gt archimedeanClassMk_omega_neg)

theorem infinitesimalScale_marginallyLT_iff :
    infinitesimalScale.MarginallyLT x y ↔ x < y ∧ 0 < mk (y - x) := by
  rw [infinitesimalScale, ofAddSubgroup_marginallyLT_iff, mem_ballAddSubgroup_iff (by simp)]

theorem infinitesimalScale_atMostMarginal_iff :
    infinitesimalScale.AtMostMarginal x y ↔ 0 < mk (y - x) := by
  rw [infinitesimalScale, ofAddSubgroup_atMostMarginal_iff, mem_ballAddSubgroup_iff (by simp)]

theorem finiteScale_marginallyLT_iff : finiteScale.MarginallyLT x y ↔ x < y ∧ 0 ≤ mk (y - x) := by
  rw [finiteScale, ofAddSubgroup_marginallyLT_iff, mem_closedBallAddSubgroup_iff]

theorem finiteScale_atMostMarginal_iff : finiteScale.AtMostMarginal x y ↔ 0 ≤ mk (y - x) := by
  rw [finiteScale, ofAddSubgroup_atMostMarginal_iff, mem_closedBallAddSubgroup_iff]

theorem finiteScale_largelyLT_iff : finiteScale.LargelyLT x y ↔ x < y ∧ mk (y - x) < 0 := by
  rw [LargelyLT, finiteScale_marginallyLT_iff]
  grind

end Hyperreal
