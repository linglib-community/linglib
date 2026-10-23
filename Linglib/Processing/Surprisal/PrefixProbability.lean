/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.AutoregressiveSequenceModel.Basic

/-!
# Prefix probabilities of a generative process

A generative process is a probability measure on complete structures with string yields, and its
language model is the pushforward along the yield. The prefix probability of a string is the mass
of the structures whose yield extends it ([stolcke-1995]), its prefix probability under the
autoregressive model of the language model, and the probability of the next word is the process
conditioned on the prefix, at the structures consistent with the extended prefix. These are the
inputs of surprisal theory ([hale-2001], [levy-2008]).

## Main definitions

* `consistent`: the structures whose yield extends a prefix.

## Main results

* `condPrefixProb_ofMeasure_map`: the probability of continuing a prefix with a string is the
  ratio of the prefix probabilities after and before it.
* `next_ofMeasure_map_apply_some`: the probability of the next word is the process conditioned on
  the prefix, at the structures consistent with the extended prefix.

## References

* [stolcke-1995]
* [hale-2001]
* [levy-2008]
-/

@[expose] public section

namespace Surprisal

open MeasureTheory ProbabilityTheory AutoregressiveSequenceModel
open scoped ProbabilityTheory

variable {T W : Type*} (str : T → List W)

/-- The complete structures whose yield extends the prefix `ws`. -/
def consistent (ws : List W) : Set T := str ⁻¹' {l | ws <+: l}

@[simp] theorem consistent_nil : consistent str ([] : List W) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ List.nil_prefix

theorem consistent_anti {ws ws' : List W} (h : ws <+: ws') :
    consistent str ws' ⊆ consistent str ws :=
  fun _ ht ↦ h.trans ht

variable [MeasurableSpace T] [DiscreteMeasurableSpace T] (P : Measure T)

theorem map_apply_setOf_prefix (ws : List W) :
    P.map str {l | ws <+: l} = P (consistent str ws) :=
  Measure.map_apply .of_discrete .of_discrete

variable [MeasurableSpace W] [MeasurableSingletonClass W]

/-- After a prefix of positive probability, the autoregressive model of a process continues with
`xs` with the ratio of the masses of the structures consistent with the extended prefix and with
the prefix. -/
theorem condPrefixProb_ofMeasure_map [IsProbabilityMeasure P] {ws : List W}
    (hws : P (consistent str ws) ≠ 0) (xs : List W) :
    (ofMeasure (P.map str)).condPrefixProb ws xs =
      P (consistent str (ws ++ xs)) / P (consistent str ws) := by
  have hsub : {l : List W | ws ++ xs <+: l} ⊆ {l | ws <+: l} :=
    fun _ ↦ (List.prefix_append ws xs).trans
  rw [condPrefixProb_ofMeasure (by rwa [map_apply_setOf_prefix]),
    cond_apply_of_subset .of_discrete hsub, map_apply_setOf_prefix, map_apply_setOf_prefix]

/-- The probability of the next word `w` after the prefix `ws` is the process conditioned on the
prefix, at the structures consistent with the extended prefix. -/
theorem next_ofMeasure_map_apply_some (ws : List W) (w : W) :
    (ofMeasure (P.map str)).next ws {some w} =
      P[consistent str (ws ++ [w]) | consistent str ws] := by
  rw [next_ofMeasure_apply_some, cond_map .of_discrete .of_discrete,
    Measure.map_apply .of_discrete .of_discrete]
  rfl

end Surprisal
