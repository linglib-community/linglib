/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Order.UpperLower.Closure

/-!
# Carcassi, Steinert-Threlkeld and Szymanik (2021): Monotone Quantifiers Emerge

[carcassi-steinert-threlkeld-szymanik-2021] grade the upward monotonicity of a quantifier by the
uncertainty coefficient ([theil-1970]) of its truth value given whether some substructure
verifies it, and its downward monotonicity given whether some superstructure does. A structure
records which members of a fixed restrictor lie in the scope, so structures are sets ordered by
inclusion and a quantifier is a property of them. A quantifier that is neither trivially true nor
trivially false has upward degree [`1` exactly when it is upward monotone](##mon_eq_one_iff) and
downward degree [`1` exactly when it is downward monotone](##monDown_eq_one_iff).

## Implementation notes

* The degrees are defined for a property of the points of any preorder, so that the models of a
  determiner, ordered by their scopes, are a second instance. The paper's probability is uniform;
  the characterizations assume only that every point has positive probability.
* The upward degree depends only on the probabilities of the quantifier and of its upward closure
  (`mon_eq`). It is `0` exactly for the quantifiers true of the empty scope (`mon_eq_zero_iff`),
  and the downward degree is `0` exactly for those true of the full scope, so a downward monotone
  quantifier has upward degree `0`. A quantifier with constant truth value has both degrees `0`.
* The degrees the paper reports for example quantifiers are those of a learner: the largest
  upward degree among the four quantifiers obtained by reading the learner's input and output bits
  either way, on a restrictor of ten. That maximum, the paper's degree of quantity and its
  iterated-learning simulations are not formalized.

## References

* [carcassi-steinert-threlkeld-szymanik-2021]
* [theil-1970]
-/

@[expose] public section

namespace CarcassiSteinertThrelkeldSzymanik2021

open MeasureTheory ProbabilityTheory InformationTheory Real

/-! ### The degrees of a property of the points of a preorder -/

section preorder

variable {Ω : Type*} [Preorder Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Prop}

/-- The degree of upward monotonicity: the share of the uncertainty about a property at a point
that is removed by knowing whether it holds at some smaller point. -/
noncomputable def mon (X : Ω → Prop) (μ : Measure Ω) : ℝ :=
  uncertaintyCoeff X (· ∈ upperClosure {ω | X ω}) μ

/-- The degree of downward monotonicity: the share of the uncertainty about a property at a point
that is removed by knowing whether it holds at some larger point. -/
noncomputable def monDown (X : Ω → Prop) (μ : Measure Ω) : ℝ :=
  uncertaintyCoeff X (· ∈ lowerClosure {ω | X ω}) μ

omit [Preorder Ω] in
private theorem entropy_ne_zero (hμ : ∀ ω, μ {ω} ≠ 0) (h₁ : ∃ ω, X ω) (h₀ : ∃ ω, ¬ X ω) :
    H[X ; μ] ≠ 0 :=
  let ⟨_, ha⟩ := h₁; let ⟨_, hb⟩ := h₀
  entropy_ne_zero_of_ne hμ .of_discrete fun h ↦ hb (h ▸ ha)

theorem condEntropy_mem_upperClosure_eq_zero_iff (hμ : ∀ ω, μ {ω} ≠ 0) :
    H[X | (· ∈ upperClosure {ω | X ω}) ; μ] = 0 ↔ Monotone X := by
  refine (condEntropy_mem_mem_eq_zero_iff_of_subset (s := {ω | X ω})
    (t := ↑(upperClosure {ω | X ω})) hμ .of_discrete .of_discrete subset_upperClosure).trans ?_
  rw [← isUpperSet_setOfPred]
  refine ⟨?_, fun h ↦ .inr h.upperClosure.symm⟩
  rintro (h | h)
  · exact h ▸ isUpperSet_empty
  · exact h ▸ (upperClosure _).upper

theorem condEntropy_mem_lowerClosure_eq_zero_iff (hμ : ∀ ω, μ {ω} ≠ 0) :
    H[X | (· ∈ lowerClosure {ω | X ω}) ; μ] = 0 ↔ Antitone X := by
  refine (condEntropy_mem_mem_eq_zero_iff_of_subset (s := {ω | X ω})
    (t := ↑(lowerClosure {ω | X ω})) hμ .of_discrete .of_discrete subset_lowerClosure).trans ?_
  rw [← isLowerSet_setOfPred]
  refine ⟨?_, fun h ↦ .inr h.lowerClosure.symm⟩
  rintro (h | h)
  · exact h ▸ isLowerSet_empty
  · exact h ▸ (lowerClosure _).lower

/-- A property that holds somewhere and fails somewhere has upward degree `1` exactly when it is
upward monotone. -/
theorem mon_eq_one_iff (hμ : ∀ ω, μ {ω} ≠ 0) (h₁ : ∃ ω, X ω) (h₀ : ∃ ω, ¬ X ω) :
    mon X μ = 1 ↔ Monotone X := by
  rw [mon, uncertaintyCoeff_eq_one_iff μ .of_discrete .of_discrete (entropy_ne_zero hμ h₁ h₀),
    condEntropy_mem_upperClosure_eq_zero_iff hμ]

/-- A property that holds somewhere and fails somewhere has downward degree `1` exactly when it
is downward monotone. -/
theorem monDown_eq_one_iff (hμ : ∀ ω, μ {ω} ≠ 0) (h₁ : ∃ ω, X ω) (h₀ : ∃ ω, ¬ X ω) :
    monDown X μ = 1 ↔ Antitone X := by
  rw [monDown, uncertaintyCoeff_eq_one_iff μ .of_discrete .of_discrete
    (entropy_ne_zero hμ h₁ h₀), condEntropy_mem_lowerClosure_eq_zero_iff hμ]

theorem mon_eq (hX : H[X ; μ] ≠ 0) :
    mon X μ = 1 - μ.real ↑(upperClosure {ω | X ω}) *
      binEntropy (μ.real {ω | X ω} / μ.real ↑(upperClosure {ω | X ω})) /
        binEntropy (μ.real {ω | X ω}) := by
  rw [mon, uncertaintyCoeff_eq_one_sub μ .of_discrete .of_discrete hX]
  congr 2
  · exact condEntropy_mem_mem_of_subset (s := {ω | X ω}) .of_discrete .of_discrete
      subset_upperClosure
  · exact entropy_mem (s := {ω | X ω}) .of_discrete

-- A property inside an event has coefficient `0` given the event exactly when the event is certain.
omit [Preorder Ω] in
private theorem uncertaintyCoeff_mem_eq_zero_iff (hμ : ∀ ω, μ {ω} ≠ 0) (h₁ : ∃ ω, X ω)
    (h₀ : ∃ ω, ¬ X ω) {t : Set Ω} (ht : {ω | X ω} ⊆ t) :
    uncertaintyCoeff X (· ∈ t) μ = 0 ↔ t = Set.univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [uncertaintyCoeff_eq_zero_iff μ .of_discrete .of_discrete (entropy_ne_zero hμ h₁ h₀)] at h
    have key := h.measure_inter_preimage_eq_mul {True} {True} (.singleton _) (.singleton _)
    rw [Set.preimage_singleton_true, Set.preimage_singleton_true] at key
    change μ ({ω | X ω} ∩ t) = μ {ω | X ω} * μ t at key
    rw [Set.inter_eq_left.2 ht] at key
    obtain ⟨a, ha⟩ := h₁
    have hs : μ {ω | X ω} ≠ 0 := fun h0 ↦
      hμ a (measure_mono_null (Set.singleton_subset_iff.2 ha) h0)
    have h1 : μ t = 1 := (ENNReal.mul_right_inj hs (measure_ne_top μ _)).1 (by rw [← key, mul_one])
    refine Set.eq_univ_of_forall fun ω ↦ by_contra fun hω ↦ ?_
    exact hμ ω (measure_mono_null (Set.singleton_subset_iff.2 hω)
      ((prob_compl_eq_zero_iff .of_discrete).2 h1))
  · rw [show (· ∈ t) = fun _ : Ω ↦ True from funext fun ω ↦ eq_true (h ▸ Set.mem_univ ω),
      uncertaintyCoeff_const μ .of_discrete]

end preorder

section partialOrder

variable {Ω : Type*} [PartialOrder Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Prop}

theorem mon_eq_zero_iff [OrderBot Ω] (hμ : ∀ ω, μ {ω} ≠ 0) (h₁ : ∃ ω, X ω) (h₀ : ∃ ω, ¬ X ω) :
    mon X μ = 0 ↔ X ⊥ := by
  refine (uncertaintyCoeff_mem_eq_zero_iff (t := ↑(upperClosure {ω | X ω})) hμ h₁ h₀
    subset_upperClosure).trans ⟨fun h ↦ ?_, fun h ↦ Set.eq_univ_of_forall fun ω ↦ ⟨⊥, h, bot_le⟩⟩
  obtain ⟨ω, hω, hle⟩ := h.ge (Set.mem_univ ⊥)
  exact le_bot_iff.1 hle ▸ hω

theorem monDown_eq_zero_iff [OrderTop Ω] (hμ : ∀ ω, μ {ω} ≠ 0) (h₁ : ∃ ω, X ω)
    (h₀ : ∃ ω, ¬ X ω) : monDown X μ = 0 ↔ X ⊤ := by
  refine (uncertaintyCoeff_mem_eq_zero_iff (t := ↑(lowerClosure {ω | X ω})) hμ h₁ h₀
    subset_lowerClosure).trans ⟨fun h ↦ ?_, fun h ↦ Set.eq_univ_of_forall fun ω ↦ ⟨⊤, h, le_top⟩⟩
  obtain ⟨ω, hω, hle⟩ := h.ge (Set.mem_univ ⊤)
  exact top_le_iff.1 hle ▸ hω

end partialOrder

/-! ### Counting quantifiers over a fixed restrictor -/

section examples

open Quantifier.Det

/-- *At least two* of three has upward degree `1`. -/
example {μ : Measure (Set (Fin 3))} [IsProbabilityMeasure μ] (hμ : ∀ B, μ {B} ≠ 0) :
    mon (atLeast 2 Set.univ : Quantifier (Fin 3)) μ = 1 :=
  (mon_eq_one_iff hμ ⟨Set.univ, by decide⟩ ⟨∅, by decide⟩).2 (scopeMonotone_atLeast 2 _)

/-- *Exactly one* of two falls short of upward degree `1`: one individual verifies it and both do
not. -/
example {μ : Measure (Set (Fin 2))} [IsProbabilityMeasure μ] (hμ : ∀ B, μ {B} ≠ 0) :
    mon (exactly 1 Set.univ : Quantifier (Fin 2)) μ ≠ 1 := fun h ↦
  absurd ((mon_eq_one_iff hμ ⟨{0}, by decide⟩ ⟨∅, by decide⟩).1 h (Set.subset_univ {0})
    (by decide)) (by decide)

/-- *At most one* of three has downward degree `1` and upward degree `0`. -/
example {μ : Measure (Set (Fin 3))} [IsProbabilityMeasure μ] (hμ : ∀ B, μ {B} ≠ 0) :
    monDown (atMost 1 Set.univ : Quantifier (Fin 3)) μ = 1 ∧
      mon (atMost 1 Set.univ : Quantifier (Fin 3)) μ = 0 :=
  ⟨(monDown_eq_one_iff hμ ⟨∅, by decide⟩ ⟨Set.univ, by decide⟩).2 (scopeAntitone_atMost 1 _),
    (mon_eq_zero_iff hμ ⟨∅, by decide⟩ ⟨Set.univ, by decide⟩).2
      (show atMost 1 Set.univ (∅ : Set (Fin 3)) by decide)⟩

end examples

end CarcassiSteinertThrelkeldSzymanik2021
