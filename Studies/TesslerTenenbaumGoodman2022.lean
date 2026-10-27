module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Pragmatics.RSA.Belief
public import Linglib.Semantics.Quantification.Basic

/-!
# Tessler, Tenenbaum and Goodman (2022): Logic, Probability, and Pragmatics in Syllogistic Reasoning

Tessler, Tenenbaum and Goodman model syllogistic reasoning as language use, in the Rational Speech
Act framework of Frank and Goodman. A state records which object types exist, the regions of a
three-circle Venn diagram. The reasoner first acts as a listener, updating a prior over states on
the two premises, then as a speaker choosing among nine conclusions for a naive listener who hears
the conclusion alone: the eight quantified sentences relating the end terms, and *nothing follows*,
which says nothing. Three speakers are compared. The literal speaker scores a conclusion by its
probability of being true; the state-communication speaker by the expected log-probability the
naive listener gives the reasoner's state; the belief-alignment speaker by the negative
Kullback–Leibler divergence of the naive listener's beliefs from the reasoner's. A figural
preference favors conclusions whose subject is the only end term in subject position in the
premises. The Bayesian data analysis and the comparison with the Probability Heuristics Model of
Chater and Oaksford are not formalized.

## Implementation notes

* Only *all* carries existential import (section 2.1). Table 1 prints the particular forms with
  an arrow under the existential quantifier, read here as a conjunction.
* Noise follows section 3.1.1: the listener disregards each sentence with probability `φ`, so a
  state pays a factor `φ` for every sentence false at it. The weights `1 - φ` and `φ` of
  section 2.2 give the same listeners at noise `φ / (1 - φ)`.
* The speakers are the printed equations without the figural preference, which `withFigure`
  adds by reweighting their conclusion probabilities. The paper's fitted state-communication
  model differs from belief alignment, so it is not the printed one.

## References

* [tessler-tenenbaum-goodman-2022]
* [frank-goodman-2012]
* [goodman-stuhlmuller-2013]
* [chater-oaksford-1999]
* [degen-etal-2020]
-/

@[expose] public section

namespace TesslerTenenbaumGoodman2022

open MeasureTheory ProbabilityTheory InformationTheory RSA Quantifier
open scoped ENNReal NNReal

/-! ### Sentences and states -/

/-- The terms of a syllogism are the end terms `A` and `C` and the middle term `B`. -/
inductive Term | A | B | C
  deriving DecidableEq, Fintype

/-- A region of the Venn diagram is an object type, the nonempty set of terms true of its
objects. -/
abbrev Region := {r : Finset Term // r.Nonempty}

/-- `region ts` is the region of the objects of which exactly the terms `ts` are true. -/
abbrev region (ts : Finset Term) (h : ts.Nonempty := by decide) : Region := ⟨ts, h⟩

/-- A state is the set of object types that exist. -/
abbrev State := Finset Region

/-- The Aristotelian quantifiers are *all*, *some*, *some … not* and *no*. -/
inductive Quant | all | some | someNot | no
  deriving DecidableEq, Fintype

/-- A categorical sentence relates a subject term to a predicate term by a quantifier. -/
structure Sentence where
  (quant : Quant) (subj pred : Term)
  deriving DecidableEq, Fintype

instance : MeasurableSpace Sentence := ⊤

/-- The quantifiers' meanings (Table 1) are *every* with a nonempty restrictor, *some*, its
inner negation, and *no*. -/
def Quant.denote : Quant → GQ Region
  | .all => fun R S ↦ GQ.every R S ∧ ∃ r, R r
  | .some => GQ.some
  | .someNot => GQ.innerNeg GQ.some
  | .no => GQ.no

/-- A sentence holds at a state when its quantifier relates the existing object types of the
subject term to the object types of the predicate term. -/
def Sentence.Holds (p : Sentence) (s : State) : Prop :=
  p.quant.denote (fun r ↦ r ∈ s ∧ p.subj ∈ r.1) fun r ↦ p.pred ∈ r.1

section Holds

variable {x y : Term} {s : State}

theorem holds_all :
    Sentence.Holds ⟨.all, x, y⟩ s ↔ (∀ r ∈ s, x ∈ r.1 → y ∈ r.1) ∧ ∃ r ∈ s, x ∈ r.1 := by
  simp [Sentence.Holds, Quant.denote, GQ.every]

theorem holds_some : Sentence.Holds ⟨.some, x, y⟩ s ↔ ∃ r ∈ s, x ∈ r.1 ∧ y ∈ r.1 := by
  simp [Sentence.Holds, Quant.denote, GQ.some, and_assoc]

theorem holds_someNot :
    Sentence.Holds ⟨.someNot, x, y⟩ s ↔ ∃ r ∈ s, x ∈ r.1 ∧ y ∉ r.1 := by
  simp [Sentence.Holds, Quant.denote, GQ.innerNeg, GQ.some, and_assoc]

theorem holds_no : Sentence.Holds ⟨.no, x, y⟩ s ↔ ∀ r ∈ s, x ∈ r.1 → y ∉ r.1 := by
  simp [Sentence.Holds, Quant.denote, GQ.no]

theorem holds_some_of_holds_all (h : Sentence.Holds ⟨.all, x, y⟩ s) :
    Sentence.Holds ⟨.some, x, y⟩ s :=
  GQ.subalternation_a_i _ _ h.2 h.1

end Holds

instance (p : Sentence) (s : State) : Decidable (p.Holds s) :=
  match p with
  | ⟨.all, _, _⟩ => decidable_of_iff _ holds_all.symm
  | ⟨.some, _, _⟩ => decidable_of_iff _ holds_some.symm
  | ⟨.someNot, _, _⟩ => decidable_of_iff _ holds_someNot.symm
  | ⟨.no, _, _⟩ => decidable_of_iff _ holds_no.symm

-- Table 1
theorem holds_table_one :
    Sentence.Holds ⟨.all, .A, .B⟩ {region {.A, .B}, region {.A, .B, .C}} ∧
      ¬ Sentence.Holds ⟨.all, .A, .B⟩ {region {.A}, region {.A, .B, .C}} ∧
      Sentence.Holds ⟨.some, .A, .B⟩ {region {.A}, region {.A, .B}} ∧
      ¬ Sentence.Holds ⟨.some, .A, .B⟩ {region {.A}, region {.A, .C}} ∧
      Sentence.Holds ⟨.someNot, .A, .B⟩ {region {.A}, region {.A, .B}} ∧
      ¬ Sentence.Holds ⟨.someNot, .A, .B⟩ {region {.A, .B}, region {.A, .B, .C}} ∧
      Sentence.Holds ⟨.no, .A, .B⟩ {region {.A}, region {.A, .C}} ∧
      ¬ Sentence.Holds ⟨.no, .A, .B⟩ {region {.A}, region {.A, .B}} := by
  decide

/-- The extension of a list of sentences is the set of states at which all of them hold. -/
def extension (us : List Sentence) : Set State := {s | ∀ p ∈ us, p.Holds s}

theorem mem_extension {us : List Sentence} {s : State} :
    s ∈ extension us ↔ ∀ p ∈ us, p.Holds s := Iff.rfl

@[simp] theorem extension_nil : extension [] = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h ↦ absurd h List.not_mem_nil

theorem mem_extension_singleton {p : Sentence} {s : State} : s ∈ extension [p] ↔ p.Holds s :=
  List.forall_mem_singleton

theorem mem_extension_pair {p q : Sentence} {s : State} :
    s ∈ extension [p, q] ↔ p.Holds s ∧ q.Holds s := by
  simp [mem_extension]

instance (us : List Sentence) (s : State) : Decidable (s ∈ extension us) :=
  inferInstanceAs (Decidable (∀ p ∈ us, p.Holds s))

/-! ### The listener (section 2.2) -/

/-- The noisy meaning of a list of sentences charges a state a factor `φ` for every sentence
false at it, since the listener disregards each sentence with probability `φ`. -/
noncomputable def noisy (φ : ℝ≥0∞) (us : List Sentence) (s : State) : ℝ≥0∞ :=
  φ ^ us.countP fun p ↦ ¬ p.Holds s

theorem noisy_zero (us : List Sentence) : noisy 0 us = (extension us).indicator 1 := by
  funext s
  by_cases h : s ∈ extension us
  · rw [Set.indicator_of_mem h, Pi.one_apply, noisy,
      List.countP_eq_zero.2 (by simpa [mem_extension] using h), pow_zero]
  · rw [Set.indicator_of_notMem h, noisy,
      zero_pow (mt List.countP_eq_zero.1 (by simpa [mem_extension] using h))]

variable {φ : ℝ≥0∞} {μ : Measure State}

/-- The literal listener reweights the prior by the noisy meaning of the sentences heard. -/
noncomputable def listener (φ : ℝ≥0∞) (μ : Measure State) : Kernel (List Sentence) State :=
  Kernel.ofDensity μ (noisy φ)

instance : IsFiniteKernel (listener φ μ) := inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

theorem listener_zero (μ : Measure State) :
    listener 0 μ = RSA.listener μ (truthful extension) := by
  rw [listener, listener_truthful_eq_ofDensity]
  exact congrArg _ (funext noisy_zero)

theorem lintegral_noisy_ne_top [IsFiniteMeasure μ] (hφ : φ ≠ ∞) (us : List Sentence) :
    ∫⁻ s, noisy φ us s ∂μ ≠ ∞ := by
  rw [lintegral_fintype]
  exact ENNReal.sum_ne_top.2 fun s _ ↦
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hφ) (measure_ne_top _ _)

theorem isProbabilityMeasure_listener [IsProbabilityMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (us : List Sentence) : IsProbabilityMeasure (listener φ μ us) := by
  refine Kernel.isProbabilityMeasure_ofDensity μ _ us (fun h ↦ ?_) (lintegral_noisy_ne_top hφ' us)
  rw [lintegral_eq_zero_iff (.of_discrete)] at h
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.1 (measure_mono_null
    (fun s _ ↦ show noisy φ us s ≠ 0 from pow_ne_zero _ hφ) h))

theorem listener_absolutelyContinuous [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (us us' : List Sentence) : listener φ μ us ≪ listener φ μ us' := by
  have : IsFiniteMeasure (μ.withDensity (noisy φ us')) :=
    isFiniteMeasure_withDensity (lintegral_noisy_ne_top hφ' us')
  have h : μ ≪ μ.withDensity (noisy φ us') :=
    withDensity_absolutelyContinuous' (.of_discrete) (.of_forall fun s ↦ pow_ne_zero _ hφ)
  exact (cond_absolutelyContinuous.trans (withDensity_absolutelyContinuous μ _)).trans
    (h.trans absolutelyContinuous_cond_univ)

/-! ### Syllogisms and conclusions (section 2.3.1) -/

/-- A syllogism is two premises; in the classical ones the first relates `A` and `B` and the
second `B` and `C`. -/
structure Syllogism where
  (first second : Sentence)
  deriving DecidableEq, Fintype

instance : MeasurableSpace Syllogism := ⊤

/-- The reasoner hears the two premises of a syllogism in order. -/
def Syllogism.premises (syl : Syllogism) : List Sentence := [syl.first, syl.second]

/-- The subjects of a syllogism are the terms in subject position in its premises. -/
def Syllogism.subjects (syl : Syllogism) : Finset Term := {syl.first.subj, syl.second.subj}

/-- A sentence is a candidate conclusion when it relates the two end terms. -/
def Sentence.IsConclusion (p : Sentence) : Prop := p.subj ≠ .B ∧ p.pred ≠ .B ∧ p.subj ≠ p.pred

instance : DecidablePred Sentence.IsConclusion := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A conclusion is a sentence relating the end terms or, as `none`, *nothing follows*. -/
abbrev Conclusion := Option {p : Sentence // p.IsConclusion}

/-- A conclusion says its sentence, or nothing at all. -/
def Conclusion.said : Conclusion → List Sentence
  | none => []
  | some p => [p.1]

/-- `ac q` is the conclusion relating `A` to `C` by the quantifier `q`. -/
abbrev ac (q : Quant) : Conclusion := some ⟨⟨q, .A, .C⟩, by simp [Sentence.IsConclusion]⟩

theorem extension_said_none : extension (Conclusion.said none) = Set.univ := extension_nil

/-! ### The speakers (section 2.3) -/

section Model

variable (φ : ℝ≥0∞) (μ : Measure State) (α : ℝ)

/-- The reasoner's beliefs are the listener's posterior after the premises. -/
noncomputable abbrev reasoner (syl : Syllogism) : Measure State := listener φ μ syl.premises

/-- The naive listener's beliefs are the listener's posterior after a conclusion. -/
noncomputable abbrev naive (c : Conclusion) : Measure State := listener φ μ c.said

/-- The literal speaker scores a conclusion by the reasoner's probability that it is true. -/
noncomputable def literalSpeaker : Kernel Syllogism Conclusion :=
  Kernel.softmax fun syl c ↦ ((α * (reasoner φ μ syl).real (extension c.said) : ℝ) : EReal)

/-- The state-communication speaker scores a conclusion by the expected log-probability the
naive listener gives the reasoner's state. -/
noncomputable def stateCommunication : Kernel Syllogism Conclusion :=
  Kernel.softmax fun syl c ↦
    ((α * ∑ s, (reasoner φ μ syl).real {s} * Real.log ((naive φ μ c).real {s}) : ℝ) : EReal)

/-- The belief-alignment speaker believes what the reasoner believes and addresses the naive
listener. -/
noncomputable def beliefAlignment : Kernel Syllogism Conclusion :=
  speaker α 0 (naive φ μ) (reasoner φ μ)

instance : IsFiniteKernel (beliefAlignment φ μ α) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

variable {φ μ α}

theorem beliefAlignment_eq_softmax_klDiv [IsProbabilityMeasure μ] (hα : 0 < α) (hφ : φ ≠ 0)
    (hφ' : φ ≠ ∞) :
    beliefAlignment φ μ α = Kernel.softmax fun syl c ↦
      -((ENNReal.ofReal α * klDiv (reasoner φ μ syl) (naive φ μ c) : ℝ≥0∞) : EReal) := by
  have (us : List Sentence) := isProbabilityMeasure_listener (μ := μ) hφ hφ' us
  rw [beliefAlignment, speaker_eq_softmax_klDiv hα]
  simp

/-- As printed, the state-communication and belief-alignment speakers are one speaker. -/
theorem stateCommunication_eq_beliefAlignment [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞) :
    stateCommunication φ μ α = beliefAlignment φ μ α := by
  rw [beliefAlignment, speaker_eq_softmax_sum_log fun _ _ ↦
    listener_absolutelyContinuous hφ hφ' _ _]
  simp [stateCommunication]

/-- The literal speaker never prefers a quantified conclusion to *nothing follows*, which is
true at every state. -/
theorem literalSpeaker_le_nothing_follows (hα : 0 ≤ α) (syl : Syllogism) (c : Conclusion) :
    (literalSpeaker φ μ α syl).real {c} ≤ (literalSpeaker φ μ α syl).real {none} := by
  refine not_lt.1 fun h ↦ ?_
  rw [literalSpeaker, Kernel.softmax_coe_real_singleton_lt_iff] at h
  exact h.not_ge (mul_le_mul_of_nonneg_left
    (measureReal_mono (extension_said_none ▸ Set.subset_univ _) (measure_ne_top _ _)) hα)

/-! ### The figural preference (section 3.1.1) -/

/-- The figural preference gives weight `β` to a conclusion whose subject, but not its predicate,
is the subject of a premise, and weight `1` to every other conclusion. -/
def figuralWeight (β : ℝ≥0) (syl : Syllogism) : Conclusion → ℝ≥0
  | none => 1
  | some p => if p.1.subj ∈ syl.subjects ∧ p.1.pred ∉ syl.subjects then β else 1

/-- The figural preference reweights a speaker's conclusion probabilities and renormalizes
them. -/
noncomputable def withFigure (β : ℝ≥0) (S : Kernel Syllogism Conclusion) :
    Kernel Syllogism Conclusion :=
  Kernel.ofWeights fun syl c ↦ figuralWeight β syl c * S syl {c}

variable {β : ℝ≥0} {S : Kernel Syllogism Conclusion} [IsFiniteKernel S] {syl : Syllogism}
  {c c' : Conclusion}

private theorem weight_ne_top (β : ℝ≥0) (S : Kernel Syllogism Conclusion) [IsFiniteKernel S]
    (syl : Syllogism) (c : Conclusion) : figuralWeight β syl c * S syl {c} ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)

theorem withFigure_apply_none_eq_one (h0 : S syl {none} ≠ 0) (h : ∀ c ≠ none, S syl {c} = 0) :
    withFigure β S syl {none} = 1 := by
  rw [withFigure, Kernel.ofWeights_apply_singleton, Finset.sum_eq_single none
    (fun c _ hc ↦ by rw [h c hc, mul_zero]) fun hn ↦ absurd (Finset.mem_univ _) hn]
  exact ENNReal.div_self (by simpa [figuralWeight] using h0) (weight_ne_top β S syl none)

theorem withFigure_real_singleton_lt_iff (h0 : S syl {none} ≠ 0) :
    (withFigure β S syl).real {c} < (withFigure β S syl).real {c'} ↔
      figuralWeight β syl c * (S syl).real {c} < figuralWeight β syl c' * (S syl).real {c'} := by
  rw [withFigure, Kernel.ofWeights_real_singleton_lt_iff syl
    (fun h ↦ h0 (by simpa [figuralWeight] using Finset.sum_eq_zero_iff.1 h none (by simp)))
    (ENNReal.sum_ne_top.2 fun c _ ↦ weight_ne_top β S syl c),
    ← ENNReal.toReal_lt_toReal (weight_ne_top β S syl c) (weight_ne_top β S syl c'),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal,
    measureReal_def, measureReal_def]

end Model

/-! ### Without noise (section 2.3.4) -/

section Noiseless

variable {μ : Measure State} {α : ℝ} {β : ℝ≥0} {syl : Syllogism} {c c' : Conclusion}

theorem beliefAlignment_zero (μ : Measure State) (α : ℝ) :
    beliefAlignment 0 μ α =
      speaker α 0 (RSA.listener μ (truthful fun c ↦ extension (Conclusion.said c)))
        fun syl ↦ μ[|extension syl.premises] := by
  unfold beliefAlignment reasoner naive
  rw [listener_zero]
  congr 1
  · funext c
    exact (RSA.listener_truthful_apply μ _ _).trans
      (RSA.listener_truthful_apply μ (fun c ↦ extension (Conclusion.said c)) c).symm
  · funext syl
    exact RSA.listener_truthful_apply μ _ _

private theorem ae_le_iff_subset (hμ : ∀ s, μ {s} ≠ 0) {A B : Set State} :
    A ≤ᵐ[μ] B ↔ A ⊆ B :=
  ae_iff_of_countable.trans ⟨fun h s hs ↦ h s (hμ s) hs, fun h _ _ hs ↦ h hs⟩

variable [IsFiniteMeasure μ]

private theorem measure_lt_of_notMem (hμ : ∀ s, μ {s} ≠ 0) {A B : Set State} (hAB : A ⊆ B)
    {s : State} (hB : s ∈ B) (hA : s ∉ A) : μ A < μ B :=
  calc μ A < μ A + μ {s} := ENNReal.lt_add_right (measure_ne_top _ _) (hμ s)
    _ = μ (A ∪ {s}) := (measure_union (Set.disjoint_singleton_right.2 hA) (.singleton s)).symm
    _ ≤ μ B := measure_mono (Set.union_subset hAB (Set.singleton_subset_iff.2 hB))

theorem beliefAlignment_zero_apply_singleton_eq_zero_iff (hμ : ∀ s, μ {s} ≠ 0) (hα : 0 < α) :
    beliefAlignment 0 μ α syl {c} = 0 ↔
      ¬ extension syl.premises ⊆ extension (Conclusion.said c) := by
  rw [beliefAlignment_zero, speaker_cond_listener_truthful_apply_singleton_eq_zero_iff hα,
    ae_le_iff_subset hμ]

theorem beliefAlignment_zero_real_singleton_lt_iff (hμ : ∀ s, μ {s} ≠ 0) (hα : 0 < α)
    (hne : (extension syl.premises).Nonempty)
    (hc : extension syl.premises ⊆ extension (Conclusion.said c))
    (hc' : extension syl.premises ⊆ extension (Conclusion.said c')) :
    (beliefAlignment 0 μ α syl).real {c} < (beliefAlignment 0 μ α syl).real {c'} ↔
      μ (extension (Conclusion.said c')) < μ (extension (Conclusion.said c)) := by
  rw [beliefAlignment_zero]
  exact speaker_zero_cond_listener_truthful_real_singleton_lt_iff hα
    (fun h ↦ let ⟨s, hs⟩ := hne; hμ s (measure_mono_null (Set.singleton_subset_iff.2 hs) h))
    ((ae_le_iff_subset hμ).2 hc) ((ae_le_iff_subset hμ).2 hc')

/-- Without noise the belief-alignment speaker answers *nothing follows* to every syllogism that
entails no quantified conclusion (section 2.3.4). -/
theorem nothing_follows_of_invalid (hμ : ∀ s, μ {s} ≠ 0) (hα : 0 < α)
    (h : ∀ c ≠ none, ¬ extension syl.premises ⊆ extension (Conclusion.said c)) :
    withFigure β (beliefAlignment 0 μ α) syl {none} = 1 :=
  withFigure_apply_none_eq_one
    ((beliefAlignment_zero_apply_singleton_eq_zero_iff hμ hα).not_left.2
      (extension_said_none ▸ Set.subset_univ _))
    fun c hc ↦ (beliefAlignment_zero_apply_singleton_eq_zero_iff hμ hα).2 (h c hc)

/-! ### *All A are B, All B are C* and *All A are B, All C are B* (Figures 3, 4 and 8) -/

/-- Barbara is the syllogism *All A are B, All B are C*. -/
def barbara : Syllogism := ⟨⟨.all, .A, .B⟩, ⟨.all, .B, .C⟩⟩

/-- The syllogism *All A are B, All C are B* has both end terms in subject position. -/
def allAB_allCB : Syllogism := ⟨⟨.all, .A, .B⟩, ⟨.all, .C, .B⟩⟩

theorem figuralWeight_barbara (q : Quant) : figuralWeight β barbara (ac q) = β := by
  simp [figuralWeight, Syllogism.subjects, barbara]

theorem figuralWeight_allAB_allCB (c : Conclusion) : figuralWeight β allAB_allCB c = 1 := by
  obtain _ | ⟨⟨q, x, y⟩, h⟩ := c
  · rfl
  · have hy : y ≠ .B := h.2.1
    cases y <;> simp_all [figuralWeight, Syllogism.subjects, allAB_allCB]

theorem barbara_entails_all : extension barbara.premises ⊆ extension (ac .all).said :=
  fun _ hs ↦
    have ⟨h₁, h₂⟩ := (mem_extension_pair.1 hs).imp holds_all.1 holds_all.1
    mem_extension_singleton.2 (holds_all.2 ⟨fun r hr hA ↦ h₂.1 r hr (h₁.1 r hr hA), h₁.2⟩)

/-- For *All A are B, All B are C*, the belief-alignment speaker prefers *All A are C* to *Some A
are C* and *nothing follows* (Figure 8). -/
theorem barbara_prefers_all (hμ : ∀ s, μ {s} ≠ 0) (hα : 0 < α) (hβ : 1 ≤ β) :
    (withFigure β (beliefAlignment 0 μ α) barbara).real {ac .some} <
        (withFigure β (beliefAlignment 0 μ α) barbara).real {ac .all} ∧
      (withFigure β (beliefAlignment 0 μ α) barbara).real {none} <
        (withFigure β (beliefAlignment 0 μ α) barbara).real {ac .all} := by
  have hne : (extension barbara.premises).Nonempty := ⟨{region {.A, .B, .C}}, by decide⟩
  have hsome : extension (ac .all).said ⊆ extension (ac .some).said := fun _ hs ↦
    mem_extension_singleton.2 (holds_some_of_holds_all (mem_extension_singleton.1 hs))
  have hlt : ∀ {c : Conclusion}, extension (ac .all).said ⊆ extension (Conclusion.said c) →
      ({region {.A}, region {.A, .C}} : State) ∈ extension (Conclusion.said c) →
      (beliefAlignment 0 μ α barbara).real {c} <
        (beliefAlignment 0 μ α barbara).real {ac .all} := fun hc hs ↦
    (beliefAlignment_zero_real_singleton_lt_iff hμ hα hne (barbara_entails_all.trans hc)
      barbara_entails_all).2 (measure_lt_of_notMem hμ hc hs (by decide))
  have h0 : beliefAlignment 0 μ α barbara {none} ≠ 0 :=
    (beliefAlignment_zero_apply_singleton_eq_zero_iff hμ hα).not_left.2
      (extension_said_none ▸ Set.subset_univ _)
  rw [withFigure_real_singleton_lt_iff h0, withFigure_real_singleton_lt_iff h0,
    figuralWeight_barbara, figuralWeight_barbara]
  have hβ' : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have h1 := hlt hsome (by decide)
  have h2 := hlt (c := none) (extension_said_none ▸ Set.subset_univ _)
    (extension_said_none ▸ Set.mem_univ _)
  exact ⟨mul_lt_mul_of_pos_left h1 (by linarith), by
    simpa [figuralWeight] using h2.trans_le (le_mul_of_one_le_left measureReal_nonneg hβ')⟩

theorem allAB_allCB_nothing_follows (hμ : ∀ s, μ {s} ≠ 0) (hα : 0 < α) :
    withFigure β (beliefAlignment 0 μ α) allAB_allCB {none} = 1 := by
  refine nothing_follows_of_invalid hμ hα fun c hc h ↦ ?_
  obtain _ | ⟨⟨q, x, y⟩, hx, hy, hxy⟩ := c
  · exact hc rfl
  · have h₁ : Sentence.Holds ⟨q, x, y⟩ {region {.A, .B}, region {.B, .C}} :=
      mem_extension_singleton.1 (h (by decide))
    have h₂ : Sentence.Holds ⟨q, x, y⟩ {region {.A, .B, .C}} :=
      mem_extension_singleton.1 (h (by decide))
    clear h hc
    revert hx hy hxy h₁ h₂
    cases q <;> cases x <;> cases y <;> decide

end Noiseless

end TesslerTenenbaumGoodman2022
