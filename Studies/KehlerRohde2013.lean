module

public import Linglib.Core.Probability.Kernel.OfDensity
public import Linglib.Data.Experiments.KehlerRohde2013
public import Linglib.Discourse.Accessibility
public import Linglib.Discourse.Centering.Basic
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Discourse.Coherence
public import Linglib.Fragments.English.Pronouns
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Kehler and Rohde (2013): A Probabilistic Reconciliation of Coherence-Driven and Centering-Driven Theories of Pronoun Interpretation

This file models pronoun interpretation as Bayes' rule over one joint measure
$\mu \otimes (\eta \times \sigma)$ on referent, coherence relation and form of reference, built
from a next-mention prior $\mu$, a relation kernel $\eta$ and a production kernel $\sigma$, so that
relation and form are independent given the referent. [Its production marginal does not depend on
$\eta$](##map_production_compProd_prod); [conditioned on a pronoun](##map_cond_compProd_prod), its
referent marginal is the interpretation and its relation marginal the bidirectional dependency
between relation and referent. The paper's passage-completion data rule out three model classes:
[the inert pronoun of a Hobbsian analysis](##not_inert), [an interpretation heuristic blind to the
relation](##not_heuristic), and [a pronominalization rate fixed by Centering
status](##not_cbFactored).

## Implementation notes

* The referents are the Source and the Goal of the transfer contexts and of Arnold's data, the
  Source being the subject, and the two positions of the voice manipulation.
* A pronoun prompt conditions the joint on the form; a no-pronoun prompt does not.
* Priors and production rates enter in percent. Relation frequencies are finite measures of the
  printed mass, which need not sum to one; the refutations read single cells.
* Arnold's printed rates are rounded, and [their posterior is .618](##arnold_prediction); his
  counts, 19 of 25 Source subjects and 30 of 149 Goal objects pronominalized, give the paper's
  .86, .28 and .61.
* The paper's predictions for the voice manipulation were estimated per participant and item, so
  they [exceed the posterior of the aggregate rates](##bayesSubject_lt_predicted).
* `FocusesEndState` holding of Occasion and Result reads "such as Occasion and Result".

## References

* [kehler-rohde-2013]
* [kehler-kertz-rohde-elman-2008]
* [kehler-2002]
* [hobbs-1979]
* [grosz-joshi-weinstein-1995]
* [arnold-2001]
* [rohde-kehler-2014]
* [davison-1984]
-/

@[expose] public section

namespace KehlerRohde2013

open MeasureTheory ProbabilityTheory Discourse.Centering
open scoped ENNReal
open Discourse.AccessibilityLevel (Head)
open Morphology (Word Features)

/-! ### The model -/

section Model

variable {R C F : Type*} [MeasurableSpace R] [MeasurableSpace C] [MeasurableSpace F]
  [Fintype R] [Fintype C] [Fintype F] [DiscreteMeasurableSpace R] [DiscreteMeasurableSpace C]
  [DiscreteMeasurableSpace F]
  (μ : Measure R) (η : Kernel R C) [IsMarkovKernel η] (σ : Kernel R F)

omit [DiscreteMeasurableSpace C] in
theorem compProd_prod_apply_form (u : F) :
    (μ ⊗ₘ (η ×ₖ σ)) {x | x.2.2 = u} = ∫⁻ r, σ r {u} ∂μ := by
  rw [show {x : R × C × F | x.2.2 = u} = Set.univ ×ˢ (Set.univ ×ˢ {u}) by ext; simp,
    Measure.compProd_apply_prod .univ (MeasurableSet.univ.prod (.singleton u)),
    Measure.restrict_univ]
  simp [Kernel.prod_apply_prod]

/-- Conditioned on the form, the (referent, relation) marginal is the posterior over referents
composed with the relation kernel. -/
theorem map_cond_compProd_prod (u : F) :
    ((μ ⊗ₘ (η ×ₖ σ))[|{x | x.2.2 = u}]).map (fun x ↦ (x.1, x.2.1)) =
      Kernel.ofDensity μ (fun u r ↦ σ r {u}) u ⊗ₘ η := by
  have hm : Measurable fun x : R × C × F ↦ (x.1, x.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  refine Measure.ext_of_singleton fun ⟨r, c⟩ ↦ ?_
  have hset : {x : R × C × F | x.2.2 = u} ∩ (fun x ↦ (x.1, x.2.1)) ⁻¹' {(r, c)} =
      {(r, (c, u))} := by
    ext ⟨r', c', f'⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq]
    tauto
  have hs : MeasurableSet {x : R × C × F | x.2.2 = u} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton u)
  rw [Measure.map_apply hm (.singleton _), cond_apply hs, hset,
    Measure.compProd_apply_singleton, Measure.compProd_apply_singleton,
    ← Set.singleton_prod_singleton, Kernel.prod_apply_prod, compProd_prod_apply_form,
    Kernel.ofDensity_apply_singleton', div_eq_mul_inv]
  ring

omit [DiscreteMeasurableSpace C] in
/-- The (referent, form) marginal is `μ ⊗ₘ σ` whatever the relation kernel, so the choice of a
pronoun is blind to coherence (p. 18). -/
theorem map_production_compProd_prod :
    (μ ⊗ₘ (η ×ₖ σ)).map (fun x ↦ (x.1, x.2.2)) = μ ⊗ₘ σ := by
  have hm : Measurable fun x : R × C × F ↦ (x.1, x.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  refine Measure.ext_of_singleton fun ⟨r, f⟩ ↦ ?_
  rw [Measure.map_apply hm (.singleton _),
    show (fun x : R × C × F ↦ (x.1, x.2.2)) ⁻¹' {(r, f)} = {r} ×ˢ (Set.univ ×ˢ {f}) by
      ext; simp,
    Measure.compProd_apply_prod (.singleton r) (MeasurableSet.univ.prod (.singleton f)),
    lintegral_singleton, Kernel.prod_apply_prod, measure_univ, one_mul,
    Measure.compProd_apply_singleton, mul_comm]

theorem fst_cond_compProd_prod (u : F) :
    ((μ ⊗ₘ (η ×ₖ σ))[|{x | x.2.2 = u}]).fst = Kernel.ofDensity μ (fun u r ↦ σ r {u}) u := by
  have hm : Measurable fun x : R × C × F ↦ (x.1, x.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  rw [← Measure.fst_compProd (Kernel.ofDensity μ (fun u r ↦ σ r {u}) u) η,
    ← map_cond_compProd_prod, Measure.fst, Measure.fst, Measure.map_map measurable_fst hm]
  rfl

omit [Fintype F] [DiscreteMeasurableSpace C] [DiscreteMeasurableSpace F] [IsMarkovKernel η] in
theorem map_relation_compProd_prod [IsMarkovKernel σ] :
    (μ ⊗ₘ (η ×ₖ σ)).map (fun x ↦ x.2.1) = η ∘ₘ μ := by
  rw [show (fun x : R × C × F ↦ x.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd, ← Measure.snd, Measure.snd_compProd,
    Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]

theorem map_relation_cond_compProd_prod (u : F) :
    ((μ ⊗ₘ (η ×ₖ σ))[|{x | x.2.2 = u}]).map (fun x ↦ x.2.1) =
      η ∘ₘ Kernel.ofDensity μ (fun u r ↦ σ r {u}) u := by
  have hm : Measurable fun x : R × C × F ↦ (x.1, x.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  rw [← Measure.snd_compProd, ← map_cond_compProd_prod, Measure.snd,
    Measure.map_map measurable_snd hm]
  rfl

omit [Fintype C] [DiscreteMeasurableSpace C] in
theorem ofDensity_eq_posterior_comp [Nonempty R] (u : F) :
    Kernel.ofDensity μ (fun u r ↦ σ r {u}) u =
      η†(Kernel.ofDensity μ (fun u r ↦ σ r {u}) u) ∘ₘ
        (η ∘ₘ Kernel.ofDensity μ (fun u r ↦ σ r {u}) u) :=
  posterior_comp_self.symm

theorem posterior_apply_eq_ofDensity [Nonempty R] [IsFiniteMeasure μ] [IsFiniteKernel σ] (u : F)
    (c : C)
    (hc : (η ∘ₘ Kernel.ofDensity μ (fun u r ↦ σ r {u}) u) {c} ≠ 0) :
    (η†(Kernel.ofDensity μ (fun u r ↦ σ r {u}) u)) c =
      Kernel.ofDensity μ (fun p : C × F ↦ fun r ↦ σ r {p.2} * η r {p.1}) (c, u) := by
  have hfin : μ.withDensity (fun r ↦ σ r {u}) Set.univ ≠ ∞ := by
    rw [withDensity_apply _ .univ, Measure.restrict_univ, lintegral_fintype]
    exact ENNReal.sum_ne_top.2 fun _ _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [← Kernel.ofDensity_apply_eq_posterior η _ hc, Kernel.ofDensity_apply,
    Kernel.ofDensity_apply, Kernel.ofDensity_apply,
    cond_univ_withDensity_mul μ .of_discrete .of_discrete hfin]
  rfl

theorem lt_ofDensity_apply_singleton_iff [IsFiniteMeasure μ] (f : F → R → ℝ≥0∞)
    (u : F) (r : R) (hr : μ {r} ≠ 0) (hf : ∀ r, f u r ≠ ∞) :
    μ {r} < Kernel.ofDensity μ f u {r} ↔ ∑ r', f u r' * μ {r'} < f u r := by
  have htop : ∑ r', f u r' * μ {r'} ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun r' _ ↦ ENNReal.mul_ne_top (hf r') (measure_ne_top _ _)
  rw [Kernel.ofDensity_apply_singleton]
  rcases eq_or_ne (∑ r', f u r' * μ {r'}) 0 with hZ | hZ
  · have h0 : f u r = 0 := by simpa [hr] using (Finset.sum_eq_zero_iff.1 hZ) r (Finset.mem_univ r)
    simp [hZ, h0]
  · rw [ENNReal.lt_div_iff_mul_lt (Or.inl hZ) (Or.inl htop), mul_comm]
    exact ⟨fun h ↦ lt_of_mul_lt_mul_right h zero_le,
      fun h ↦ ENNReal.mul_lt_mul_left hr (measure_ne_top _ _) h⟩

omit [Fintype R] [DiscreteMeasurableSpace R] in
theorem ofDensity_eq_cond_univ_of_forall_eq [IsFiniteKernel σ] {u : F}
    (hσ : ∀ r r', σ r {u} = σ r' {u}) (r₀ : R) (h0 : σ r₀ {u} ≠ 0) :
    Kernel.ofDensity μ (fun u r ↦ σ r {u}) u = μ[|Set.univ] := by
  rw [← Kernel.ofDensity_indicator_one_apply μ (fun _ : F ↦ Set.univ) u .univ]
  exact Kernel.ofDensity_apply_eq_of_eq_mul μ h0 (measure_ne_top _ _) fun r ↦ by simp [hσ r r₀]

theorem map_relation_cond_eq_of_forall_eq [IsProbabilityMeasure μ] [IsMarkovKernel σ] {u : F}
    (hσ : ∀ r r', σ r {u} = σ r' {u}) (r₀ : R) (h0 : σ r₀ {u} ≠ 0) :
    ((μ ⊗ₘ (η ×ₖ σ))[|{x | x.2.2 = u}]).map (fun x ↦ x.2.1) =
      (μ ⊗ₘ (η ×ₖ σ)).map (fun x ↦ x.2.1) := by
  rw [map_relation_cond_compProd_prod, map_relation_compProd_prod,
    ofDensity_eq_cond_univ_of_forall_eq μ σ hσ r₀ h0, cond_univ]

end Model

/-! ### Referents and forms -/

/-- The two characters of a transfer-of-possession context, by thematic role. -/
inductive Role where
  | source
  | goal
  deriving DecidableEq, Fintype

/-- The position of a transfer role, the Source being the subject in (7) and (10). -/
def Role.position : Role → Position
  | .source => .subject
  | .goal => .nonSubject

/-- The form of a reference is a pronoun or another referring expression. -/
inductive Form where
  | pronoun
  | other
  deriving DecidableEq, Fintype

instance : MeasurableSpace Role := ⊤
instance : DiscreteMeasurableSpace Role := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Form := ⊤
instance : DiscreteMeasurableSpace Form := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Relation := ⊤
instance : DiscreteMeasurableSpace Relation := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Position := ⊤
instance : DiscreteMeasurableSpace Position := ⟨fun _ ↦ trivial⟩

/-- A real value prints as the decimal `d` when it lies within half a unit of `d`'s last place. -/
def RoundsTo (x : ℝ) (d : Data.Experiments.Decimal) : Prop :=
  |x - d.toRat| ≤ 1 / (2 * 10 ^ d.exponent)

/-! ### Coherence-conditioned interpretation (Tables 1–5) -/

/-- The Source interpretation rate of Table 1 by aspect, in percent. -/
def aspectSource (a : Aspect) : ℕ := (sourceByAspect a).sourceInterpretation.hundredths.toNat

theorem imperfective_more_source : aspectSource .perfective < aspectSource .imperfective := by
  decide

/-- The measure on relations given by a printed column of frequencies. -/
noncomputable def frequencies (d : Relation → Data.Experiments.Decimal) : Measure Relation :=
  Measure.ofRealWeights fun c ↦ ((d c).toRat : ℝ)

instance (d : Relation → Data.Experiments.Decimal) : IsFiniteMeasure (frequencies d) :=
  inferInstanceAs (IsFiniteMeasure (Measure.ofRealWeights _))

/-- The interpretation kernel of a column of Source biases in percent. -/
noncomputable def interpretation (b : Relation → ℕ) : Kernel Relation Role :=
  Kernel.ofWeights fun c r ↦ match r with
    | .source => (b c : ℝ≥0∞)
    | .goal => ((100 - b c : ℕ) : ℝ≥0∞)

instance (b : Relation → ℕ) : IsFiniteKernel (interpretation b) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

theorem interpretation_comp_real_source (d : Relation → Data.Experiments.Decimal)
    (hd : ∀ c, (0 : ℝ) ≤ (d c).toRat) (b : Relation → ℕ) (hb : ∀ c, b c ≤ 100) :
    (interpretation b ∘ₘ frequencies d).real {.source} =
      ∑ c, ((d c).toRat : ℝ) * b c / 100 := by
  have hk : ∀ c, (interpretation b c).real {.source} = (b c : ℝ) / 100 := fun c ↦ by
    rw [interpretation,
      Kernel.ofWeights_real_singleton _ _ (fun r ↦ by cases r <;> exact ENNReal.natCast_ne_top _),
      show (Finset.univ : Finset Role) = {.source, .goal} by decide,
      Finset.sum_pair (by decide)]
    simp only [ENNReal.toReal_natCast, Nat.cast_sub (hb c)]
    norm_num
  rw [Measure.comp_real_singleton]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hk, frequencies, Measure.ofRealWeights_real_singleton hd]
  ring

/-- The frequency of a relation in the perfective continuations of Table 2. -/
def perfectiveFrequency (c : Relation) : Data.Experiments.Decimal :=
  (relationsPerfective c).frequency

/-- The Source bias of a relation in Table 2, in percent. -/
def perfectiveSourceGiven (c : Relation) : ℕ :=
  (relationsPerfective c).biasToSource.hundredths.toNat

theorem perfective_mixture_masks_biases :
    (2 / 5 < (interpretation perfectiveSourceGiven ∘ₘ frequencies perfectiveFrequency).real
        {.source} ∧
      (interpretation perfectiveSourceGiven ∘ₘ frequencies perfectiveFrequency).real
        {.source} < 3 / 5) ∧
      perfectiveSourceGiven .occasion < 20 ∧ 90 < perfectiveSourceGiven .elaboration ∧
      ∀ c, (perfectiveFrequency c).hundredths ≤ (perfectiveFrequency .occasion).hundredths := by
  have h := interpretation_comp_real_source perfectiveFrequency
    (fun c ↦ by cases c <;> norm_num [perfectiveFrequency, relationsPerfective,
      Data.Experiments.Decimal.toRat]) perfectiveSourceGiven (fun c ↦ by cases c <;> decide)
  rw [show (Finset.univ : Finset Relation) =
      {.occasion, .elaboration, .explanation, .violatedExpectation, .result} by decide] at h
  simp [Finset.sum_insert, perfectiveFrequency, perfectiveSourceGiven, relationsPerfective,
    Data.Experiments.Decimal.hundredths, Data.Experiments.Decimal.toRat] at h
  refine ⟨⟨?_, ?_⟩, by decide, by decide, by decide⟩ <;> rw [h] <;> norm_num

/-- The frequency of a relation under an instruction in Table 3. -/
def instructionFrequency (i : Instruction) (c : Relation) : Data.Experiments.Decimal :=
  (relationsByInstruction c i).frequency

/-- The Source bias of a relation in the instruction manipulation of Table 4, in percent. -/
def instructionSourceGiven (c : Relation) : ℕ :=
  (biasesByRelation c).instructionManipulation.hundredths.toNat

theorem biasesByRelation_original (c : Relation) :
    (biasesByRelation c).original = (relationsPerfective c).biasToSource := by
  cases c <;> rfl

theorem instruction_mixtures :
    (1 / 2 < (interpretation instructionSourceGiven ∘ₘ frequencies (instructionFrequency .why)).real
        {.source} ∧
      (interpretation instructionSourceGiven ∘ₘ
        frequencies (instructionFrequency .whatNext)).real {.source} < 1 / 2) ∧
      50 < (sourceByInstruction .why).sourceInterpretation.hundredths ∧
      (sourceByInstruction .whatNext).sourceInterpretation.hundredths < 50 := by
  have hb : ∀ c, instructionSourceGiven c ≤ 100 := fun c ↦ by cases c <;> decide
  have hu : (Finset.univ : Finset Relation) =
      {.occasion, .elaboration, .explanation, .violatedExpectation, .result} := by decide
  have hw := interpretation_comp_real_source (instructionFrequency .why)
    (fun c ↦ by cases c <;> norm_num [instructionFrequency, relationsByInstruction,
      Data.Experiments.Decimal.toRat]) _ hb
  have hn := interpretation_comp_real_source (instructionFrequency .whatNext)
    (fun c ↦ by cases c <;> norm_num [instructionFrequency, relationsByInstruction,
      Data.Experiments.Decimal.toRat]) _ hb
  rw [hu] at hw hn
  simp [Finset.sum_insert, instructionFrequency, instructionSourceGiven, relationsByInstruction,
    biasesByRelation, Data.Experiments.Decimal.hundredths, Data.Experiments.Decimal.toRat]
    at hw hn
  refine ⟨⟨?_, ?_⟩, by decide, by decide⟩
  · rw [hw]; norm_num
  · rw [hn]; norm_num

/-- A heuristic interpretation bias, the same under every relation, gives the same Source rate
under every distribution of relations (p. 13), while Table 5 prints .34 and .82, which no one
rate rounds to. -/
theorem not_heuristic (ν : Measure Role) (ρ : Instruction → Measure Relation)
    [∀ i, IsProbabilityMeasure (ρ i)] :
    ¬ ∀ i, RoundsTo ((Kernel.const Relation ν ∘ₘ ρ i).real {.source})
      (sourceByInstruction i).sourceInterpretation := by
  intro h
  have e : Kernel.const Relation ν ∘ₘ ρ .whatNext = Kernel.const Relation ν ∘ₘ ρ .why := by
    rw [Measure.const_comp, Measure.const_comp, measure_univ, measure_univ]
  have h₁ := h .whatNext
  have h₂ := h .why
  rw [e] at h₁
  simp only [RoundsTo, sourceByInstruction, Data.Experiments.Decimal.toRat, abs_le] at h₁ h₂
  norm_num at h₁ h₂
  linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-! ### The end state -/

/-- The paper's relations in Kehler's classification. -/
def Relation.toCoherence : Relation → Discourse.Coherence.Relation
  | .occasion => .occasion
  | .elaboration => .elaboration
  | .explanation => .explanation
  | .violatedExpectation => .violatedExpectation
  | .result => .result

/-- A relation focuses the end state when its second segment continues from the end state of the
first, as Occasion does and Result, whose second segment is the effect (pp. 9–10). -/
def FocusesEndState : Discourse.Coherence.Relation → Prop
  | .occasion | .result => True
  | _ => False

instance : DecidablePred FocusesEndState := fun r ↦ by
  unfold FocusesEndState
  cases r with
  | occasion => exact inferInstance
  | resemblance _ => exact inferInstance
  | causeEffect d s => cases d <;> cases s <;> exact inferInstance

theorem goalBiased_iff_focusesEndState (c : Relation) :
    perfectiveSourceGiven c < 50 ↔ FocusesEndState c.toCoherence := by
  cases c <;> decide

theorem goalBiased_iff_focusesEndState_table4 (c : Relation) :
    ((biasesByRelation c).original.hundredths < 50 ∧ instructionSourceGiven c < 50) ↔
      FocusesEndState c.toCoherence := by
  cases c <;> decide

/-! ### Arnold's data (p. 15) -/

/-- The row of the worked example. -/
def arnoldRow : ArnoldPrediction := arnoldPrediction[0]'(by decide)

/-- The next-mention prior over the transfer roles in percent, the Goal's as printed and the
Source's the rest. -/
def arnoldPrior : Role → ℕ
  | .source => 100 - arnoldRow.goalNextMention.hundredths.toNat
  | .goal => arnoldRow.goalNextMention.hundredths.toNat

/-- The production rates of the forms by role, in percent. -/
def arnoldLikelihood : Form → Role → ℕ
  | .pronoun, r => (arnoldPronominalizations r.position).proportion.hundredths.toNat
  | .other, r => 100 - (arnoldPronominalizations r.position).proportion.hundredths.toNat

theorem arnold_prediction :
    (61 / 100 < (Kernel.ofDensity (Measure.ofWeights (arnoldPrior ·))
          (fun u r ↦ (arnoldLikelihood u r : ℝ≥0∞)) .pronoun).real {.goal} ∧
        (Kernel.ofDensity (Measure.ofWeights (arnoldPrior ·))
          (fun u r ↦ (arnoldLikelihood u r : ℝ≥0∞)) .pronoun).real {.goal} < 62 / 100) ∧
      RoundsTo (2784 / 10000) arnoldRow.pronounRate ∧
      RoundsTo ((20 / 100) * (86 / 100) / (28 / 100)) arnoldRow.goalInterpretation := by
  rw [Kernel.ofDensity_real_singleton _ _ _ (by simp),
    show (Finset.univ : Finset Role) = {.source, .goal} by decide, Finset.sum_pair (by decide)]
  simp only [Measure.ofWeights_real_singleton, ENNReal.toReal_natCast, RoundsTo, arnoldPrior,
    arnoldLikelihood, arnoldRow, arnoldPrediction, arnoldPronominalizations, Role.position,
    Data.Experiments.Decimal.hundredths, Data.Experiments.Decimal.toRat, abs_le]
  norm_num

/-! ### Bidirectionality (Table 6) -/

/-- The frequency of a relation by prompt type in Table 6, in percent. -/
def promptFrequency (p : Prompt) (c : Relation) : ℕ :=
  (relationsByPrompt c p).frequency.hundredths.toNat

/-- The share of first mentions to the Goal by prompt type, in percent. -/
def goalMention (p : Prompt) : ℕ := (goalFirstMentions p).percent

theorem prompt_shifts_relations :
    goalMention .pronoun < goalMention .noPronoun ∧
      promptFrequency .noPronoun .elaboration + promptFrequency .noPronoun .explanation <
        promptFrequency .pronoun .elaboration + promptFrequency .pronoun .explanation ∧
      promptFrequency .pronoun .occasion + promptFrequency .pronoun .result <
        promptFrequency .noPronoun .occasion + promptFrequency .noPronoun .result := by
  decide

/-- No joint with an inert pronoun prints Table 6's Elaboration frequencies, since it predicts the
same relation distribution with and without the prompt and .06 and .20 have no common value. -/
theorem not_inert (μ : Measure Role) [IsProbabilityMeasure μ] (η : Kernel Role Relation)
    [IsMarkovKernel η] (σ : Kernel Role Form) [IsMarkovKernel σ]
    (hσ : ∀ r r', σ r {.pronoun} = σ r' {.pronoun}) (h0 : σ .source {.pronoun} ≠ 0) :
    ¬ (RoundsTo (((μ ⊗ₘ (η ×ₖ σ)).map (fun x ↦ x.2.1)).real {.elaboration})
          (relationsByPrompt .elaboration .noPronoun).frequency ∧
        RoundsTo ((((μ ⊗ₘ (η ×ₖ σ))[|{x | x.2.2 = .pronoun}]).map (fun x ↦ x.2.1)).real
          {.elaboration}) (relationsByPrompt .elaboration .pronoun).frequency) := by
  rw [map_relation_cond_eq_of_forall_eq μ η σ hσ .source h0]
  rintro ⟨h₁, h₂⟩
  simp only [RoundsTo, relationsByPrompt, Data.Experiments.Decimal.toRat, abs_le] at h₁ h₂
  norm_num at h₁ h₂
  linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-! ### The voice manipulation (Tables 7–10) -/

/-- The rate of next mention of the causally implicated referent in Table 7. -/
def causalMention (v : Voice) (p : Prompt) : ℕ := (causalMentions v p).proportion.hundredths.toNat

/-- The rate of Explanation continuations in Table 8. -/
def explanationRate (v : Voice) (p : Prompt) : ℕ := (explanations v p).proportion.hundredths.toNat

/-- The observed bias of the pronoun toward the subject in Table 10. -/
def actualSubject (v : Voice) : ℕ := (subjectBiases v).actual.hundredths.toNat

theorem voice_shifts_interpretation_and_coherence :
    causalMention .passive .pronoun < causalMention .active .pronoun ∧
      explanationRate .passive .pronoun < explanationRate .active .pronoun := by
  decide

/-- The next-mention prior over positions in percent, from the no-pronoun column of Table 7, the
causally implicated referent being the active's subject and the passive's by-phrase. -/
def voicePrior (v : Voice) : Position → ℕ
  | .subject => match v with
    | .active => causalMention .active .noPronoun
    | .passive => 100 - causalMention .passive .noPronoun
  | .nonSubject => match v with
    | .active => 100 - causalMention .active .noPronoun
    | .passive => causalMention .passive .noPronoun

/-- The production rates of the forms by position in Table 9, in percent. -/
def voiceLikelihood (v : Voice) : Form → Position → ℕ
  | .pronoun, pos => (pronominalizations v pos).proportion.hundredths.toNat
  | .other, pos => 100 - (pronominalizations v pos).proportion.hundredths.toNat

/-- Table 9 as the production kernel of the voice manipulation. -/
noncomputable def voiceProduction (v : Voice) : Kernel Position Form :=
  Kernel.ofWeights fun pos f ↦ (voiceLikelihood v f pos : ℝ≥0∞)

instance (v : Voice) : IsMarkovKernel (voiceProduction v) :=
  Kernel.isMarkovKernel_ofWeights
    (fun pos ↦ ⟨.pronoun, by cases v <;> cases pos <;>
      simp [voiceLikelihood, pronominalizations, Data.Experiments.Decimal.hundredths]⟩)
    (fun _ _ ↦ ENNReal.natCast_ne_top _)

theorem voiceProduction_apply_singleton (v : Voice) (pos : Position) (f : Form) :
    voiceProduction v pos {f} = 100⁻¹ * (voiceLikelihood v f pos : ℝ≥0∞) := by
  rw [voiceProduction, Kernel.ofWeights_apply_singleton,
    show (Finset.univ : Finset Form) = {.pronoun, .other} by decide, Finset.sum_pair (by decide),
    ENNReal.div_eq_inv_mul]
  congr
  cases v <;> cases pos <;> simp [voiceLikelihood, pronominalizations,
    Data.Experiments.Decimal.hundredths] <;> norm_num

/-- The predicted bias of an ambiguous pronoun toward the subject is the posterior (13) under the
no-pronoun prior of Table 7 and the production kernel of Table 9. -/
noncomputable def bayesSubject (v : Voice) : ℝ :=
  (Kernel.ofDensity (Measure.ofWeights (voicePrior v ·)) (fun u r ↦ voiceProduction v r {u})
    .pronoun).real {.subject}

theorem bayesSubject_eq_fst_cond {C : Type*} [MeasurableSpace C] [Fintype C]
    [DiscreteMeasurableSpace C] (v : Voice) (η : Kernel Position C) [IsMarkovKernel η] :
    bayesSubject v = ((Measure.ofWeights (voicePrior v ·) ⊗ₘ (η ×ₖ voiceProduction v))[|
      {x | x.2.2 = .pronoun}]).fst.real {.subject} := by
  rw [fst_cond_compProd_prod]
  rfl

theorem bayesSubject_eq : bayesSubject .active = 3658 / 4642 ∧
    bayesSubject .passive = 2088 / 3836 := by
  have key (v : Voice) : bayesSubject v =
      (Kernel.ofDensity (Measure.ofWeights (voicePrior v ·))
        (fun u r ↦ (voiceLikelihood v u r : ℝ≥0∞)) .pronoun).real {.subject} := by
    rw [bayesSubject, Kernel.ofDensity_apply_eq_of_eq_mul _ (c := 100⁻¹)
      (f := fun u r ↦ (voiceLikelihood v u r : ℝ≥0∞)) (by simp) (by simp)
      fun r ↦ voiceProduction_apply_singleton v r .pronoun]
  rw [key, key, Kernel.ofDensity_real_singleton _ _ _ (by simp),
    Kernel.ofDensity_real_singleton _ _ _ (by simp),
    show (Finset.univ : Finset Position) = {.subject, .nonSubject} by decide,
    Finset.sum_pair (by decide)]
  simp only [Measure.ofWeights_real_singleton, ENNReal.toReal_natCast, voicePrior, voiceLikelihood,
    causalMention, causalMentions, pronominalizations, Data.Experiments.Decimal.hundredths]
  norm_num

theorem voice_predictions :
    (1 / 2 < bayesSubject .active ∧ 1 / 2 < bayesSubject .passive ∧
        bayesSubject .passive < bayesSubject .active) ∧
      50 < actualSubject .active ∧ 50 < actualSubject .passive ∧
        actualSubject .passive < actualSubject .active := by
  obtain ⟨hA, hP⟩ := bayesSubject_eq
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [hA, hP]
  norm_num

theorem overlaid_subject_bias :
    (voicePrior .active .subject : ℝ) / 100 < bayesSubject .active ∧
      (voicePrior .passive .subject : ℝ) / 100 < bayesSubject .passive := by
  obtain ⟨hA, hP⟩ := bayesSubject_eq
  rw [hA, hP]
  simp only [voicePrior, causalMention, causalMentions, Data.Experiments.Decimal.hundredths]
  norm_num

theorem bayesSubject_lt_predicted (v : Voice) :
    bayesSubject v < (subjectBiases v).predicted.toRat := by
  obtain ⟨hA, hP⟩ := bayesSubject_eq
  cases v
  · rw [hA]; norm_num [subjectBiases, Data.Experiments.Decimal.toRat]
  · rw [hP]; norm_num [subjectBiases, Data.Experiments.Decimal.toRat]

theorem voiceProduction_subject_lt :
    (voiceProduction .active .subject).real {.pronoun} <
      (voiceProduction .passive .subject).real {.pronoun} := by
  simp only [measureReal_def, voiceProduction_apply_singleton]
  simp [voiceLikelihood, pronominalizations, Data.Experiments.Decimal.hundredths]
  norm_num

/-! ### The Centering term

The stimuli pair same-gender characters, so the prompt pronoun φ-agrees with both. The voice
manipulation varies the context sentence, (20a) against (20b): the passive promotes the stimulus
to subject, a stronger signal of topichood than the subject of an active ([davison-1984]), while
under the grammatical-role ranking of forward-looking centers the context's subject is the
backward-looking center of any continuation that mentions it, in either voice. -/

/-- The two characters of (20), both third-person singular feminine. -/
def amanda : Word :=
  ⟨"Amanda", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .Fem)⟩

def brittany : Word :=
  ⟨"Brittany", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .Fem)⟩

theorem she_ambiguous_over_stimuli :
    English.Pronouns.she.toPronoun.CandidateAntecedent amanda ∧
      English.Pronouns.she.toPronoun.CandidateAntecedent brittany := by
  decide

/-- The context sentence of (20) by voice, *Amanda amazed Brittany* in the active and *Brittany
was amazed by Amanda*, with Amanda in the by-phrase, in the passive. -/
def contextSentence : Voice → Utterance Word GrammaticalRole Head
  | .active => { realizations := [⟨amanda, .subject, .name⟩, ⟨brittany, .object, .name⟩] }
  | .passive => { realizations := [⟨brittany, .subject, .name⟩, ⟨amanda, .other, .name⟩] }

/-- The subject of the context sentence. -/
def contextSubject : Voice → Word
  | .active => amanda
  | .passive => brittany

theorem cb_contextSentence (v : Voice) {cur : Utterance Word GrammaticalRole Head}
    (h : contextSubject v ∈ cur) : cb (contextSentence v) cur = some (contextSubject v) := by
  cases v
  · rw [cb, show (contextSentence .active).cf = [amanda, brittany] by decide]
    simp [show amanda ∈ cur from h, contextSubject]
  · rw [cb, show (contextSentence .passive).cf = [brittany, amanda] by decide]
    simp [show brittany ∈ cur from h, contextSubject]

/-- A pronominalization rate that depends on the context's subject only through whether it is the
backward-looking center is the same in both voices, so it cannot print as the subject rates of
Table 9, .62 and .87. -/
theorem not_cbFactored (g : Prop → ℝ) (cur : Voice → Utterance Word GrammaticalRole Head)
    (hcur : ∀ v, contextSubject v ∈ cur v) :
    ¬ ∀ v, RoundsTo (g (cb (contextSentence v) (cur v) = some (contextSubject v)))
      (pronominalizations v .subject).proportion := by
  intro h
  have h₁ := h .active
  have h₂ := h .passive
  rw [cb_contextSentence _ (hcur _), eq_self_iff_true] at h₁ h₂
  simp only [RoundsTo, pronominalizations, Data.Experiments.Decimal.toRat, abs_le] at h₁ h₂
  norm_num at h₁ h₂
  linarith [h₁.1, h₁.2, h₂.1, h₂.2]

end KehlerRohde2013
