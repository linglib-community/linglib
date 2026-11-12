/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.KullbackLeibler.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod

import Linglib.Core.MeasureTheory.Measure.WithDensity
import Linglib.Core.Probability.ConditionalProbability

/-!
# Principles that determine reweighting

A choice rule takes a reference measure on a finite set of alternatives and a cost on them, with
an infinite cost for an alternative that is excluded, and returns a measure on the alternatives.
Three principles are stated for such a rule, besides its returning a probability measure whenever
some alternative of positive reference mass is not excluded:

* consistency: relabelling or merging alternatives commutes with the rule, and so does restricting
  the reference to a subset;
* independence: two independent choices, whose costs add, are made independently;
* monotonicity: a costlier alternative is not favoured beyond its reference mass, so that
  alternatives of equal cost keep their reference odds.

Reweighting the reference by `exp (-α * c)` and normalizing [satisfies
them](##InformationTheory.isChoiceRule_reweight) at every inverse temperature `α`. A rule
satisfying them is [that reweighting at some `α`](##InformationTheory.IsChoiceRule.eq), or one of
the two ends of the family: it conditions the reference on the alternatives that are not excluded,
or on those of least cost. With costs that are zero or infinite, every member of the family at a
positive `α` conditions on the alternatives that are not excluded.

## Implementation notes

* Independence is what selects the exponential: reweighting by another decreasing function of the
  cost satisfies the other principles.
* A probability measure is required only where some alternative of positive reference mass has
  finite cost. Required everywhere, it would leave only the rule that returns the reference, since
  an independent choice among excluded alternatives erases the cost of the choice it is paired
  with.
* The temperature is one constant of the rule, the same for every set of alternatives.

## TODO

* The axiomatic derivations of minimum cross-entropy and of the Gibbs posterior state related
  principles for a rule that takes constraints or a loss; the correspondence is not recorded here.

## References

* [luce-1959]
* [mcfadden-1974]
* [franke-degen-2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace InformationTheory

/-- A choice rule returns, for a reference measure and a cost on a finite type, a measure on it. -/
abbrev ChoiceRule : Type (u + 1) :=
  ∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β],
    Measure β → (β → ℝ≥0∞) → Measure β

/-- The principles for a choice rule. -/
structure IsChoiceRule (R : ChoiceRule.{u}) : Prop where
  /-- The rule returns a probability measure when some alternative of positive reference mass has
  finite cost. -/
  isProbabilityMeasure {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) (h : ∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) :
    IsProbabilityMeasure (R β μ c)
  /-- Relabelling or merging alternatives, with the cost defined on the merged ones, commutes with
  the rule. -/
  map {β γ : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (f : β → γ) (μ : Measure β)
    [IsProbabilityMeasure μ] (c : γ → ℝ≥0∞) : (R β μ (c ∘ f)).map f = R γ (μ.map f) c
  /-- Restricting the reference to a set the rule gives positive mass restricts the rule. -/
  cond {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) (s : Set β) (hs : R β μ c s ≠ 0) :
    R β μ[|s] c = (R β μ c)[|s]
  /-- Independent choices whose costs add are made independently. -/
  prod {β γ : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (μ : Measure β) [IsProbabilityMeasure μ]
    (ν : Measure γ) [IsProbabilityMeasure ν] (c : β → ℝ≥0∞) (d : γ → ℝ≥0∞) :
    R (β × γ) (μ.prod ν) (fun p ↦ c p.1 + d p.2) = (R β μ c).prod (R γ ν d)
  /-- A costlier alternative is not favoured beyond its reference mass. -/
  mono {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) {x y : β} (h : c x ≤ c y) :
    R β μ c {y} * μ {x} ≤ R β μ c {x} * μ {y}

/-- The weight `exp (-α * t)` of a cost `t`. -/
private noncomputable def weight (α : ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  EReal.exp (-((ENNReal.ofReal α * t : ℝ≥0∞) : EReal))

private lemma weight_add (α : ℝ) (a b : ℝ≥0∞) : weight α (a + b) = weight α a * weight α b := by
  rw [weight, weight, weight, mul_add, EReal.coe_ennreal_add,
    EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _)) (.inr (EReal.coe_ennreal_ne_bot _)),
    sub_eq_add_neg, EReal.exp_add]

private lemma weight_antitone (α : ℝ) : Antitone (weight α) := fun _ _ h ↦
  EReal.exp_monotone (EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (by gcongr)))

private lemma weight_le_one (α : ℝ) (t : ℝ≥0∞) : weight α t ≤ 1 :=
  (weight_antitone α (zero_le : 0 ≤ t)).trans_eq (by simp [weight])

private lemma weight_ne_zero (α : ℝ) {t : ℝ≥0∞} (ht : t ≠ ∞) : weight α t ≠ 0 := by
  rw [weight, ne_eq, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht

private instance {β : Type*} [MeasurableSpace β] (μ : Measure β) [IsFiniteMeasure μ] (α : ℝ)
    (c : β → ℝ≥0∞) : IsFiniteMeasure (μ.withDensity fun x ↦ weight α (c x)) :=
  isFiniteMeasure_withDensity ((lintegral_mono fun x ↦ weight_le_one α (c x)).trans_lt
    (by simp)).ne

private lemma cond_univ_prod {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) (ν : Measure γ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ.prod ν)[|Set.univ] = μ[|Set.univ].prod ν[|Set.univ] := by
  have h : μ.prod ν Set.univ = μ Set.univ * ν Set.univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, h]
  rw [ENNReal.mul_inv (.inr (measure_ne_top _ _)) (.inl (measure_ne_top _ _)), mul_comm]

/-- Reweighting the reference by `exp (-α * c)` and normalizing satisfies the principles. -/
theorem isChoiceRule_reweight (α : ℝ) :
    IsChoiceRule.{u} fun _ _ _ _ μ c ↦ (μ.withDensity fun x ↦
      EReal.exp (-((ENNReal.ofReal α * c x : ℝ≥0∞) : EReal)))[|Set.univ] := by
  change IsChoiceRule fun _ _ _ _ μ c ↦ (μ.withDensity fun x ↦ weight α (c x))[|Set.univ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β _ _ _ μ _ c ⟨x, hμx, hcx⟩
    refine cond_isProbabilityMeasure_of_finite (fun h0 ↦ ?_) (measure_ne_top _ _)
    have hx := measure_mono_null (Set.subset_univ {x}) h0
    rw [withDensity_apply _ (.singleton x), lintegral_singleton] at hx
    exact mul_ne_zero (weight_ne_zero α hcx) hμx hx
  · intro β γ _ _ _ _ _ _ f μ _ c
    have hf : Measurable f := .of_discrete
    rw [← Measure.map_withDensity_comp Measurable.of_discrete.aemeasurable hf.aemeasurable,
      cond_map hf.aemeasurable .univ, Set.preimage_univ]
    rfl
  · intro β _ _ _ μ _ c s hs
    have hμs : μ s ≠ 0 := fun h ↦
      hs ((cond_absolutelyContinuous.trans (withDensity_absolutelyContinuous μ _)) h)
    have hcond : μ[|s] = (μ s)⁻¹ • μ.restrict s := rfl
    rw [hcond, withDensity_smul_measure,
      cond_smul (ENNReal.inv_ne_zero.2 (measure_ne_top μ s)) (ENNReal.inv_ne_top.2 hμs),
      ← restrict_withDensity .of_discrete, cond_cond_eq_cond_inter' .univ .of_discrete
        (measure_ne_top _ _), Set.univ_inter]
    simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]
  · intro β γ _ _ _ _ _ _ μ _ ν _ c d
    simp only [weight_add]
    rw [← prod_withDensity (f := fun x ↦ weight α (c x)) (g := fun y ↦ weight α (d y))
      .of_discrete .of_discrete, cond_univ_prod]
  · intro β _ _ _ μ _ c x y h
    simp only [cond_apply MeasurableSet.univ, Set.univ_inter, withDensity_apply _ (.singleton _),
      lintegral_singleton]
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm (μ {y})]
    gcongr
    exact weight_antitone α h

namespace IsChoiceRule

/-! ### The rule read off two alternatives

A rule is read off two alternatives of equal reference mass, through the odds it gives the costlier
one. Monotonicity in both directions keeps the reference odds of alternatives of equal cost; merging
along an inclusion shows that the rule ignores alternatives of no reference mass; independence with
a one-point choice makes the odds depend on the cost difference only; restricting to a pair of
alternatives and merging along the graph of a choice between two gives any two alternatives their
reference odds times the odds of their costs. Independence makes the odds multiplicative in the
cost difference and monotonicity bounds them by one, so they are an exponential, or vanish off
zero, or vanish only at an infinite cost. -/

/-! ### Masses of points -/

private lemma map_singleton_of_injective {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] {f : α → γ} (hf : Measurable f) (hinj : Function.Injective f)
    (ν : Measure α) (z : α) : ν.map f {f z} = ν {z} := by
  rw [Measure.map_apply hf (.singleton _), ← Set.image_singleton, hinj.preimage_image]

private lemma cond_singleton_of_mem {α : Type*} [MeasurableSpace α] {ν : Measure α} {s : Set α}
    (hs : MeasurableSet s) {z : α} (hz : z ∈ s) : ν[|s] {z} = (ν s)⁻¹ * ν {z} := by
  rw [cond_apply hs, Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hz)]

private lemma prod_singleton {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure γ) [SFinite ν] (a : α) (b : γ) :
    μ.prod ν {(a, b)} = μ {a} * ν {b} := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

/-! ### Consequences of the principles on one set of alternatives -/

section General

variable {R : ChoiceRule.{u}} {β : Type u} [Fintype β] [MeasurableSpace β]
  [MeasurableSingletonClass β]

private lemma sum_singleton (μ : Measure β) : ∑ x, μ {x} = μ Set.univ := by
  rw [sum_measure_singleton, Finset.coe_univ]

private lemma exists_ne_zero (μ : Measure β) [IsProbabilityMeasure μ] : ∃ x, μ {x} ≠ 0 := by
  by_contra! h
  have h1 := measure_univ (μ := μ)
  rw [← sum_singleton] at h1
  simp [h] at h1

/-- With no cost the rule returns the reference. -/
private lemma zero_cost (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ] :
    R β μ (fun _ ↦ 0) = μ := by
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero μ
  have := hR.isProbabilityMeasure μ (fun _ ↦ 0) ⟨x₀, hx₀, ENNReal.zero_ne_top⟩
  refine Measure.ext_of_singleton fun x ↦ ?_
  have h := Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) ↦
    le_antisymm (hR.mono μ (fun _ ↦ 0) (le_refl (0 : ℝ≥0∞)) (x := x) (y := y))
      (hR.mono μ (fun _ ↦ 0) le_rfl)
  rwa [← Finset.sum_mul, ← Finset.mul_sum, sum_singleton, sum_singleton, measure_univ,
    measure_univ, one_mul, mul_one, eq_comm] at h

/-- Alternatives of equal cost keep their reference odds. -/
private lemma apply_mul_eq_of_cost_eq (hR : IsChoiceRule R) (μ : Measure β)
    [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) {x y : β} (h : c x = c y) :
    R β μ c {y} * μ {x} = R β μ c {x} * μ {y} :=
  le_antisymm (hR.mono μ c h.le) (hR.mono μ c h.ge)

open Classical in
/-- The rule is the pushforward of the rule on the alternatives of positive reference mass. -/
private lemma map_val (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ]
    (c : β → ℝ≥0∞) :
    (R {x | μ {x} ≠ 0} (μ.comap Subtype.val) (c ∘ Subtype.val)).map Subtype.val = R β μ c := by
  have hemb := MeasurableEmbedding.subtype_coe (MeasurableSet.of_discrete (s := {x | μ {x} ≠ 0}))
  have hmap : (μ.comap Subtype.val).map (Subtype.val : {x | μ {x} ≠ 0} → β) = μ := by
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff_of_countable.2 fun x hx ↦ hx)
  have : IsProbabilityMeasure (μ.comap (Subtype.val : {x | μ {x} ≠ 0} → β)) :=
    ⟨by rw [← Set.preimage_univ (f := Subtype.val), ← hemb.map_apply, hmap, measure_univ]⟩
  rw [hR.map Subtype.val (μ.comap Subtype.val) c, hmap]

/-- The rule gives no mass to an alternative of no reference mass. -/
private lemma apply_eq_zero (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ]
    (c : β → ℝ≥0∞) {y : β} (hy : μ {y} = 0) : R β μ c {y} = 0 := by
  rw [← map_val hR μ c, Measure.map_apply measurable_subtype_coe (.singleton y)]
  convert measure_empty (μ := R _ (μ.comap Subtype.val) _)
  ext ⟨z, hz⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro rfl
  exact hz hy

/-- The rule reads the cost only on the alternatives of positive reference mass. -/
private lemma congr_cost (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ]
    {c c' : β → ℝ≥0∞} (h : ∀ x, μ {x} ≠ 0 → c x = c' x) : R β μ c = R β μ c' := by
  rw [← map_val hR μ c, ← map_val hR μ c']
  congr 2
  funext x
  exact h x x.2

/-- Adding a finite constant to the cost does not change the rule. -/
private lemma add_const (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ]
    (c : β → ℝ≥0∞) {k : ℝ≥0∞} (hk : k ≠ ∞) : R β μ (fun x ↦ c x + k) = R β μ c := by
  have := hR.isProbabilityMeasure (Measure.dirac PUnit.unit.{u+1}) (fun _ ↦ k)
    ⟨PUnit.unit, by simp, hk⟩
  have h := hR.map Prod.fst (μ.prod (Measure.dirac PUnit.unit.{u+1})) (fun x ↦ c x + k)
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  rw [← h, Function.comp_def, hR.prod μ _ c (fun _ ↦ k), Measure.map_fst_prod, measure_univ,
    one_smul]

/-- An alternative of positive reference mass and least finite cost among those is charged. -/
private lemma apply_ne_zero_of_min (hR : IsChoiceRule R) (μ : Measure β)
    [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) {x : β} (hx : μ {x} ≠ 0) (hcx : c x ≠ ∞)
    (hmin : ∀ y, μ {y} ≠ 0 → c x ≤ c y) : R β μ c {x} ≠ 0 := by
  have := hR.isProbabilityMeasure μ c ⟨x, hx, hcx⟩
  intro h0
  have hall : ∀ y, R β μ c {y} = 0 := fun y ↦ by
    by_cases hy : μ {y} = 0
    · exact apply_eq_zero hR μ c hy
    · have h := hR.mono μ c (hmin y hy)
      rw [h0, zero_mul, nonpos_iff_eq_zero, mul_eq_zero] at h
      exact h.resolve_right hx
  have h1 := measure_univ (μ := R β μ c)
  rw [← sum_singleton] at h1
  simp [hall] at h1

end General

/-! ### Two alternatives -/

/-- Two alternatives, in the universe of the rule. -/
private abbrev Two : Type u := ULift.{u} Bool

/-- The uniform reference on two alternatives. -/
private noncomputable def unif : Measure Two.{u} := Measure.count[|Set.univ]

private instance : IsProbabilityMeasure unif.{u} :=
  cond_isProbabilityMeasure (by simp)

private lemma unif_singleton (i : Two.{u}) :
    unif {i} = (Measure.count (Set.univ : Set Two.{u}))⁻¹ := by
  rw [unif, cond_apply .univ, Set.univ_inter, Measure.count_singleton, mul_one]

private lemma unif_singleton_ne_zero (i : Two.{u}) : unif {i} ≠ 0 := by
  rw [unif_singleton]; simp

section Graph

variable {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Conditioning an independent uniform choice on the graph of `k` is the pushforward along the
graph. -/
private lemma cond_range_graph (ν : Measure β) [IsProbabilityMeasure ν] (k : β → Two.{u}) :
    (unif.prod ν)[|Set.range fun z ↦ (k z, z)] = ν.map fun z ↦ (k z, z) := by
  set g : β → Two × β := fun z ↦ (k z, z)
  have hg : Function.Injective g := fun _ _ h ↦ (Prod.ext_iff.1 h).2
  have hS : unif.prod ν (Set.range g) = (Measure.count (Set.univ : Set Two.{u}))⁻¹ := by
    rw [Measure.prod_apply_symm .of_discrete]
    have : ∀ z, (fun i ↦ (i, z)) ⁻¹' Set.range g = {k z} := fun z ↦ by
      ext i; simp [g, eq_comm]
    simp only [this, unif_singleton, lintegral_const, measure_univ, mul_one]
  refine Measure.ext_of_singleton fun ⟨i, z⟩ ↦ ?_
  by_cases h : k z = i
  · subst h
    change (unif.prod ν)[|Set.range g] {g z} = ν.map g {g z}
    rw [map_singleton_of_injective .of_discrete hg,
      cond_singleton_of_mem .of_discrete (Set.mem_range_self z), hS, prod_singleton,
      unif_singleton, ENNReal.inv_mul_cancel_left (by simp) (by simp)]
  · have hz : (i, z) ∉ Set.range g := by
      rintro ⟨w, hw⟩
      simp only [g, Prod.mk.injEq] at hw
      exact h (hw.2 ▸ hw.1)
    rw [cond_apply .of_discrete, Set.inter_singleton_eq_empty.2 hz,
      Measure.map_apply .of_discrete (.singleton _), Set.preimage_singleton_eq_empty.2 hz,
      measure_empty, measure_empty, mul_zero]

end Graph

/-- The cost `a` of the first alternative and `b` of the second. -/
private def cost₂ (a b : ℝ≥0∞) : Two.{u} → ℝ≥0∞ := fun i ↦ bif i.down then b else a

/-- The rule on two alternatives of uniform reference and costs `a` and `b`. -/
private noncomputable def pair (R : ChoiceRule.{u}) (a b : ℝ≥0∞) : Measure Two.{u} :=
  R Two unif (cost₂ a b)

/-- The odds the rule gives an alternative of cost `b` against one of cost `a` and equal reference
mass. -/
private noncomputable def odds (R : ChoiceRule.{u}) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  pair R a b {⟨true⟩} / pair R a b {⟨false⟩}

section Odds

variable {R : ChoiceRule.{u}}

private lemma pair_isProbabilityMeasure (hR : IsChoiceRule R) {a : ℝ≥0∞} (ha : a ≠ ∞)
    (b : ℝ≥0∞) : IsProbabilityMeasure (pair R a b) :=
  hR.isProbabilityMeasure unif _ ⟨⟨false⟩, unif_singleton_ne_zero _, ha⟩

private lemma pair_false_ne_zero (hR : IsChoiceRule R) {a b : ℝ≥0∞} (hab : a ≤ b)
    (ha : a ≠ ∞) : pair R a b {⟨false⟩} ≠ 0 :=
  apply_ne_zero_of_min hR unif _ (unif_singleton_ne_zero _) ha fun
    | ⟨false⟩, _ => le_rfl
    | ⟨true⟩, _ => hab

private lemma pair_false_ne_top (hR : IsChoiceRule R) {a : ℝ≥0∞} (ha : a ≠ ∞) (b : ℝ≥0∞) :
    pair R a b {⟨false⟩} ≠ ∞ :=
  have := pair_isProbabilityMeasure hR ha b
  measure_ne_top _ _

private lemma pair_true_eq (hR : IsChoiceRule R) {a b : ℝ≥0∞} (hab : a ≤ b) (ha : a ≠ ∞) :
    pair R a b {⟨true⟩} = odds R a b * pair R a b {⟨false⟩} :=
  (ENNReal.div_mul_cancel (pair_false_ne_zero hR hab ha) (pair_false_ne_top hR ha b)).symm

private lemma odds_le_one (hR : IsChoiceRule R) {a b : ℝ≥0∞} (hab : a ≤ b) :
    odds R a b ≤ 1 := by
  have h := hR.mono unif (cost₂ a b) (x := ⟨false⟩) (y := ⟨true⟩) hab
  rw [unif_singleton, unif_singleton, ENNReal.mul_le_mul_iff_left (by simp) (by simp)] at h
  exact ENNReal.div_le_of_le_mul (by rwa [one_mul])

private lemma odds_self (hR : IsChoiceRule R) {a : ℝ≥0∞} (ha : a ≠ ∞) : odds R a a = 1 := by
  have h := apply_mul_eq_of_cost_eq hR unif (cost₂ a a) (x := ⟨false⟩) (y := ⟨true⟩) rfl
  rw [unif_singleton, unif_singleton, ENNReal.mul_left_inj (by simp) (by simp)] at h
  rw [odds, pair, h]
  exact ENNReal.div_self (pair_false_ne_zero hR le_rfl ha) (pair_false_ne_top hR ha a)

private lemma odds_add_const (hR : IsChoiceRule R) (a b : ℝ≥0∞) {k : ℝ≥0∞} (hk : k ≠ ∞) :
    odds R (a + k) (b + k) = odds R a b := by
  have : cost₂ (a + k) (b + k) = fun i ↦ cost₂ a b i + k :=
    funext fun | ⟨false⟩ => rfl | ⟨true⟩ => rfl
  rw [odds, odds, pair, pair, this, add_const hR unif _ hk]

/-- The odds depend only on the difference of the costs. -/
private lemma odds_eq_odds_zero (hR : IsChoiceRule R) {a b : ℝ≥0∞} (hab : a ≤ b)
    (ha : a ≠ ∞) : odds R a b = odds R 0 (b - a) := by
  rw [← odds_add_const hR 0 (b - a) ha, zero_add, tsub_add_cancel_of_le hab]

/-- The rule gives two alternatives their reference odds times the odds of their costs. -/
private lemma apply_mul_eq_odds (hR : IsChoiceRule R) {β : Type u} [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (μ : Measure β) [IsProbabilityMeasure μ]
    (c : β → ℝ≥0∞) {x y : β} (hx : μ {x} ≠ 0) (hxy : c x ≤ c y) (hcx : c x ≠ ∞) :
    R β μ c {y} * μ {x} = odds R (c x) (c y) * (R β μ c {x} * μ {y}) := by
  classical
  have := hR.isProbabilityMeasure μ c ⟨x, hx, hcx⟩
  rcases eq_or_ne x y with rfl | hne
  · rw [odds_self hR hcx, one_mul]
  rcases eq_or_ne (R β μ c {x}) 0 with h0 | h0
  · have h := hR.mono μ c hxy
    rw [h0, zero_mul, nonpos_iff_eq_zero] at h
    rw [h, h0, zero_mul, mul_zero]
  set s : Set β := {x, y}
  have hxs : x ∈ s := by simp [s]
  have hys : y ∈ s := by simp [s]
  have hrs : R β μ c s ≠ 0 := fun h ↦ h0 (measure_mono_null (by simpa using hxs) h)
  have hμs : μ s ≠ 0 := fun h ↦ hx (measure_mono_null (by simpa using hxs) h)
  have := cond_isProbabilityMeasure (μ := μ) hμs
  set k : β → Two.{u} := fun z ↦ ⟨decide (z ≠ x)⟩
  set g : β → Two × β := fun z ↦ (k z, z)
  have hg : Function.Injective g := fun _ _ h ↦ (Prod.ext_iff.1 h).2
  have hkx : k x = ⟨false⟩ := by simp [k]
  have hky : k y = ⟨true⟩ := by simp [k, hne.symm]
  set P := (pair R (c x) (c y)).prod μ[|s]
  have hμsx : μ[|s] {x} = (μ s)⁻¹ * μ {x} := cond_singleton_of_mem .of_discrete hxs
  have hμsy : μ[|s] {y} = (μ s)⁻¹ * μ {y} := cond_singleton_of_mem .of_discrete hys
  have hPx : P {g x} = pair R (c x) (c y) {⟨false⟩} * ((μ s)⁻¹ * μ {x}) := by
    rw [prod_singleton, hkx, hμsx]
  have hPy : P {g y} = pair R (c x) (c y) {⟨true⟩} * ((μ s)⁻¹ * μ {y}) := by
    rw [prod_singleton, hky, hμsy]
  have hpos : P (Set.range g) ≠ 0 := by
    refine fun h ↦ ?_
    have := measure_mono_null (Set.singleton_subset_iff.2 (Set.mem_range_self x)) h
    rw [hPx] at this
    exact mul_ne_zero (pair_false_ne_zero hR hxy hcx)
      (mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hx) this
  -- the rule conditioned on `s` is the pushforward of a rule on two alternatives
  have key : ((R β μ c)[|s]).map g = P[|Set.range g] := by
    have hc : R β μ[|s] c =
        R β μ[|s] ((fun q ↦ cost₂ (c x) (c y) q.1 + (fun _ ↦ 0) q.2) ∘ g) := by
      refine congr_cost hR _ fun z hz ↦ ?_
      have hzs : z ∈ s := by
        by_contra hzs
        rw [cond_apply .of_discrete, Set.inter_singleton_eq_empty.2 hzs, measure_empty,
          mul_zero] at hz
        exact hz rfl
      rcases hzs with rfl | rfl
      · simp [g, hkx, cost₂]
      · simp [g, hky, cost₂]
    have hprod : R (Two × β) (unif.prod μ[|s])
        (fun q ↦ cost₂ (c x) (c y) q.1 + (fun _ ↦ 0) q.2) = P := by
      rw [hR.prod unif μ[|s] (cost₂ (c x) (c y)) (fun _ ↦ 0), zero_cost hR]; rfl
    rw [← hR.cond μ c s hrs, hc, hR.map g, ← cond_range_graph, hR.cond _ _ _ (hprod ▸ hpos),
      hprod]
  have hmg : Measurable g := .of_discrete
  have ex := congrArg (fun m : Measure (Two × β) ↦ m {g x}) key
  have ey := congrArg (fun m : Measure (Two × β) ↦ m {g y}) key
  rw [map_singleton_of_injective hmg hg, cond_singleton_of_mem .of_discrete hxs,
    cond_singleton_of_mem .of_discrete (Set.mem_range_self x), hPx] at ex
  rw [map_singleton_of_injective hmg hg, cond_singleton_of_mem .of_discrete hys,
    cond_singleton_of_mem .of_discrete (Set.mem_range_self y), hPy,
    pair_true_eq hR hxy hcx] at ey
  set A := (R β μ c s)⁻¹
  set ρl := pair R (c x) (c y) {⟨false⟩}
  set o := odds R (c x) (c y)
  set Z := P (Set.range g)
  set M := (μ s)⁻¹
  have hA0 : A ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
  have hAt : A ≠ ∞ := ENNReal.inv_ne_top.2 hrs
  rw [← ENNReal.mul_right_inj (mul_ne_zero hA0 (pair_false_ne_zero hR hxy hcx))
    (ENNReal.mul_ne_top hAt (pair_false_ne_top hR hcx (c y)))]
  calc A * ρl * (R β μ c {y} * μ {x}) = ρl * μ {x} * (A * R β μ c {y}) := by ring
    _ = ρl * μ {x} * (Z⁻¹ * (o * ρl * (M * μ {y}))) := by rw [ey]
    _ = ρl * o * μ {y} * (Z⁻¹ * (ρl * (M * μ {x}))) := by ring
    _ = ρl * o * μ {y} * (A * R β μ c {x}) := by rw [ex]
    _ = A * ρl * (o * (R β μ c {x} * μ {y})) := by ring

/-- Independence makes the odds multiplicative in the cost difference. -/
private lemma odds_zero_add (hR : IsChoiceRule R) (s t : ℝ≥0∞) :
    odds R 0 (s + t) = odds R 0 s * odds R 0 t := by
  have hx : unif.{u}.prod unif.{u} {(⟨false⟩, ⟨false⟩)} ≠ 0 := by
    rw [prod_singleton]
    exact mul_ne_zero (unif_singleton_ne_zero _) (unif_singleton_ne_zero _)
  have h := apply_mul_eq_odds hR (unif.{u}.prod unif.{u})
    (fun q ↦ cost₂ 0 s q.1 + cost₂ 0 t q.2) (y := (⟨true⟩, ⟨true⟩)) hx
    (show (0 : ℝ≥0∞) + 0 ≤ s + t by simp) (by simp [cost₂])
  rw [hR.prod unif unif (cost₂ 0 s) (cost₂ 0 t)] at h
  simp only [prod_singleton, unif_singleton] at h
  change pair R 0 s {⟨true⟩} * pair R 0 t {⟨true⟩} * _ =
    odds R (0 + 0) (s + t) * (pair R 0 s {⟨false⟩} * pair R 0 t {⟨false⟩} * _) at h
  rw [pair_true_eq hR zero_le ENNReal.zero_ne_top, pair_true_eq hR zero_le ENNReal.zero_ne_top,
    add_zero] at h
  set v := (Measure.count (Set.univ : Set Two.{u}))⁻¹
  have hv0 : v ≠ 0 := by simp [v]
  have hvt : v ≠ ∞ := by simp [v]
  have hK0 : pair R 0 s {⟨false⟩} * pair R 0 t {⟨false⟩} * (v * v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pair_false_ne_zero hR zero_le ENNReal.zero_ne_top)
      (pair_false_ne_zero hR zero_le ENNReal.zero_ne_top)) (mul_ne_zero hv0 hv0)
  have hKt : pair R 0 s {⟨false⟩} * pair R 0 t {⟨false⟩} * (v * v) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (pair_false_ne_top hR ENNReal.zero_ne_top s)
      (pair_false_ne_top hR ENNReal.zero_ne_top t)) (ENNReal.mul_ne_top hvt hvt)
  rw [← ENNReal.mul_left_inj hK0 hKt, ← h]
  ring

end Odds

/-! ### Multiplicative functions of the cost -/

private lemma le_zero_of_forall_nat_mul_le {d C : ℝ} (h : ∀ n : ℕ, n * d ≤ C) : d ≤ 0 := by
  by_contra! hd
  obtain ⟨n, hn⟩ := exists_nat_gt (C / d)
  have := h n
  rw [div_lt_iff₀ hd] at hn
  linarith

/-- A monotone additive function on the nonnegative reals is linear. -/
private lemma eq_mul_of_add_of_monotone {φ : ℝ≥0 → ℝ} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hmono : Monotone φ) (x : ℝ≥0) : φ x = x * φ 1 := by
  have h0 : φ 0 = 0 := by have := hadd 0 0; simp at this; linarith
  have hnat : ∀ (n : ℕ) (y : ℝ≥0), φ (n * y) = n * φ y := by
    intro n y
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Nat.cast_succ, add_mul, hadd, ih, one_mul, Nat.cast_succ, add_mul, one_mul]
  have h1 : 0 ≤ φ 1 := h0 ▸ hmono zero_le
  have key : ∀ n : ℕ, (n : ℝ) * (φ x - x * φ 1) ≤ φ 1 ∧ (n : ℝ) * (x * φ 1 - φ x) ≤ φ 1 := by
    intro n
    set m := ⌊(n : ℝ≥0) * x⌋₊
    have hm1 : (m : ℝ≥0) ≤ n * x := Nat.floor_le zero_le
    have hm2 : (n : ℝ≥0) * x < m + 1 := Nat.lt_floor_add_one _
    have hlo := hmono hm1
    have hhi := hmono hm2.le
    rw [hnat, ← mul_one (m : ℝ≥0), hnat] at hlo
    rw [hnat, ← Nat.cast_succ, ← mul_one ((m.succ : ℕ) : ℝ≥0), hnat] at hhi
    have hm1' : (m : ℝ) ≤ n * x := by exact_mod_cast hm1
    have hm2' : (n : ℝ) * x < m + 1 := by exact_mod_cast hm2
    push_cast at hhi
    constructor <;> nlinarith
  have ha := le_zero_of_forall_nat_mul_le fun n ↦ (key n).1
  have hb := le_zero_of_forall_nat_mul_le fun n ↦ (key n).2
  linarith

private lemma weight_coe {α : ℝ} (hα : 0 ≤ α) (x : ℝ≥0) :
    weight α x = ENNReal.ofReal (Real.exp (-(α * x))) := by
  rw [weight, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hα, EReal.coe_ennreal_ofReal,
    max_eq_left (mul_nonneg hα x.coe_nonneg), ← EReal.coe_neg, EReal.exp_coe]

private lemma weight_zero (t : ℝ≥0∞) : weight 0 t = 1 := by simp [weight]

private lemma weight_top {α : ℝ} (hα : 0 < α) : weight α ∞ = 0 := by
  simp [weight, ENNReal.mul_top, hα]

/-- A function of the cost that is at most one, one at zero and multiplicative is `exp (-α * c)`,
or vanishes at infinity and is one elsewhere, or vanishes off zero. -/
private lemma classify {f : ℝ≥0∞ → ℝ≥0∞} (h0 : f 0 = 1) (hle : ∀ s, f s ≤ 1)
    (hmul : ∀ s t, f (s + t) = f s * f t) :
    (∃ α : ℝ, 0 ≤ α ∧ ∀ s, f s = weight α s) ∨ (∀ s, f s = if s = ∞ then 0 else 1) ∨
      (∀ s, f s = if s = 0 then 1 else 0) := by
  have hanti : Antitone f := fun a b hab ↦ by
    rw [← add_tsub_cancel_of_le hab, hmul]
    exact mul_le_of_le_one_right' (hle _)
  have htop : ∀ s, f ∞ = f s * f ∞ := fun s ↦ by rw [← hmul, add_top]
  have hfin : ∀ s, f s ≠ ∞ := fun s ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hle s)
  by_cases hz : ∃ s, s ≠ ∞ ∧ f s = 0
  · obtain ⟨s₀, hs₀, hfs₀⟩ := hz
    refine .inr (.inr fun s ↦ ?_)
    split_ifs with hs
    · rw [hs, h0]
    rcases eq_or_ne s ∞ with rfl | hst
    · rw [htop s₀, hfs₀, zero_mul]
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hs hs₀
    have hpow : ∀ n : ℕ, f (n * s) = f s ^ n := by
      intro n
      induction n with
      | zero => simp [h0]
      | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
    have := hanti hn.le
    rw [hpow, hfs₀, nonpos_iff_eq_zero] at this
    exact pow_eq_zero_iff'.1 this |>.1
  push Not at hz
  have hpos : ∀ x : ℝ≥0, 0 < (f x).toReal := fun x ↦
    ENNReal.toReal_pos (hz x ENNReal.coe_ne_top) (hfin x)
  set φ : ℝ≥0 → ℝ := fun x ↦ -Real.log (f x).toReal with hφ
  have hadd : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y
    simp only [φ, ENNReal.coe_add, hmul, ENNReal.toReal_mul,
      Real.log_mul (hpos x).ne' (hpos y).ne']
    ring
  have hmono : Monotone φ := fun x y hxy ↦ by
    simp only [φ, neg_le_neg_iff]
    exact Real.log_le_log (hpos y)
      (ENNReal.toReal_mono (hfin x) (hanti (ENNReal.coe_le_coe.2 hxy)))
  have hα : 0 ≤ φ 1 := by
    simp only [φ, neg_nonneg]
    exact Real.log_nonpos ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using hle 1))
  have hfx : ∀ x : ℝ≥0, f x = weight (φ 1) x := fun x ↦ by
    rw [weight_coe hα, mul_comm, ← eq_mul_of_add_of_monotone hadd hmono x, hφ, neg_neg,
      Real.exp_log (hpos x), ENNReal.ofReal_toReal (hfin x)]
  rcases hα.eq_or_lt with hα0 | hαpos
  · have hf : ∀ x : ℝ≥0, f x = 1 := fun x ↦ by rw [hfx, ← hα0, weight_zero]
    rcases eq_or_ne (f ∞) 0 with h | h
    · refine .inr (.inl fun s ↦ ?_)
      split_ifs with hs
      · rw [hs, h]
      · lift s to ℝ≥0 using hs
        exact hf s
    · have h1 : f ∞ = 1 :=
        ((ENNReal.mul_left_inj h (hfin _)).1 (by rw [one_mul, ← htop ∞])).symm
      refine .inl ⟨0, le_rfl, fun s ↦ ?_⟩
      rw [weight_zero]
      induction s using ENNReal.recTopCoe with
      | top => exact h1
      | coe x => exact hf x
  · refine .inl ⟨φ 1, hα, fun s ↦ ?_⟩
    induction s using ENNReal.recTopCoe with
    | coe x => exact hfx x
    | top =>
      rw [weight_top hαpos]
      by_contra h
      have hf1 : f 1 = 1 :=
        ((ENNReal.mul_left_inj h (hfin _)).1 (by rw [one_mul, ← htop 1])).symm
      have := hfx 1
      rw [weight_coe hα, ENNReal.coe_one, hf1, NNReal.coe_one, mul_one] at this
      exact (ENNReal.ofReal_lt_one.2 (Real.exp_lt_one_iff.2 (neg_lt_zero.2 hαpos))).ne this.symm

/-! ### Assembly -/

section Assembly

variable {R : ChoiceRule.{u}} {β : Type u} [Fintype β] [MeasurableSpace β]
  [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
private lemma exists_min (μ : Measure β) {c : β → ℝ≥0∞} (h : ∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) :
    ∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞ ∧ ∀ y, μ {y} ≠ 0 → c x ≤ c y := by
  classical
  obtain ⟨x₀, hx₀, hcx₀⟩ := h
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun x ↦ μ {x} ≠ 0) c
    ⟨x₀, by simpa using hx₀⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hmin
  exact ⟨x, hx, ne_top_of_le_ne_top hcx₀ (hmin x₀ hx₀), hmin⟩

/-- The rule is the reference reweighted by any function proportional, on the alternatives of
positive reference mass, to the odds of their costs against the least cost, and normalized. -/
private lemma eq_cond_withDensity (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ]
    (c : β → ℝ≥0∞) {x : β} (hx : μ {x} ≠ 0) (hcx : c x ≠ ∞)
    (hmin : ∀ y, μ {y} ≠ 0 → c x ≤ c y) (w : β → ℝ≥0∞) {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ∞)
    (hw : ∀ y, μ {y} ≠ 0 → odds R 0 (c y - c x) = l * w y) :
    R β μ c = (μ.withDensity w)[|Set.univ] := by
  have := hR.isProbabilityMeasure μ c ⟨x, hx, hcx⟩
  have hrx := apply_ne_zero_of_min hR μ c hx hcx hmin
  set κ := R β μ c {x} / μ {x} * l
  have hκ0 : κ ≠ 0 :=
    mul_ne_zero (ENNReal.div_ne_zero.2 ⟨hrx, measure_ne_top _ _⟩) hl0
  have hκt : κ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.div_ne_top (measure_ne_top _ _) hx) hlt
  have h : R β μ c = κ • μ.withDensity w := by
    refine Measure.ext_of_singleton fun y ↦ ?_
    rw [Measure.smul_apply, withDensity_apply _ (.singleton y), lintegral_singleton, smul_eq_mul]
    by_cases hy : μ {y} = 0
    · rw [apply_eq_zero hR μ c hy, hy, mul_zero, mul_zero]
    have hF := apply_mul_eq_odds hR μ c hx (hmin y hy) hcx
    rw [odds_eq_odds_zero hR (hmin y hy) hcx, hw y hy] at hF
    rw [← ENNReal.mul_left_inj hx (measure_ne_top _ _), hF]
    calc l * w y * (R β μ c {x} * μ {y})
        = R β μ c {x} / μ {x} * μ {x} * (l * (w y * μ {y})) := by
          rw [ENNReal.div_mul_cancel hx (measure_ne_top _ _)]; ring
      _ = κ * (w y * μ {y}) * μ {x} := by ring
  calc R β μ c = (R β μ c)[|Set.univ] := (cond_univ _).symm
    _ = (κ • μ.withDensity w)[|Set.univ] := by rw [← h]
    _ = (μ.withDensity w)[|Set.univ] := cond_smul hκ0 hκt _ _

/-- The same, with a weight that is the indicator of a set: the rule conditions the reference on
it. -/
private lemma eq_cond (hR : IsChoiceRule R) (μ : Measure β) [IsProbabilityMeasure μ]
    (c : β → ℝ≥0∞) {x : β} (hx : μ {x} ≠ 0) (hcx : c x ≠ ∞)
    (hmin : ∀ y, μ {y} ≠ 0 → c x ≤ c y) (S : Set β) [DecidablePred (· ∈ S)]
    (hw : ∀ y, μ {y} ≠ 0 → odds R 0 (c y - c x) = if y ∈ S then 1 else 0) :
    R β μ c = μ[|S] := by
  rw [eq_cond_withDensity hR μ c hx hcx hmin (S.indicator 1) one_ne_zero ENNReal.one_ne_top
    fun y hy ↦ by rw [hw y hy, one_mul, Set.indicator_apply]; rfl,
    withDensity_indicator_one .of_discrete, ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.restrict_univ, Measure.restrict_apply_univ]

end Assembly

end IsChoiceRule

/-- A rule satisfying the principles reweights the reference by `exp (-α * c)` at some inverse
temperature `α` and normalizes, or conditions the reference on the alternatives of finite cost, or
conditions it on the alternatives of least cost. -/
theorem IsChoiceRule.eq {R : ChoiceRule.{u}} (hR : IsChoiceRule R) :
    (∃ α : ℝ, 0 ≤ α ∧ ∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞), (∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) →
        R β μ c = (μ.withDensity fun x ↦
          EReal.exp (-((ENNReal.ofReal α * c x : ℝ≥0∞) : EReal)))[|Set.univ]) ∨
    (∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞), (∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) →
        R β μ c = μ[|{x | c x ≠ ∞}]) ∨
    (∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞), (∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) →
        R β μ c = μ[|{x | ∀ y, μ {y} ≠ 0 → c x ≤ c y}]) := by
  classical
  obtain ⟨α, hα, hf⟩ | hf | hf := IsChoiceRule.classify (f := IsChoiceRule.odds R 0)
    (IsChoiceRule.odds_self hR ENNReal.zero_ne_top) (fun _ ↦ IsChoiceRule.odds_le_one hR zero_le)
    (IsChoiceRule.odds_zero_add hR)
  · refine .inl ⟨α, hα, fun β _ _ _ μ _ c hc ↦ ?_⟩
    obtain ⟨x, hx, hcx, hmin⟩ := IsChoiceRule.exists_min μ hc
    have hw0 : weight α (c x) ≠ 0 := weight_ne_zero α hcx
    have hwt : weight α (c x) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (weight_le_one α _)
    refine IsChoiceRule.eq_cond_withDensity hR μ c hx hcx hmin (fun y ↦ weight α (c y))
      (ENNReal.inv_ne_zero.2 hwt) (ENNReal.inv_ne_top.2 hw0) fun y hy ↦ ?_
    rw [hf]
    conv_rhs => rw [← add_tsub_cancel_of_le (hmin y hy), weight_add]
    rw [ENNReal.inv_mul_cancel_left hw0 hwt]
  · refine .inr (.inl fun β _ _ _ μ _ c hc ↦ ?_)
    obtain ⟨x, hx, hcx, hmin⟩ := IsChoiceRule.exists_min μ hc
    refine IsChoiceRule.eq_cond hR μ c hx hcx hmin _ fun y hy ↦ ?_
    rw [hf]
    split_ifs with h1 h2 h2
    · exact absurd (ENNReal.sub_eq_top_iff.1 h1).1 h2
    · rfl
    · rfl
    · exact absurd (ENNReal.sub_eq_top_iff.2 ⟨by simpa using h2, hcx⟩) h1
  · refine .inr (.inr fun β _ _ _ μ _ c hc ↦ ?_)
    obtain ⟨x, hx, hcx, hmin⟩ := IsChoiceRule.exists_min μ hc
    refine IsChoiceRule.eq_cond hR μ c hx hcx hmin _ fun y hy ↦ ?_
    have hiff : c y - c x = 0 ↔ y ∈ {x | ∀ y, μ {y} ≠ 0 → c x ≤ c y} := by
      rw [tsub_eq_zero_iff_le]
      exact ⟨fun h z hz ↦ h.trans (hmin z hz), fun h ↦ h x hx⟩
    rw [hf]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl

end InformationTheory
