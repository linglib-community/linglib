module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.TFAE
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Data.Examples.Adams1975

/-!
# Adams (1975): The Logic of Conditionals: An Application of Probability to Deductive Logic

Adams asks when an inference is probabilistically sound: when making the premises certain enough
makes the conclusion as certain as one likes. A factual formula's probability is the probability
that it is true, and an indicative conditional's is the conditional probability of its consequent
given its antecedent. For factual formulas the answer is classical: such an inference is
probabilistically sound exactly when it is logically valid, and then the conclusion's
uncertainty, its probability of being false, is at most the sum of the premises'. For
conditionals the two part ways. Contraposition, the inference of a conditional from a
disjunction, the hypothetical syllogism and the strengthening of an antecedent are valid for the
material conditional but not probabilistically sound, which is why the English inferences Adams
prints are unacceptable; what p-entailment does satisfy is the rules for conditionals of his
natural deduction system.

## Main results

* `tfae_pEntails`: for factual formulas, logical consequence, p-entailment, the uncertainty bound
  under every probability, and the preservation of certainty coincide.
* `isPreferential_pEntails`: p-entailment from a set of conditionals is closed under the rules
  for conditionals of Adams's natural deduction system.
* `materially_valid_not_pEntailed`, `printed_inferences`: the patterns of conditional inference
  Adams examines are valid for the material conditional but not p-entailed, and the English
  inferences he prints are unacceptable instances of them.
* `not_isRational_pEntails`: unlike the closest-worlds conditional on a total order,
  p-entailment does not validate rational monotonicity.

## Implementation notes

* Possible states of affairs form a measurable space, a formula is the set of states where it is
  true, and a probability-assignment is a probability measure, after Adams's assumption that a
  proposition's probability is the measure of the states in which it is true. His assignments
  are finitely additive on formulas; over finitely many atoms these are the measures on truth
  assignments, and beyond that countable additivity is an added assumption.
* Every formula is a conditional `Formula`, a factual one having a tautological antecedent, as
  rule R1 makes them interderivable; an assignment is proper when it gives each antecedent
  positive probability. Uncertainty, probability of falsity, is stated directly as `μ Aᶜ`.
* The natural deduction rules are proved on a discrete space, where every set of states is an
  event, as for the finite sentential languages Adams considers.

## TODO

* The completeness half of Theorem 4.2, that the rules derive every p-entailed conditional, and
  Theorem 3.3 for conditional premises, that a p-consistent set p-entails only conclusions whose
  material counterparts its own entail.

## References

* [E. W. Adams, *The Logic of Conditionals: An Application of Probability to Deductive
  Logic*][adams-1975]
-/

@[expose] public section

namespace Adams1975

open MeasureTheory ENNReal ProbabilityTheory

/-! ### Formulas of the conditional extension -/

/-- A formula of the conditional extension, *if `ante` then `cons`*. -/
structure Formula (Ω : Type*) where
  /-- The antecedent. -/
  ante : Set Ω
  /-- The consequent. -/
  cons : Set Ω

namespace Formula

variable {Ω : Type*}

/-- The factual formula `A`, *if ⊤ then `A`*. -/
def fact (A : Set Ω) : Formula Ω := ⟨Set.univ, A⟩

/-- The material counterpart of a formula, `ante ⊃ cons`. -/
def material (φ : Formula Ω) : Set Ω := Conditional.materialImp φ.ante φ.cons

end Formula

variable {Ω ι : Type*} [MeasurableSpace Ω] {s : Finset ι}

/-- The premises `X i`, `i ∈ s`, p-entail `d` when, however probable `d` must be, making every
premise probable enough makes it so, under every probability proper for them (Definition 2). -/
def PEntails (s : Finset ι) (X : ι → Formula Ω) (d : Formula Ω) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ μ : Measure Ω, IsProbabilityMeasure μ → μ d.ante ≠ 0 →
    (∀ i ∈ s, μ (X i).ante ≠ 0) → (∀ i ∈ s, 1 - δ ≤ μ[(X i).cons | (X i).ante]) →
      1 - ε ≤ μ[d.cons | d.ante]

/-- A set p-entails each of its members (Theorem 4.1). -/
theorem pEntails_of_mem {X : ι → Formula Ω} {i : ι} (hi : i ∈ s) : PEntails s X (X i) :=
  fun ε hε ↦ ⟨ε, hε, fun _ _ _ _ hp ↦ hp i hi⟩

theorem one_sub_le_cond_iff {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Set Ω} {δ : ℝ≥0∞}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (h0 : μ A ≠ 0) :
    1 - δ ≤ μ[B | A] ↔ μ (A ∩ Bᶜ) ≤ δ * μ A := by
  have := cond_isProbabilityMeasure (μ := μ) h0
  rw [tsub_le_iff_tsub_le, ← prob_compl_eq_one_sub hB, cond_apply hA,
    ENNReal.inv_mul_le_iff h0 (measure_ne_top μ A), mul_comm]

/-- A stricter premise bound gives a weaker hypothesis. -/
private theorem premises_mono {X : ι → Formula Ω} {μ : Measure Ω} {δ δ' : ℝ≥0∞} (h : δ ≤ δ')
    (hp : ∀ i ∈ s, 1 - δ ≤ μ[(X i).cons | (X i).ante]) :
    ∀ i ∈ s, 1 - δ' ≤ μ[(X i).cons | (X i).ante] :=
  fun i hi ↦ (tsub_le_tsub_left h 1).trans (hp i hi)

/-! ### Factual inferences -/

section Factual

variable {A : ι → Set Ω} {B : Set Ω}

theorem pEntails_fact_iff :
    PEntails s (fun i ↦ .fact (A i)) (.fact B) ↔ ∀ ε > 0, ∃ δ > 0, ∀ μ : Measure Ω,
      IsProbabilityMeasure μ → (∀ i ∈ s, 1 - δ ≤ μ (A i)) → 1 - ε ≤ μ B := by
  refine forall₂_congr fun ε _ ↦ exists_congr fun δ ↦ and_congr_right fun _ ↦
    forall₂_congr fun μ hμ ↦ ?_
  simp [Formula.fact, cond_univ]

/-- The uncertainty of a logical consequence is at most the sum of the premises' uncertainties,
the rule of Section I.1 that Theorem 3.1 generalizes. -/
theorem uncertainty_le_sum (h : ⋂ i ∈ s, A i ⊆ B) (μ : Measure Ω) :
    μ Bᶜ ≤ ∑ i ∈ s, μ (A i)ᶜ :=
  calc μ Bᶜ ≤ μ (⋃ i ∈ s, (A i)ᶜ) := measure_mono fun w hw ↦ by
        by_contra hw'
        simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hw'
        exact hw (h (Set.mem_iInter₂.mpr hw'))
    _ ≤ ∑ i ∈ s, μ (A i)ᶜ := measure_biUnion_finset_le s _

theorem exists_dirac_of_not_subset (hB : MeasurableSet B) (h : ¬ ⋂ i ∈ s, A i ⊆ B) :
    ∃ w, (∀ i ∈ s, Measure.dirac w (A i) = 1) ∧ Measure.dirac w B = 0 := by
  obtain ⟨w, hw, hwB⟩ := Set.not_subset.mp h
  exact ⟨w, fun i hi ↦ Measure.dirac_apply_of_mem (Set.mem_iInter₂.mp hw i hi), by
    rw [Measure.dirac_apply' _ hB, Set.indicator_of_notMem hwB]⟩

theorem tfae_pEntails (hA : ∀ i ∈ s, MeasurableSet (A i)) (hB : MeasurableSet B) :
    [⋂ i ∈ s, A i ⊆ B,
      PEntails s (fun i ↦ .fact (A i)) (.fact B),
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → μ Bᶜ ≤ ∑ i ∈ s, μ (A i)ᶜ,
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ i ∈ s, μ (A i) = 1) → μ B = 1].TFAE := by
  tfae_have 1 → 3 := fun h μ _ ↦ uncertainty_le_sum h μ
  tfae_have 3 → 4 := fun h μ hμ h1 ↦ by
    have : μ Bᶜ = 0 := nonpos_iff_eq_zero.mp ((h μ hμ).trans_eq (Finset.sum_eq_zero fun i hi ↦ by
      rw [prob_compl_eq_one_sub (hA i hi), h1 i hi, tsub_self]))
    rwa [prob_compl_eq_zero_iff hB] at this
  tfae_have 4 → 1 := fun h ↦ by
    by_contra hn
    obtain ⟨w, h1, h0⟩ := exists_dirac_of_not_subset hB hn
    simp [h (Measure.dirac w) inferInstance h1] at h0
  tfae_have 3 → 2 := fun h ↦ pEntails_fact_iff.mpr fun ε hε ↦ by
    refine ⟨ε / (s.card + 1), ENNReal.div_pos hε.ne' (by simp), fun μ hμ hp ↦ ?_⟩
    have hu : ∀ i ∈ s, μ (A i)ᶜ ≤ ε / (s.card + 1) := fun i hi ↦ by
      rw [prob_compl_eq_one_sub (hA i hi)]
      exact tsub_le_iff_tsub_le.mp (hp i hi)
    have hsum : μ Bᶜ ≤ ε := (h μ hμ).trans <| (Finset.sum_le_sum hu).trans <| by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc (s.card : ℝ≥0∞) * (ε / (s.card + 1)) ≤ (s.card + 1) * (ε / (s.card + 1)) := by
            gcongr; exact le_self_add
        _ ≤ ε := ENNReal.mul_div_le
    rw [prob_compl_eq_one_sub hB] at hsum
    exact tsub_le_iff_tsub_le.mp hsum
  tfae_have 2 → 1 := fun h ↦ by
    by_contra hn
    obtain ⟨w, h1, h0⟩ := exists_dirac_of_not_subset hB hn
    obtain ⟨δ, -, hδ⟩ := pEntails_fact_iff.mp h (1 / 2) (by norm_num)
    have := hδ (Measure.dirac w) inferInstance fun i hi ↦ (h1 i hi).symm ▸ tsub_le_self
    rw [h0, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at this
    exact absurd this (by norm_num)
  tfae_finish

/-- Where the premises do not p-entail the conclusion, premises as probable as one likes are
compatible with a conclusion as improbable as one likes (Theorem 3.2, for factual formulas). -/
theorem exists_of_not_pEntails (hA : ∀ i ∈ s, MeasurableSet (A i)) (hB : MeasurableSet B)
    (h : ¬ PEntails s (fun i ↦ .fact (A i)) (.fact B)) (ε : ℝ≥0∞) :
    ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧ (∀ i ∈ s, 1 - ε ≤ μ (A i)) ∧ μ B ≤ ε := by
  obtain ⟨w, h1, h0⟩ := exists_dirac_of_not_subset hB (mt ((tfae_pEntails hA hB).out 1 2).mp h)
  exact ⟨Measure.dirac w, inferInstance, fun i hi ↦ by rw [h1 i hi]; exact tsub_le_self, by
    rw [h0]; exact zero_le⟩

end Factual

theorem lottery_attains_bound (n : ℕ) :
    let μ := uniformOn (Set.univ : Set (Fin (n + 1)))
    μ (⋂ i ∈ Finset.univ, ({i}ᶜ : Set (Fin (n + 1))))ᶜ = 1 ∧
      ∑ i : Fin (n + 1), μ ({i}ᶜ)ᶜ = 1 := by
  refine ⟨by simp [Set.iUnion_of_singleton], ?_⟩
  simp [uniformOn_univ, ENNReal.mul_inv_cancel]

/-! ### Conditional inferences -/

section Conditional

variable [DiscreteMeasurableSpace Ω] {X : ι → Formula Ω}

theorem pEntails_iff_mass {φ ψ : Set Ω} : PEntails s X ⟨φ, ψ⟩ ↔ ∀ ε > 0, ∃ δ > 0,
    ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ i ∈ s, μ (X i).ante ≠ 0) →
      (∀ i ∈ s, 1 - δ ≤ μ[(X i).cons | (X i).ante]) → μ (φ ∩ ψᶜ) ≤ ε * μ φ := by
  refine forall₂_congr fun ε _ ↦ exists_congr fun δ ↦ and_congr_right fun _ ↦
    forall₂_congr fun μ hμ ↦ ?_
  refine ⟨fun h hX hp ↦ ?_, fun h h0 hX hp ↦ ?_⟩
  · by_cases h0 : μ φ = 0
    · simp [h0, measure_mono_null Set.inter_subset_left h0]
    · exact (one_sub_le_cond_iff .of_discrete .of_discrete h0).mp (h h0 hX hp)
  · exact (one_sub_le_cond_iff .of_discrete .of_discrete h0).mpr (h hX hp)

/-- **Theorem 4.2, its rules R2 to R6.** P-entailment from a set of conditionals, read as a
relation between antecedent and consequent, is reflexive and closed under weakening and
conjunction of consequents, disjunction of antecedents, and the strengthening of an antecedent by
one of its consequents, the rules from which R2 to R6 follow. -/
theorem isPreferential_pEntails (s : Finset ι) (X : ι → Formula Ω) :
    Nonmonotonic.IsPreferential fun φ ψ ↦ PEntails s X ⟨φ, ψ⟩ where
  refl _ := pEntails_iff_mass.mpr fun _ _ ↦ ⟨1, one_pos, fun _ _ _ _ ↦ by simp⟩
  rightWeakening h hψχ := pEntails_iff_mass.mpr fun ε hε ↦ by
    obtain ⟨δ, hδ, h⟩ := pEntails_iff_mass.mp h ε hε
    exact ⟨δ, hδ, fun μ hμ hX hp ↦ (measure_mono (Set.inter_subset_inter_right _
      (Set.compl_subset_compl.mpr hψχ))).trans (h μ hμ hX hp)⟩
  and {φ ψ χ} h₁ h₂ := pEntails_iff_mass.mpr fun ε hε ↦ by
    obtain ⟨δ₁, hδ₁, h₁⟩ := pEntails_iff_mass.mp h₁ (ε / 2) (ENNReal.half_pos hε.ne')
    obtain ⟨δ₂, hδ₂, h₂⟩ := pEntails_iff_mass.mp h₂ (ε / 2) (ENNReal.half_pos hε.ne')
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ hμ hX hp ↦ ?_⟩
    calc μ (φ ∩ (ψ ∩ χ)ᶜ) ≤ μ (φ ∩ ψᶜ) + μ (φ ∩ χᶜ) := by
          rw [Set.compl_inter, Set.inter_union_distrib_left]; exact measure_union_le _ _
      _ ≤ ε / 2 * μ φ + ε / 2 * μ φ := add_le_add (h₁ μ hμ hX (premises_mono (min_le_left _ _) hp))
          (h₂ μ hμ hX (premises_mono (min_le_right _ _) hp))
      _ = ε * μ φ := by rw [← add_mul, ENNReal.add_halves]
  or {φ ψ χ} h₁ h₂ := pEntails_iff_mass.mpr fun ε hε ↦ by
    obtain ⟨δ₁, hδ₁, h₁⟩ := pEntails_iff_mass.mp h₁ (ε / 2) (ENNReal.half_pos hε.ne')
    obtain ⟨δ₂, hδ₂, h₂⟩ := pEntails_iff_mass.mp h₂ (ε / 2) (ENNReal.half_pos hε.ne')
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ hμ hX hp ↦ ?_⟩
    calc μ ((φ ∪ ψ) ∩ χᶜ) ≤ μ (φ ∩ χᶜ) + μ (ψ ∩ χᶜ) := by
          rw [Set.union_inter_distrib_right]; exact measure_union_le _ _
      _ ≤ ε / 2 * μ φ + ε / 2 * μ ψ := add_le_add (h₁ μ hμ hX (premises_mono (min_le_left _ _) hp))
          (h₂ μ hμ hX (premises_mono (min_le_right _ _) hp))
      _ ≤ ε / 2 * μ (φ ∪ ψ) + ε / 2 * μ (φ ∪ ψ) := by
          gcongr
          · exact Set.subset_union_left
          · exact Set.subset_union_right
      _ = ε * μ (φ ∪ ψ) := by rw [← add_mul, ENNReal.add_halves]
  cautiousMonotonicity {φ ψ χ} h₁ h₂ := pEntails_iff_mass.mpr fun ε hε ↦ by
    obtain ⟨δ₁, hδ₁, h₁⟩ := pEntails_iff_mass.mp h₁ (1 / 2) (by norm_num)
    obtain ⟨δ₂, hδ₂, h₂⟩ := pEntails_iff_mass.mp h₂ (ε / 2) (ENNReal.half_pos hε.ne')
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ hμ hX hp ↦ ?_⟩
    have hψ := h₁ μ hμ hX (premises_mono (min_le_left _ _) hp)
    have hφ : μ φ ≤ 2 * μ (φ ∩ ψ) := by
      have hle : μ φ / 2 + μ φ / 2 ≤ μ (φ ∩ ψ) + μ φ / 2 := by
        rw [ENNReal.add_halves]
        calc μ φ ≤ μ (φ ∩ ψ) + μ (φ ∩ ψᶜ) := by
              rw [← Set.sdiff_eq]; exact measure_le_inter_add_sdiff μ φ ψ
          _ ≤ μ (φ ∩ ψ) + μ φ / 2 := by
              gcongr; rwa [one_div, ← ENNReal.div_eq_inv_mul] at hψ
      have := ENNReal.le_of_add_le_add_right (ENNReal.div_ne_top (measure_ne_top μ φ)
        two_ne_zero) hle
      calc μ φ = 2 * (μ φ / 2) := (ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top).symm
        _ ≤ 2 * μ (φ ∩ ψ) := by gcongr
    calc μ ((φ ∩ ψ) ∩ χᶜ) ≤ μ (φ ∩ χᶜ) :=
          measure_mono (Set.inter_subset_inter_left _ Set.inter_subset_left)
      _ ≤ ε / 2 * μ φ := h₂ μ hμ hX (premises_mono (min_le_right _ _) hp)
      _ ≤ ε / 2 * (2 * μ (φ ∩ ψ)) := by gcongr
      _ = ε * μ (φ ∩ ψ) := by rw [← mul_assoc, ENNReal.div_mul_cancel two_ne_zero ofNat_ne_top]

theorem not_pEntails_of_falsify {d : Formula Ω} {v w : Ω} (hv : v ∈ d.ante) (hvd : v ∉ d.cons)
    (hw : w ∉ d.ante) (hX : ∀ i ∈ s, w ∈ (X i).ante ∧ w ∈ (X i).cons ∨
      w ∉ (X i).ante ∧ v ∈ (X i).ante ∧ v ∈ (X i).cons) :
    ¬ PEntails s X d := by
  intro h
  obtain ⟨δ, hδ, h⟩ := pEntails_iff_mass.mp (show PEntails s X ⟨d.ante, d.cons⟩ from h) (1 / 2)
    (by norm_num)
  set η : ℝ≥0∞ := min (δ / 2) (1 / 2)
  have hη0 : η ≠ 0 := (lt_min (ENNReal.half_pos hδ.ne') (by norm_num)).ne'
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  have hηt : η ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hη1
  have hhalf : 1 / 2 ≤ 1 - η := by
    calc (1 : ℝ≥0∞) / 2 = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - η := tsub_le_tsub_left hη1 1
  set μ : Measure Ω := η • Measure.dirac v + (1 - η) • Measure.dirac w
  have hμ : ∀ S : Set Ω, μ S = η * S.indicator 1 v + (1 - η) * S.indicator 1 w := fun S ↦ by
    simp [μ, Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := S))]
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ]; simpa using add_tsub_cancel_of_le (hη1.trans (by norm_num))⟩
  have hX' : ∀ i ∈ s, μ (X i).ante ≠ 0 := fun i hi ↦ by
    rw [hμ]
    rcases hX i hi with ⟨hwa, -⟩ | ⟨-, hva, -⟩
    · exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hhalf.trans (by simp [hwa])))
    · exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hη0) (by simp [hva]))
  have hp : ∀ i ∈ s, 1 - δ ≤ μ[(X i).cons | (X i).ante] := fun i hi ↦ by
    rw [one_sub_le_cond_iff .of_discrete .of_discrete (hX' i hi)]
    rcases hX i hi with ⟨hwa, hwc⟩ | ⟨hwa, hva, hvc⟩
    · calc μ ((X i).ante ∩ (X i).consᶜ) ≤ η := by
            rw [hμ, Set.indicator_of_notMem
              (show w ∉ (X i).ante ∩ (X i).consᶜ from fun h ↦ h.2 hwc), mul_zero, add_zero]
            by_cases hv' : v ∈ (X i).ante ∩ (X i).consᶜ <;> simp [hv']
        _ ≤ δ / 2 := min_le_left _ _
        _ = δ * (1 / 2) := by rw [ENNReal.div_eq_inv_mul, mul_comm, one_div]
        _ ≤ δ * μ (X i).ante := by gcongr; exact hhalf.trans (by rw [hμ]; simp [hwa])
    · rw [hμ]; simp [hwa, hvc]
  have hd := h μ this hX' hp
  rw [hμ, hμ, Set.indicator_of_mem (show v ∈ d.ante ∩ d.consᶜ from ⟨hv, hvd⟩),
    Set.indicator_of_notMem (fun h ↦ hw h.1), Set.indicator_of_mem hv, Set.indicator_of_notMem hw]
    at hd
  simp only [Pi.one_apply, mul_one, mul_zero, add_zero] at hd
  exact absurd hd (not_le.mpr (by
    rw [one_div, ← ENNReal.div_eq_inv_mul]; exact ENNReal.half_lt_self hη0 hηt))

end Conditional

/-! ### Patterns of conditional inference

The states are the truth-assignments to three atomic formulas `A`, `B` and `C`, and the patterns
are those of Section I.3 with Adams's lettering. -/

/-- A truth-assignment to the atomic formulas `A`, `B` and `C`. -/
abbrev Assignment := Fin 3 → Bool

/-- The atomic formulas `A`, `B` and `C`. -/
def atom (k : Fin 3) : Set Assignment := {v | v k}

/-- The patterns of conditional inference Adams examines. -/
inductive Pattern where
  /-- From `−A` to `A ⇒ B`, the first fallacy of material implication. -/
  | firstFallacy
  /-- From `B` to `A ⇒ B`, the second fallacy of material implication. -/
  | secondFallacy
  /-- From `B ⇒ −A` to `A ⇒ −B`. -/
  | contraposition
  /-- From `A ∨ B` to `−A ⇒ B`. -/
  | disjunction
  /-- From `A ⇒ B` and `B ⇒ C` to `A ⇒ C`. -/
  | hypotheticalSyllogism
  /-- From `B ⇒ C` to `(A & B) ⇒ C`. -/
  | antecedentRestriction
  deriving DecidableEq, Repr, Fintype

namespace Pattern

/-- The premises of a pattern. -/
def premises : Pattern → List (Formula Assignment)
  | firstFallacy => [.fact (atom 0)ᶜ]
  | secondFallacy => [.fact (atom 1)]
  | contraposition => [⟨atom 1, (atom 0)ᶜ⟩]
  | disjunction => [.fact (atom 0 ∪ atom 1)]
  | hypotheticalSyllogism => [⟨atom 0, atom 1⟩, ⟨atom 1, atom 2⟩]
  | antecedentRestriction => [⟨atom 1, atom 2⟩]

/-- The conclusion of a pattern. -/
def conclusion : Pattern → Formula Assignment
  | firstFallacy | secondFallacy => ⟨atom 0, atom 1⟩
  | contraposition => ⟨atom 0, (atom 1)ᶜ⟩
  | disjunction => ⟨(atom 0)ᶜ, atom 1⟩
  | hypotheticalSyllogism => ⟨atom 0, atom 2⟩
  | antecedentRestriction => ⟨atom 0 ∩ atom 1, atom 2⟩

/-- The name a pattern bears in the data. -/
def name : Pattern → String
  | firstFallacy => "firstFallacy"
  | secondFallacy => "secondFallacy"
  | contraposition => "contraposition"
  | disjunction => "disjunction"
  | hypotheticalSyllogism => "hypotheticalSyllogism"
  | antecedentRestriction => "antecedentRestriction"

/-- The pattern is valid for the material conditional. -/
def MateriallyValid (π : Pattern) : Prop :=
  ∀ v, (∀ φ ∈ π.premises, v ∈ φ.material) → v ∈ π.conclusion.material

/-- The premises p-entail the conclusion. -/
def PEntailed (π : Pattern) : Prop :=
  PEntails Finset.univ π.premises.get π.conclusion

/-- A state that falsifies the conclusion and one that verifies the premises, from Adams's
figures. -/
def witnesses : Pattern → Assignment × Assignment
  | firstFallacy => (![true, false, false], ![false, false, false])
  | secondFallacy => (![true, false, false], ![false, true, false])
  | contraposition => (![true, true, false], ![false, true, false])
  | disjunction => (![false, false, false], ![true, false, false])
  | hypotheticalSyllogism | antecedentRestriction => (![true, true, false], ![false, true, true])

end Pattern

/-- **Section I.3.** Each pattern is valid for the material conditional but not p-entailed. -/
theorem materially_valid_not_pEntailed (π : Pattern) : π.MateriallyValid ∧ ¬ π.PEntailed := by
  refine ⟨by
    cases π <;> intro v <;>
      simp [Pattern.premises, Pattern.conclusion, Formula.material, Formula.fact, atom] <;>
      revert v <;> decide, ?_⟩
  refine not_pEntails_of_falsify (v := π.witnesses.1) (w := π.witnesses.2) ?_ ?_ ?_ ?_ <;>
    cases π <;> simp [Pattern.witnesses, Pattern.premises, Pattern.conclusion, atom, Formula.fact,
      Fin.forall_fin_succ]

theorem printed_inferences : ∀ e ∈ Examples.all, e.judgment = .unacceptable ∧
    ∃ π : Pattern, e.feature? "pattern" = some π.name ∧ π.MateriallyValid ∧ ¬ π.PEntailed := by
  intro e he
  have hname : e.judgment = .unacceptable ∧ ∃ π : Pattern, e.feature? "pattern" = some π.name := by
    revert e; decide
  obtain ⟨hj, π, hπ⟩ := hname
  exact ⟨hj, π, hπ, materially_valid_not_pEntailed π⟩

theorem not_isRational_pEntails :
    ¬ Nonmonotonic.IsRational fun φ ψ : Set Assignment ↦
      PEntails Finset.univ ![(⟨atom 1, atom 2⟩ : Formula Assignment)] ⟨φ, ψ⟩ := fun h ↦
  not_pEntails_of_falsify (v := ![true, true, false]) (w := ![false, true, true])
    (by simp [atom]) (by simp [atom]) (by simp [atom]) (by simp [atom])
    (h.rationalMonotonicity (φ := atom 1) (ψ := atom 0) (pEntails_of_mem (Finset.mem_univ 0))
      (not_pEntails_of_falsify (v := ![true, true, true]) (w := ![false, false, false])
        (by simp [atom]) (by simp [atom]) (by simp [atom]) (by simp [atom])))

end Adams1975
