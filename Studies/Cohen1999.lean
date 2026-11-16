module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Quantification.Counting

/-!
# Cohen (1999): Think Generic!

Cohen's inductivist semantics makes a generic sentence a probability judgment. With $A$ the
disjunction of the alternatives, $\mathbf{gen}(\psi, \phi)$ holds when $P(\phi \mid \psi \wedge A)$
exceeds one half on the absolute reading, and when it exceeds $P(\phi \mid A)$ on the relative
one. For fixed alternatives both are determiner denotations. The absolute reading is
[conservative](##Cohen1999.conservative_freq) and, on a counting measure with trivial
alternatives, [is *most*](##Cohen1999.gen_count_univ). The relative reading is
[positive correlation within the alternatives](##Cohen1999.genRelative_iff_mul_lt), so it is
symmetric in restrictor and scope and not conservative. Requiring the same probability in every
subclass of the reference class [leaves only the exceptionless
cases](##Cohen1999.homogeneous_iff), so the final truth conditions ask for the threshold within
the cells of salient partitions alone, which
[strengthens the absolute reading](##Cohen1999.gen_of_genSalient). Frequency adverbs put other
requirements on the same probability.

## Implementation notes

* Page and definition numbers follow the 1996 Carnegie Mellon dissertation, whose independent and
  dependent readings are the absolute and relative readings here.
* The probability is any measure `μ`, and the finite models are the counting measure. The
  alternatives enter the definitions only through their disjunction `A`; the alternatives to the
  restrictor and to the scope are conjoined into it.
* A conditional probability on a null reference class is undefined in the source and `0` here, so
  **gen** is false there, and a salient cell with a null reference class imposes no condition.
* A salient cell restricts the alternatives, which is
  [conditioning the measure on the cell](##Cohen1999.gen_cond).

## TODO

* The unboundedness constraint and lawlikeness restrict which sentences express generics at all
  and are not stated.
* The calculus of alternatives, the quantification over cases and the default reasoning of the
  later chapters are not formalized; the alternatives are taken as given.

## References

* [cohen-1999a]
* [salmon-1977]
* [thomason-1988]
* [carlson-1977a]
-/

@[expose] public section

namespace Cohen1999

open Quantifier Quantifier.Det MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Finset

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α)

/-- A frequency adverb puts its lexical requirement `R` on the conditional probability of the
scope `φ`, given the restrictor `ψ` and the disjunction `A` of the alternatives (definition 10,
p. 138). -/
def freq (R : ℝ≥0∞ → Prop) : Det α := fun ψ φ ↦ R (μ[φ | ψ ∩ A])

/-- The generic quantifier on its absolute reading (definition 1, p. 39) holds when the
conditional probability of the scope, given the restrictor and the alternatives, exceeds one
half. -/
def gen : Det α := fun ψ φ ↦ 2⁻¹ < μ[φ | ψ ∩ A]

/-- The relative reading (definition 3, p. 60) holds when the restrictor raises the probability of
the scope above its value among the alternatives. -/
def genRelative : Det α := fun ψ φ ↦ μ[φ | A] < μ[φ | ψ ∩ A]

/-- The final truth conditions on the absolute reading (definition 5, p. 90) ask for the
threshold within every salient cell whose reference class is not null. With a requirement in
place of the threshold this is the final definition of the frequency adverbs (definition 11,
p. 142). -/
def genSalient (cells : ι → Set α) : Det α := fun ψ φ ↦
  ∀ i, μ (ψ ∩ (cells i ∩ A)) ≠ 0 → gen μ (cells i ∩ A) ψ φ

/-- The final truth conditions on the relative reading (definition 5, p. 90) compare, within every
salient cell, the restrictor's probability of the scope with that of the cell. -/
def genRelativeSalient (cells : ι → Set α) : Det α := fun ψ φ ↦
  ∀ i, μ (ψ ∩ (cells i ∩ A)) ≠ 0 → genRelative μ (cells i ∩ A) ψ φ

/-- A reference class `ψ` is homogeneous with respect to `φ` (definition 4, pp. 88–89, after
Salmon) when no subclass of positive probability changes the probability of `φ`. -/
def Homogeneous (ψ φ : Set α) : Prop :=
  ∀ ω, MeasurableSet ω → μ (ψ ∩ ω) ≠ 0 → μ[φ | ψ ∩ ω] = μ[φ | ψ]

variable {μ A} {ψ φ ω : Set α} {cells : ι → Set α}

/-! ### The absolute reading -/

theorem gen_iff_lt (hs : MeasurableSet (ψ ∩ A)) :
    gen μ A ψ φ ↔ μ (ψ ∩ A) < 2 * μ (ψ ∩ A ∩ φ) := by
  rw [gen, cond_apply hs]
  rcases eq_or_ne (μ (ψ ∩ A)) 0 with h0 | h0
  · simp [h0, measure_mono_null inter_subset_left h0]
  rcases eq_or_ne (μ (ψ ∩ A)) ∞ with ht | ht
  · simp [ht]
  rw [← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (.inl h0) (.inl ht),
    ← ENNReal.div_eq_inv_mul, ENNReal.div_lt_iff (by simp) (by simp), mul_comm]

theorem scopeMonotone_freq {R : ℝ≥0∞ → Prop} (hR : Monotone R) : (freq μ A R).ScopeMonotone :=
  fun _ _ _ h ↦ hR (measure_mono h)

theorem scopeMonotone_gen : (gen μ A).ScopeMonotone :=
  fun _ _ _ h hg ↦ hg.trans_le (measure_mono h)

theorem freq_inter_left {R : ℝ≥0∞ → Prop} (hs : MeasurableSet (ψ ∩ A)) :
    freq μ A R ψ (ψ ∩ φ) ↔ freq μ A R ψ φ := by
  have h : ψ ∩ A ∩ (ψ ∩ φ) = ψ ∩ A ∩ φ := by ext; simp only [mem_inter_iff]; tauto
  rw [freq, freq, cond_apply hs, cond_apply hs, h]

/-- Whatever its requirement, a frequency adverb on the absolute reading is conservative: the
scope matters only within the restrictor (§3.4.2, p. 57; §6.2.2, p. 139). -/
theorem conservative_freq [DiscreteMeasurableSpace α] (R : ℝ≥0∞ → Prop) :
    (freq μ A R).Conservative :=
  fun _ _ ↦ (freq_inter_left .of_discrete).symm

theorem conservative_gen [DiscreteMeasurableSpace α] : (gen μ A).Conservative :=
  conservative_freq (2⁻¹ < ·)

-- §5.7, pp. 131–132
theorem gen_self_iff [IsFiniteMeasure μ] (hs : MeasurableSet (ψ ∩ φ)) :
    gen μ φ ψ φ ↔ μ (ψ ∩ φ) ≠ 0 := by
  rw [gen_iff_lt hs, inter_assoc, inter_self, two_mul]
  exact ⟨fun h h0 ↦ by simp [h0] at h, ENNReal.lt_add_right (measure_ne_top _ _)⟩

/-! ### The relative reading -/

/-- The relative reading is positive correlation of restrictor and scope within the
alternatives. -/
theorem genRelative_iff_mul_lt [IsFiniteMeasure μ] (hA : MeasurableSet A)
    (hψ : MeasurableSet ψ) :
    genRelative μ A ψ φ ↔ μ (A ∩ φ) * μ (ψ ∩ A) < μ (ψ ∩ A ∩ φ) * μ A := by
  rw [genRelative, cond_apply hA, cond_apply (hψ.inter hA)]
  rcases eq_or_ne (μ (ψ ∩ A)) 0 with h0 | h0
  · simp [h0, measure_mono_null inter_subset_left h0]
  have hA0 : μ A ≠ 0 := fun h ↦ h0 (measure_mono_null inter_subset_right h)
  rw [← ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hA0) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h0) (measure_ne_top _ _)),
    ← ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [inv_mul_eq_div, inv_mul_eq_div, div_lt_div_iff₀
    (ENNReal.toReal_pos hA0 (measure_ne_top _ _)) (ENNReal.toReal_pos h0 (measure_ne_top _ _))]

-- (124b), p. 57
theorem genRelative_comm [IsFiniteMeasure μ] (hA : MeasurableSet A) (hψ : MeasurableSet ψ)
    (hφ : MeasurableSet φ) : genRelative μ A ψ φ ↔ genRelative μ A φ ψ := by
  rw [genRelative_iff_mul_lt hA hψ, genRelative_iff_mul_lt hA hφ, inter_comm A φ, inter_comm ψ A,
    inter_comm φ A, inter_right_comm A φ ψ, mul_comm]

-- (128), p. 58
theorem genRelative_inter_left_iff [IsFiniteMeasure μ] (hA : MeasurableSet A)
    (hψ : MeasurableSet ψ) :
    genRelative μ A ψ (ψ ∩ φ) ↔ μ (ψ ∩ A ∩ φ) ≠ 0 ∧ μ (A \ ψ) ≠ 0 := by
  have h₁ : A ∩ (ψ ∩ φ) = ψ ∩ A ∩ φ := by ext; simp only [mem_inter_iff]; tauto
  have h₂ : ψ ∩ A ∩ (ψ ∩ φ) = ψ ∩ A ∩ φ := by ext; simp only [mem_inter_iff]; tauto
  rw [genRelative_iff_mul_lt hA hψ, h₁, h₂, ← measure_inter_add_sdiff A hψ, inter_comm A ψ]
  rcases eq_or_ne (μ (ψ ∩ A ∩ φ)) 0 with h0 | h0
  · simp [h0]
  rw [ENNReal.mul_lt_mul_iff_right h0 (measure_ne_top _ _)]
  exact ⟨fun h ↦ ⟨h0, fun h' ↦ by simp [h'] at h⟩,
    fun h ↦ ENNReal.lt_add_right (measure_ne_top _ _) h.2⟩

/-! ### Homogeneity -/

/-- Unrestricted homogeneity holds only in the two exceptionless cases, since the scope itself
cuts a subclass out of any mixed reference class (p. 89). -/
theorem homogeneous_iff [IsFiniteMeasure μ] (hψ : MeasurableSet ψ) (hφ : MeasurableSet φ) :
    Homogeneous μ ψ φ ↔ μ[φ | ψ] = 0 ∨ μ[φ | ψ] = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases h0 : μ (ψ ∩ φ) = 0
    · exact .inl (by rw [cond_apply hψ, h0, mul_zero])
    · rw [← h φ hφ h0, cond_apply (hψ.inter hφ), inter_assoc, inter_self]
      exact .inr (ENNReal.inv_mul_cancel h0 (measure_ne_top _ _))
  · rintro (h | h) ω hω hc
    · have h0 : μ (ψ ∩ φ) = 0 := by
        rw [cond_apply hψ] at h
        exact (mul_eq_zero.1 h).resolve_left (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
      rw [h, cond_apply (hψ.inter hω), (measure_mono_null
        (inter_subset_inter_left φ inter_subset_left) h0 : μ (ψ ∩ ω ∩ φ) = 0), mul_zero]
    · have hd : μ (ψ \ φ) = 0 := by
        have h₁ := cond_mul_eq_inter hψ φ μ
        have h₂ := measure_inter_add_sdiff (μ := μ) ψ hφ
        rw [h, one_mul] at h₁
        rw [← h₁] at h₂
        by_contra hne
        exact (ENNReal.lt_add_right (measure_ne_top μ ψ) hne).ne' h₂
      have he : μ (ψ ∩ ω ∩ φ) = μ (ψ ∩ ω) :=
        le_antisymm (measure_mono inter_subset_left) <|
          calc μ (ψ ∩ ω) ≤ μ (ψ ∩ ω ∩ φ ∪ ψ \ φ) := measure_mono fun x hx ↦ by
                by_cases hx' : x ∈ φ
                · exact .inl ⟨hx, hx'⟩
                · exact .inr ⟨hx.1, hx'⟩
            _ ≤ μ (ψ ∩ ω ∩ φ) + μ (ψ \ φ) := measure_union_le _ _
            _ = μ (ψ ∩ ω ∩ φ) := by rw [hd, add_zero]
      rw [h, cond_apply (hψ.inter hω), he]
      exact ENNReal.inv_mul_cancel hc (measure_ne_top _ _)

/-! ### Salient partitions -/

theorem gen_cond (hω : MeasurableSet ω) (hs : MeasurableSet (ψ ∩ A)) (ht : μ ω ≠ ∞) :
    gen μ[|ω] A ψ φ ↔ gen μ (ω ∩ A) ψ φ := by
  rw [gen, gen, cond_cond_eq_cond_inter' hω hs ht, inter_left_comm]

theorem genRelative_cond (hω : MeasurableSet ω) (hψ : MeasurableSet ψ) (hA : MeasurableSet A)
    (ht : μ ω ≠ ∞) : genRelative μ[|ω] A ψ φ ↔ genRelative μ (ω ∩ A) ψ φ := by
  rw [genRelative, genRelative, cond_cond_eq_cond_inter' hω hA ht,
    cond_cond_eq_cond_inter' hω (hψ.inter hA) ht, inter_left_comm]

/-- A generic true within every cell of a partition of its reference class is true on the absolute
reading: the final truth conditions strengthen the first (p. 90). -/
theorem gen_of_genSalient [Countable ι] (hd : Pairwise (Disjoint on cells))
    (hm : ∀ i, MeasurableSet (cells i)) (hcover : ψ ∩ A ⊆ ⋃ i, cells i) (hψ : MeasurableSet ψ)
    (hA : MeasurableSet A) (hφ : MeasurableSet φ) (hc : μ (ψ ∩ A) ≠ 0) (ht : μ (ψ ∩ A) ≠ ∞)
    (h : genSalient μ A cells ψ φ) : gen μ A ψ φ := by
  have key : ∀ t, MeasurableSet t → t ⊆ ψ ∩ A → μ t = ∑' i, μ (t ∩ cells i) := fun t ht hsub ↦ by
    have h₁ := Measure.restrict_iUnion_apply (μ := μ) hd hm ht
    simp only [Measure.restrict_apply ht] at h₁
    rwa [inter_eq_left.2 (hsub.trans hcover)] at h₁
  have cell : ∀ j, μ (ψ ∩ A ∩ cells j) ≠ 0 →
      μ (ψ ∩ A ∩ cells j) < 2 * μ (ψ ∩ A ∩ φ ∩ cells j) := fun j hj ↦ by
    have e : ψ ∩ (cells j ∩ A) = ψ ∩ A ∩ cells j := by ext; simp only [mem_inter_iff]; tauto
    have h₁ := (gen_iff_lt (hψ.inter ((hm j).inter hA))).1 (h j (e ▸ hj))
    rwa [e, inter_right_comm _ (cells j) φ] at h₁
  obtain ⟨i, hi⟩ : ∃ i, μ (ψ ∩ A ∩ cells i) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (by rw [key _ (hψ.inter hA) subset_rfl]; simp [hall])
  rw [gen_iff_lt (hψ.inter hA), key _ (hψ.inter hA) subset_rfl,
    key _ ((hψ.inter hA).inter hφ) inter_subset_left, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_lt_tsum (i := i) ?_ (fun j ↦ ?_) (cell i hi)
  · rwa [← key _ (hψ.inter hA) subset_rfl]
  · by_cases hj : μ (ψ ∩ A ∩ cells j) = 0
    · simp [hj]
    · exact (cell j hj).le

/-! ### Frequency adverbs

The requirements of *never*, *sometimes* and *always* (p. 137) are the three quantifiers of the
conditional measure: almost nowhere, frequently and almost everywhere. -/

theorem freq_eq_zero_iff : freq μ A (· = 0) ψ φ ↔ ∀ᵐ x ∂μ[|ψ ∩ A], x ∉ φ :=
  measure_eq_zero_iff_ae_notMem

theorem freq_pos_iff : freq μ A (0 < ·) ψ φ ↔ ∃ᵐ x ∂μ[|ψ ∩ A], x ∈ φ :=
  pos_iff_ne_zero.trans frequently_ae_mem_iff.symm

theorem freq_eq_one_iff (hc : μ (ψ ∩ A) ≠ 0) (ht : μ (ψ ∩ A) ≠ ∞) (hφ : MeasurableSet φ) :
    freq μ A (· = 1) ψ φ ↔ ∀ᵐ x ∂μ[|ψ ∩ A], x ∈ φ :=
  have := cond_isProbabilityMeasure_of_finite hc ht
  (mem_ae_iff_prob_eq_one hφ).symm

/-! ### The counting measure

On a finite universe with the counting measure the probabilities are proportions, and the
classical determiners reappear. -/

section Count

variable [MeasurableSingletonClass α]

-- p. 137
theorem freq_count_eq_zero_iff [Finite α] : freq .count A (· = 0) ψ φ ↔ no (ψ ∩ A) φ :=
  (uniformOn_eq_zero_iff (toFinite _)).trans
    (disjoint_iff_inter_eq_empty.symm.trans subset_compl_iff_disjoint_right.symm)

theorem freq_count_pos_iff [Finite α] : freq .count A (0 < ·) ψ φ ↔ Det.some (ψ ∩ A) φ :=
  pos_iff_ne_zero.trans (uniformOn_ne_zero_iff (toFinite _))

theorem freq_count_eq_one_iff [Finite α] (h : (ψ ∩ A).Nonempty) :
    freq .count A (· = 1) ψ φ ↔ every (ψ ∩ A) φ :=
  uniformOn_eq_one_iff (toFinite _) h

theorem gen_count_iff_most [Finite α] : gen .count A ψ φ ↔ most (ψ ∩ A) φ := by
  rw [gen_iff_lt .of_discrete, Measure.count_apply .of_discrete, Measure.count_apply .of_discrete,
    ← (toFinite (ψ ∩ A)).cast_ncard_eq, ← (toFinite (ψ ∩ A ∩ φ)).cast_ncard_eq, most_apply]
  have h := ncard_inter_add_ncard_sdiff_eq_ncard (ψ ∩ A) φ (toFinite _)
  simp only [ENat.toENNReal_coe]
  norm_cast
  omega

/-- On the counting measure of a finite universe, with alternatives that exclude nothing, the
absolute reading is the determiner *most*. -/
theorem gen_count_univ [Finite α] : gen (.count : Measure α) univ = most :=
  funext fun ψ ↦ funext fun φ ↦ propext (by rw [gen_count_iff_most, inter_univ])

-- p. 89
theorem homogeneous_count_iff [Finite α] :
    Homogeneous .count ψ φ ↔ no ψ φ ∨ every ψ φ := by
  rw [homogeneous_iff .of_discrete .of_discrete]
  rcases ψ.eq_empty_or_nonempty with rfl | hψ
  · simp [no, every]
  · exact or_congr ((uniformOn_eq_zero_iff (toFinite _)).trans
      (disjoint_iff_inter_eq_empty.symm.trans subset_compl_iff_disjoint_right.symm))
      (uniformOn_eq_one_iff (toFinite _) hψ)

variable [Fintype α] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ ψ)] [DecidablePred (· ∈ φ)]

private theorem count_eq_card (s : Set α) [DecidablePred (· ∈ s)] :
    Measure.count s = #{x | x ∈ s} := by
  rw [← Measure.count_apply_finset]
  congr 1
  ext
  simp

theorem gen_count_iff_card :
    gen .count A ψ φ ↔ #{x | x ∈ ψ ∩ A} < 2 * #{x | x ∈ ψ ∩ A ∩ φ} := by
  rw [gen_iff_lt .of_discrete, count_eq_card, count_eq_card]
  norm_cast

instance : Decidable (gen .count A ψ φ) := decidable_of_iff _ gen_count_iff_card.symm

theorem genRelative_count_iff_card :
    genRelative .count A ψ φ ↔
      #{x | x ∈ A ∩ φ} * #{x | x ∈ ψ ∩ A} < #{x | x ∈ ψ ∩ A ∩ φ} * #{x | x ∈ A} := by
  rw [genRelative_iff_mul_lt .of_discrete .of_discrete, count_eq_card (A ∩ φ),
    count_eq_card (ψ ∩ A), count_eq_card (ψ ∩ A ∩ φ), count_eq_card A]
  norm_cast

instance : Decidable (genRelative .count A ψ φ) :=
  decidable_of_iff _ genRelative_count_iff_card.symm

variable [Fintype ι] [∀ i, DecidablePred (· ∈ cells i)]

instance : Decidable (genSalient .count A cells ψ φ) :=
  decidable_of_iff (∀ i, (∃ x, x ∈ ψ ∩ (cells i ∩ A)) → gen .count (cells i ∩ A) ψ φ)
    (forall_congr' fun _ ↦ imp_congr_left Measure.count_ne_zero_iff.symm)

instance : Decidable (genRelativeSalient .count A cells ψ φ) :=
  decidable_of_iff (∀ i, (∃ x, x ∈ ψ ∩ (cells i ∩ A)) → genRelative .count (cells i ∩ A) ψ φ)
    (forall_congr' fun _ ↦ imp_congr_left Measure.count_ne_zero_iff.symm)

end Count

/-! ### People have a hard time finding CMU ((65), pp. 32–33, after Thomason)

Twenty people, five of whom sought the university: four found it with difficulty, one with
ease. The alternatives, the levels of difficulty of the search, restrict the reference class to
the seekers, so the generic holds with no majority among people. -/

section Examples

abbrev soughtCMU : Set (Fin 20) := {x | x.val < 5}
abbrev hardTime : Set (Fin 20) := {x | x.val < 4}

example : gen .count soughtCMU univ hardTime ∧ ¬ gen .count univ univ hardTime := by
  decide

/-! ### Mammals bear live young; mammals are not female ((66), p. 34; (192), p. 99)

Twenty mammals, eight of which procreate: six bear live young, two lay eggs. Eleven are
female, among them every procreator. Relativized to the forms of procreation, the first
generic is true though bearers are a minority of all mammals, and it holds in each cell of the
sex partition that has procreators. The second clears the first definition on the female majority
alone and fails the final one, since the male cell contains no female. The adverb *usually*
carries the same threshold and answers only to temporal partitions (§6.2.3, pp. 141–142), so
"usually female" stays true. -/

abbrev procreates : Set (Fin 20) := {x | x.val < 8}
abbrev bearsLive : Set (Fin 20) := {x | x.val < 6}
abbrev female : Set (Fin 20) := {x | x.val < 11}

/-- The sex partition divides the females from the males. -/
abbrev sexCell (b : Bool) : Set (Fin 20) := {x | decide (x.val < 11) = b}

example : gen .count procreates univ bearsLive ∧ ¬ gen .count univ univ bearsLive ∧
    genSalient .count procreates sexCell univ bearsLive := by
  decide

-- (192b), p. 99
theorem female_not_genSalient :
    gen .count univ univ female ∧ ¬ genSalient .count univ sexCell univ female := by
  decide

/-! ### Relative readings (§3.4.3, pp. 58–59; (179), p. 94)

Twenty people, fifteen of them weightlifters: the five Bulgarians all lift, two of them
well; one of the ten other lifters is good. A Bulgarian lifter is likelier than an
arbitrary one to be good, though no majority of Bulgarian lifters is. In the soccer
variant the lousy players concentrate outside Brazil, and the relative reading rejects
"Brazilians are lousy soccer players" while accepting the sentence with its scope intersected
with the restrictor. Of twenty women five are Dutch and one of those is the only queen: a Dutch
woman is likelier than an arbitrary one to be a queen, and the generic still fails, since a
partition by region has a cell of Dutch women without a queen. -/

abbrev bulgarian : Set (Fin 20) := {x | x.val < 5}
abbrev lifter : Set (Fin 20) := {x | x.val < 15}
abbrev goodLifter : Set (Fin 20) := {x | x.val < 2 ∨ x.val = 5}

example : genRelative .count lifter bulgarian goodLifter ∧
    ¬ gen .count lifter bulgarian goodLifter := by
  decide

abbrev brazilian : Set (Fin 20) := {x | x.val < 5}
abbrev soccerPlayer : Set (Fin 20) := {x | x.val < 15}
abbrev lousy : Set (Fin 20) := {x | x.val = 0 ∨ (5 ≤ x.val ∧ x.val < 13)}

-- (130), p. 59
theorem not_conservative_genRelative :
    ¬ (genRelative (.count : Measure (Fin 20)) soccerPlayer).Conservative :=
  fun h ↦ absurd (h brazilian lousy) (by decide)

abbrev dutch : Set (Fin 20) := {x | x.val < 5}
abbrev queen : Set (Fin 20) := {x | x.val = 0}

/-- The capital region and the rest of the country. -/
abbrev regionCell (b : Bool) : Set (Fin 20) := {x | decide (x.val % 2 = 0) = b}

example : genRelative .count univ dutch queen ∧
    ¬ genRelativeSalient .count univ regionCell dutch queen := by
  decide

end Examples

end Cohen1999
