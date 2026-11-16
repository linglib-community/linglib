module

public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Quantification.Counting

/-!
# Cohen (1999): Think Generic!

Cohen's inductivist semantics makes a generic sentence a probability judgment within the
alternatives to its scope: on the absolute reading the probability of the scope given the
restrictor exceeds one half, on the relative reading it exceeds the probability of the scope. The
absolute reading is [conservative](##Cohen1999.conservative_freq) and, on a uniform measure,
[is *most*](##Cohen1999.gen_uniformOn_univ); the relative one is
[positive correlation](##Cohen1999.genRelative_iff_mul_lt), hence symmetric and not conservative.
Unrestricted homogeneity [admits only the exceptionless cases](##Cohen1999.homogeneous_iff), so
the final truth conditions ask for the threshold in the cells of salient partitions, which
[strengthens the absolute reading](##Cohen1999.gen_of_salient).

## Implementation notes

* Page and definition numbers follow the 1996 Carnegie Mellon dissertation, whose independent and
  dependent readings are the absolute and relative readings here.
* The alternatives and the salient cells both enter by conditioning the measure: with $A$ the
  disjunction of the alternatives, $P(\phi \mid \psi \wedge A)$ is `μ[|A][φ | ψ]`, and the finite
  models are the uniform measures `uniformOn A`. The alternatives to the restrictor and to the
  scope are conjoined into `A`.
* A conditional probability on a null reference class is undefined in the source and `0` here, so
  **gen** is false there, and a salient cell with a null reference class imposes no condition.

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

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α)

/-- A frequency adverb puts its lexical requirement `R` on the conditional probability of the
scope `φ` given the restrictor `ψ` (definition 10, p. 138). -/
def freq (R : ℝ≥0∞ → Prop) : Det α := fun ψ φ ↦ R (μ[φ | ψ])

/-- The generic quantifier on its absolute reading (definition 1, p. 39) holds when the
conditional probability of the scope given the restrictor exceeds one half. -/
def gen : Det α := freq μ (2⁻¹ < ·)

/-- The relative reading (definition 3, p. 60) holds when the restrictor raises the probability of
the scope. -/
def genRelative : Det α := fun ψ φ ↦ μ φ < μ[φ | ψ]

/-- The final truth conditions (definition 5, p. 90; definition 11, p. 142) ask for a reading `Q`
within every salient cell whose reference class is not null. -/
def salient (Q : Measure α → Det α) (cells : ι → Set α) : Det α := fun ψ φ ↦
  ∀ i, μ (cells i ∩ ψ) ≠ 0 → Q μ[|cells i] ψ φ

/-- A reference class `ψ` is homogeneous with respect to `φ` (definition 4, pp. 88–89, after
Salmon) when no subclass of positive probability changes the probability of `φ`. -/
def Homogeneous (ψ φ : Set α) : Prop :=
  ∀ ω, MeasurableSet ω → μ (ψ ∩ ω) ≠ 0 → μ[φ | ψ ∩ ω] = μ[φ | ψ]

variable {μ} {A ψ φ ω : Set α} {cells : ι → Set α} {R : ℝ≥0∞ → Prop}

/-! ### The absolute reading -/

theorem scopeMonotone_freq (hR : Monotone R) : (freq μ R).ScopeMonotone :=
  fun _ _ _ h ↦ hR (measure_mono h)

theorem scopeMonotone_gen : (gen μ).ScopeMonotone :=
  scopeMonotone_freq fun _ _ h h' ↦ h'.trans_le h

theorem freq_inter_left (hψ : MeasurableSet ψ) : freq μ R ψ (ψ ∩ φ) ↔ freq μ R ψ φ := by
  rw [freq, freq, cond_inter_self hψ]

/-- Whatever its requirement, a frequency adverb on the absolute reading is conservative: the
scope matters only within the restrictor (§3.4.2, p. 57; §6.2.2, p. 139). -/
theorem conservative_freq [DiscreteMeasurableSpace α] (R : ℝ≥0∞ → Prop) :
    (freq μ R).Conservative :=
  fun _ _ ↦ (freq_inter_left .of_discrete).symm

theorem conservative_gen [DiscreteMeasurableSpace α] : (gen μ).Conservative :=
  conservative_freq _

section IsFiniteMeasure

variable [IsFiniteMeasure μ]

theorem freq_cond (hω : MeasurableSet ω) (hψ : MeasurableSet ψ) :
    freq μ[|ω] R ψ φ ↔ freq μ R (ω ∩ ψ) φ := by
  rw [freq, freq, cond_cond_eq_cond_inter hω hψ]

theorem gen_cond (hω : MeasurableSet ω) (hψ : MeasurableSet ψ) :
    gen μ[|ω] ψ φ ↔ gen μ (ω ∩ ψ) φ :=
  freq_cond hω hψ

theorem gen_iff_lt (hψ : MeasurableSet ψ) : gen μ ψ φ ↔ μ ψ < 2 * μ (ψ ∩ φ) := by
  rw [gen, freq, lt_cond_iff_mul_lt hψ, ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (by simp) (by simp), mul_comm]

-- §5.7, pp. 131–132
theorem gen_cond_self (hψ : MeasurableSet ψ) (hφ : MeasurableSet φ) :
    gen μ[|φ] ψ φ ↔ μ (φ ∩ ψ) ≠ 0 := by
  rw [gen_cond hφ hψ, gen_iff_lt (hφ.inter hψ), inter_right_comm, inter_self, two_mul]
  exact ⟨fun h h0 ↦ by simp [h0] at h, ENNReal.lt_add_right (measure_ne_top _ _)⟩

/-! ### The relative reading -/

/-- The relative reading is positive correlation of restrictor and scope. -/
theorem genRelative_iff_mul_lt (hψ : MeasurableSet ψ) :
    genRelative μ ψ φ ↔ μ φ * μ ψ < μ (ψ ∩ φ) :=
  lt_cond_iff_mul_lt hψ

-- (124b), p. 57
theorem genRelative_comm (hψ : MeasurableSet ψ) (hφ : MeasurableSet φ) :
    genRelative μ ψ φ ↔ genRelative μ φ ψ := by
  rw [genRelative_iff_mul_lt hψ, genRelative_iff_mul_lt hφ, mul_comm, inter_comm]

theorem genRelative_cond_iff_mul_lt (hA : MeasurableSet A) (hψ : MeasurableSet ψ) :
    genRelative μ[|A] ψ φ ↔ μ (A ∩ φ) * μ (A ∩ ψ) < μ (A ∩ ψ ∩ φ) * μ A := by
  rw [genRelative, cond_cond_eq_cond_inter hA hψ, lt_cond_iff_mul_lt (hA.inter hψ), cond_apply hA]
  rcases eq_or_ne (μ A) 0 with h0 | h0
  · simp [h0, measure_mono_null (inter_subset_left : A ∩ ψ ⊆ A) h0,
      measure_mono_null (inter_subset_left.trans inter_subset_left : A ∩ ψ ∩ φ ⊆ A) h0]
  · rw [mul_assoc, ← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (.inl h0) (.inl (measure_ne_top _ _))]

-- (128), p. 58
theorem genRelative_inter_left_iff [IsProbabilityMeasure μ] (hψ : MeasurableSet ψ) :
    genRelative μ ψ (ψ ∩ φ) ↔ μ (ψ ∩ φ) ≠ 0 ∧ μ ψ < 1 := by
  rw [genRelative, cond_inter_self hψ, lt_cond_iff_mul_lt hψ]
  rcases eq_or_ne (μ (ψ ∩ φ)) 0 with h0 | h0
  · simp [h0]
  · conv_lhs => rhs; rw [← mul_one (μ (ψ ∩ φ))]
    rw [ENNReal.mul_lt_mul_iff_right h0 (measure_ne_top _ _), and_iff_right h0]

/-! ### Homogeneity -/

/-- Unrestricted homogeneity holds only in the two exceptionless cases, since the scope itself
cuts a subclass out of any mixed reference class (p. 89). -/
theorem homogeneous_iff (hψ : MeasurableSet ψ) (hφ : MeasurableSet φ) :
    Homogeneous μ ψ φ ↔ μ[φ | ψ] = 0 ∨ μ[φ | ψ] = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases h0 : μ (ψ ∩ φ) = 0
    · exact .inl (by rw [cond_apply hψ, h0, mul_zero])
    · rw [← h φ hφ h0]
      exact .inr ((cond_apply_eq_one_iff (hψ.inter hφ) hφ h0).2 inter_subset_right.eventuallyLE)
  · rintro (h | h) ω hω hc
    · rw [h, cond_apply_eq_zero_iff (hψ.inter hω)]
      exact inter_subset_left.eventuallyLE.trans ((cond_apply_eq_zero_iff hψ).1 h)
    · have hc' : μ ψ ≠ 0 := fun h0 ↦ hc (measure_mono_null inter_subset_left h0)
      rw [h, cond_apply_eq_one_iff (hψ.inter hω) hφ hc]
      exact inter_subset_left.eventuallyLE.trans ((cond_apply_eq_one_iff hψ hφ hc').1 h)

/-! ### Salient partitions -/

/-- A generic true within every cell of a partition of its restrictor is true on the absolute
reading: the final truth conditions strengthen the first (p. 90). -/
theorem gen_of_salient [Countable ι] (hd : Pairwise (Disjoint on cells))
    (hm : ∀ i, MeasurableSet (cells i)) (hcover : ψ ⊆ ⋃ i, cells i) (hψ : MeasurableSet ψ)
    (hφ : MeasurableSet φ) (hc : μ ψ ≠ 0) (h : salient μ gen cells ψ φ) : gen μ ψ φ := by
  have key : ∀ t, MeasurableSet t → t ⊆ ψ → μ t = ∑' i, μ (t ∩ cells i) := fun t ht hsub ↦ by
    have h₁ := Measure.restrict_iUnion_apply (μ := μ) hd hm ht
    simp only [Measure.restrict_apply ht] at h₁
    rwa [inter_eq_left.2 (hsub.trans hcover)] at h₁
  have cell : ∀ j, μ (ψ ∩ cells j) ≠ 0 → μ (ψ ∩ cells j) < 2 * μ (ψ ∩ φ ∩ cells j) :=
    fun j hj ↦ by
      rw [inter_comm] at hj
      have h₁ := (gen_iff_lt ((hm j).inter hψ)).1 ((gen_cond (hm j) hψ).1 (h j hj))
      rwa [inter_comm (cells j) ψ, inter_right_comm] at h₁
  obtain ⟨i, hi⟩ : ∃ i, μ (ψ ∩ cells i) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (by rw [key _ hψ subset_rfl]; simp [hall])
  rw [gen_iff_lt hψ, key _ hψ subset_rfl, key _ (hψ.inter hφ) inter_subset_left,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_lt_tsum (i := i) ?_ (fun j ↦ ?_) (cell i hi)
  · rw [← key _ hψ subset_rfl]
    exact measure_ne_top _ _
  · by_cases hj : μ (ψ ∩ cells j) = 0
    · simp [hj]
    · exact (cell j hj).le

/-! ### Frequency adverbs

*Never* and *always* (p. 137) ask that almost all of the restrictor lie outside the scope and
inside it, and *sometimes* denies the first. -/

theorem freq_eq_zero_iff (hψ : MeasurableSet ψ) : freq μ (· = 0) ψ φ ↔ ψ ≤ᵐ[μ] φᶜ :=
  cond_apply_eq_zero_iff hψ

theorem freq_pos_iff (hψ : MeasurableSet ψ) : freq μ (0 < ·) ψ φ ↔ ¬ ψ ≤ᵐ[μ] φᶜ :=
  pos_iff_ne_zero.trans (cond_apply_eq_zero_iff hψ).not

theorem freq_eq_one_iff (hψ : MeasurableSet ψ) (hφ : MeasurableSet φ) (hc : μ ψ ≠ 0) :
    freq μ (· = 1) ψ φ ↔ ψ ≤ᵐ[μ] φ :=
  cond_apply_eq_one_iff hψ hφ hc

end IsFiniteMeasure

/-! ### Uniform measures

On the uniform measure over finitely many alternatives the probabilities are proportions, and the
classical determiners reappear, restricted to the alternatives. -/

section UniformOn

variable [MeasurableSingletonClass α]

section Finite

variable [Finite α]

-- p. 137
theorem freq_uniformOn_eq_zero_iff : freq (uniformOn A) (· = 0) ψ φ ↔ no (A ∩ ψ) φ :=
  (freq_eq_zero_iff .of_discrete).trans (ae_le_uniformOn_iff (toFinite _))

theorem freq_uniformOn_pos_iff : freq (uniformOn A) (0 < ·) ψ φ ↔ Det.some (A ∩ ψ) φ :=
  (freq_pos_iff .of_discrete).trans <|
    (ae_le_uniformOn_iff (toFinite _)).not.trans no_iff_not_some.not_left

theorem freq_uniformOn_eq_one_iff (h : (A ∩ ψ).Nonempty) :
    freq (uniformOn A) (· = 1) ψ φ ↔ every (A ∩ ψ) φ :=
  (freq_eq_one_iff .of_discrete .of_discrete ((uniformOn_ne_zero_iff (toFinite _)).2 h)).trans
    (ae_le_uniformOn_iff (toFinite _))

theorem gen_uniformOn_iff_most : gen (uniformOn A) ψ φ ↔ most (A ∩ ψ) φ := by
  have h := ncard_inter_add_ncard_sdiff_eq_ncard (A ∩ ψ) φ (toFinite _)
  rw [uniformOn, gen_cond .of_discrete .of_discrete, gen_iff_lt .of_discrete,
    Measure.count_apply .of_discrete, Measure.count_apply .of_discrete,
    ← (toFinite (A ∩ ψ)).cast_ncard_eq, ← (toFinite (A ∩ ψ ∩ φ)).cast_ncard_eq, most_apply]
  simp only [ENat.toENNReal_coe]
  norm_cast
  omega

/-- On the uniform measure of a finite universe, where the alternatives exclude nothing, the
absolute reading is the determiner *most*. -/
theorem gen_uniformOn_univ : gen (uniformOn (univ : Set α)) = most :=
  funext fun ψ ↦ funext fun φ ↦ propext (by rw [gen_uniformOn_iff_most, univ_inter])

-- p. 89
theorem homogeneous_uniformOn_iff :
    Homogeneous (uniformOn A) ψ φ ↔ no (A ∩ ψ) φ ∨ every (A ∩ ψ) φ := by
  rw [homogeneous_iff .of_discrete .of_discrete]
  rcases (A ∩ ψ).eq_empty_or_nonempty with h | h
  · exact iff_of_true (.inl (freq_uniformOn_eq_zero_iff.2 (by simp [h, no])))
      (.inl (by simp [h, no]))
  · exact or_congr freq_uniformOn_eq_zero_iff (freq_uniformOn_eq_one_iff h)

theorem salient_uniformOn_iff (Q : Measure α → Det α) :
    salient (uniformOn A) Q cells ψ φ ↔
      ∀ i, (∃ x, x ∈ A ∩ (cells i ∩ ψ)) → Q (uniformOn (A ∩ cells i)) ψ φ := by
  unfold salient
  exact forall_congr' fun i ↦ by
    rw [uniformOn_cond (toFinite _) .of_discrete, uniformOn_ne_zero_iff (toFinite _)]
    rfl

end Finite

variable [Fintype α] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ ψ)] [DecidablePred (· ∈ φ)]

instance : Decidable (gen (uniformOn A) ψ φ) := decidable_of_iff _ gen_uniformOn_iff_most.symm

private theorem count_eq_card (s : Set α) [DecidablePred (· ∈ s)] :
    Measure.count s = #{x | x ∈ s} := by
  rw [← Measure.count_apply_finset]
  congr 1
  ext
  simp

theorem genRelative_uniformOn_iff_card :
    genRelative (uniformOn A) ψ φ ↔
      #{x | x ∈ A ∩ φ} * #{x | x ∈ A ∩ ψ} < #{x | x ∈ A ∩ ψ ∩ φ} * #{x | x ∈ A} := by
  rw [uniformOn, genRelative_cond_iff_mul_lt .of_discrete .of_discrete, count_eq_card (A ∩ φ),
    count_eq_card (A ∩ ψ), count_eq_card (A ∩ ψ ∩ φ), count_eq_card A]
  norm_cast

instance : Decidable (genRelative (uniformOn A) ψ φ) :=
  decidable_of_iff _ genRelative_uniformOn_iff_card.symm

variable [Fintype ι] [∀ i, DecidablePred (· ∈ cells i)]

instance : Decidable (salient (uniformOn A) gen cells ψ φ) :=
  decidable_of_iff _ (salient_uniformOn_iff gen).symm

instance : Decidable (salient (uniformOn A) genRelative cells ψ φ) :=
  decidable_of_iff _ (salient_uniformOn_iff genRelative).symm

end UniformOn

/-! ### People have a hard time finding CMU ((65), pp. 32–33, after Thomason)

Twenty people, five of whom sought the university: four found it with difficulty, one with
ease. The alternatives, the levels of difficulty of the search, restrict the reference class to
the seekers, so the generic holds with no majority among people. -/

section Examples

abbrev soughtCMU : Set (Fin 20) := {x | x.val < 5}
abbrev hardTime : Set (Fin 20) := {x | x.val < 4}

example : gen (uniformOn soughtCMU) univ hardTime := by decide

example : ¬ gen (uniformOn univ) univ hardTime := by decide

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
abbrev sexCell (b : Bool) : Set (Fin 20) := {x | x ∈ female ↔ b}

example : gen (uniformOn procreates) univ bearsLive := by decide

example : ¬ gen (uniformOn univ) univ bearsLive := by decide

example : salient (uniformOn procreates) gen sexCell univ bearsLive := by decide

example : gen (uniformOn univ) univ female := by decide

-- (192b), p. 99
theorem female_not_salient : ¬ salient (uniformOn univ) gen sexCell univ female := by
  decide

/-! ### Relative readings (§3.4.3, pp. 58–59; (179), p. 94)

Twenty people, fifteen of them weightlifters: the five Bulgarians all lift, two of them
well; one of the ten other lifters is good. A Bulgarian lifter is likelier than an
arbitrary one to be good, though no majority of Bulgarian lifters is. Of sixteen soccer players
eight are Brazilian, one of them lousy, and six of the others are: the relative reading rejects
"Brazilians are lousy soccer players" and accepts the sentence with its scope intersected with
the restrictor. Of twenty women four are Dutch and one of those is the only queen: a Dutch
woman is likelier than an arbitrary one to be a queen, and the generic still fails, since the
Dutch women outside the capital include no queen. -/

abbrev bulgarian : Set (Fin 20) := {x | x.val < 5}
abbrev lifter : Set (Fin 20) := {x | x.val < 15}
abbrev goodLifter : Set (Fin 20) := {x | x.val < 2 ∨ x.val = 5}

example : genRelative (uniformOn lifter) bulgarian goodLifter := by decide

example : ¬ gen (uniformOn lifter) bulgarian goodLifter := by decide

abbrev brazilian : Set (Fin 20) := {x | x.val < 8}
abbrev soccerPlayer : Set (Fin 20) := {x | x.val < 16}
abbrev lousy : Set (Fin 20) := {x | x.val = 0 ∨ (8 ≤ x.val ∧ x.val < 14)}

-- (130), p. 59
theorem not_conservative_genRelative : ¬ (genRelative (uniformOn soccerPlayer)).Conservative :=
  fun h ↦ absurd (h brazilian lousy) (by decide)

abbrev dutch : Set (Fin 20) := {x | x.val < 4}
abbrev queen : Set (Fin 20) := {x | x.val = 0}
abbrev capital : Set (Fin 20) := {x | x.val < 2 ∨ x.val = 10}

/-- The partition by region divides the residents of the capital from the rest. -/
abbrev regionCell (b : Bool) : Set (Fin 20) := {x | x ∈ capital ↔ b}

example : genRelative (uniformOn univ) dutch queen := by decide

example : ¬ salient (uniformOn univ) genRelative regionCell dutch queen := by decide

end Examples

end Cohen1999
