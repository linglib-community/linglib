module

public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Core.Probability.UniformOn
public import Linglib.Languages.English.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Semantics.Questions.Partition.OfProps

/-!
# Van Rooy (2003): Negative polarity items in questions

A negative polarity item weakens the positive answer of the question it stands in, most often by
widening a domain. A questioner uses one when it makes the question stronger, and the strength of
a question is its entropy under the prior of the questioner, the average informativity of its
answers. The strength of an assertion is fixed by entailment, whereas the strength of a question
varies with what the questioner expects.

For a polar question the entropy is the binary entropy of the probability of the positive answer.
Weakening the positive answer therefore [raises the entropy exactly when it makes that answer more
likely without carrying it past the old negative answer](##VanRooy2003a.entropy_polar_lt_iff).
This holds only if the negative answer was the more likely one, which is the generalization of
Borkin and of Krifka, and [it fails for every weakening when the positive answer was at least as
likely](##VanRooy2003a.not_entropy_polar_lt_of_half_le). In that case [a positive polarity
item, which strengthens the positive answer, can raise the
entropy](##VanRooy2003a.entropy_polar_lt_iff_of_superset). A question that is settled becomes
[stronger whenever weakening leaves it open](##VanRooy2003a.entropy_polar_lt_of_measure_eq_zero),
which is the comparison of Kadmon and Landman. In the subject position of a constituent question
the item widens the domain of the wh-phrase, the wider question is finer, and [its entropy is at
least as high under every prior](##VanRooy2003a.entropy_ofProps_image_mono).

A minimizer such as *lift a finger* presupposes, as *even* does, that the question is settled for
each salient alternative, while the question itself must be open. Since each alternative entails
the minimal value, [every alternative is settled
negatively](##VanRooy2003a.measure_alternative_eq_zero), which is the rhetorical reading.

A question is not downward entailing in the position of the item, so the strengths of negation do
not say which items stand in one: [no class is predicted to be possible in a
question](##VanRooy2003a.question_notMem_region), where *ever* and *lift a finger* both stand.

## Main definitions

* `VanRooy2003a.entropy`: the informativity value of a partition question under a prior.

## Implementation notes

* A question is a partition of the worlds, a `Setoid`, and worlds are finite and discrete, as in
  the paper's examples. Entropy is taken with the natural logarithm; the comparisons do not
  depend on the base.
* The presupposition of an *even*-type item is stated as a hypothesis on the prior: each
  alternative has probability zero or one.

## TODO

* An item in the predicate position of a constituent question weakens the predicate for each
  individual of the domain. With independent individuals the entropy of the question is the sum
  of the binary entropies of the individuals, and the polar comparison applies to each summand.
* Entropy is a case of utility. When the decision problem is to find the true answer to a
  question finer than the one asked, the expected utility value of a question is its entropy.
  The value of information of negative entropy is not yet in the library.

## References

* [van-rooy-2003a]
* [borkin-1971]
* [krifka-1995a]
* [kadmon-landman-1990]
* [shannon-1948]
-/

@[expose] public section

namespace VanRooy2003a

open MeasureTheory ProbabilityTheory InformationTheory Real

/-! ### Binary entropy on the two sides of one half -/

-- Raising a probability raises its binary entropy exactly when the new probability is still
-- below the complement of the old one.
private theorem binEntropy_lt_binEntropy_iff {p p' : ℝ} (hp : 0 ≤ p) (hpp : p ≤ p')
    (hp' : p' ≤ 1) : binEntropy p < binEntropy p' ↔ p < p' ∧ p + p' < 1 := by
  have hm := binEntropy_strictMonoOn
  rcases le_total p' 2⁻¹ with h | h
  · rw [hm.lt_iff_lt ⟨hp, hpp.trans h⟩ ⟨hp.trans hpp, h⟩]
    exact ⟨fun hlt ↦ ⟨hlt, by linarith⟩, fun h ↦ h.1⟩
  · rw [← binEntropy_one_sub p']
    rcases le_total p 2⁻¹ with hq | hq
    · rw [hm.lt_iff_lt ⟨hp, hq⟩ ⟨by linarith, by linarith⟩]
      exact ⟨fun hlt ↦ ⟨by linarith, by linarith⟩, fun h ↦ by linarith [h.2]⟩
    · rw [← binEntropy_one_sub p,
        hm.lt_iff_lt ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩]
      exact ⟨fun hlt ↦ absurd hlt (by linarith), fun h ↦ by linarith [h.2]⟩

-- Lowering a probability raises its binary entropy exactly when the new probability is still
-- above the complement of the old one.
private theorem binEntropy_lt_binEntropy_iff_of_ge {p p' : ℝ} (hp' : 0 ≤ p') (hpp : p' ≤ p)
    (hp : p ≤ 1) : binEntropy p < binEntropy p' ↔ p' < p ∧ 1 < p + p' := by
  rw [← binEntropy_one_sub p, ← binEntropy_one_sub p',
    binEntropy_lt_binEntropy_iff (by linarith) (by linarith) (by linarith)]
  exact ⟨fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩⟩

/-! ### The entropy of a question -/

variable {W : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]

/-- The informativity value of a question under a prior is the entropy of its answer: the
average, over the answers, of the informativity `-log P(q)` of each. -/
noncomputable def entropy (μ : Measure W) (Q : Setoid W) : ℝ := H[Quotient.mk Q ; μ]

variable (μ : Measure W) {q q' : Set W}

omit [DiscreteMeasurableSpace W] in
theorem entropy_nonneg (Q : Setoid W) : 0 ≤ entropy μ Q := InformationTheory.entropy_nonneg _ _

variable [IsProbabilityMeasure μ]

-- A finer question has at least the entropy of a coarser one, under the same prior.
theorem entropy_anti [Finite W] : Antitone (entropy μ) := fun Q Q' h ↦ by
  cases nonempty_fintype (Quotient Q')
  cases nonempty_fintype (Quotient Q)
  have hc : (Quotient.mk Q' : W → Quotient Q') = Quotient.map' id h ∘ Quotient.mk Q := rfl
  rw [entropy, hc]
  exact entropy_comp_le μ .of_discrete _

/-- Widening the domain of the wh-phrase never lowers the entropy of a constituent question. -/
theorem entropy_ofProps_image_mono [Finite W] {E : Type*} (P : E → Set W) {D D' : Set E}
    (h : D ⊆ D') :
    entropy μ (Setoid.ofProps (P '' D)) ≤ entropy μ (Setoid.ofProps (P '' D')) :=
  entropy_anti μ (Setoid.ofProps_anti (Set.image_mono h))

/-- The entropy of a polar question is the binary entropy of the probability of its positive
answer. -/
theorem entropy_polar (q : Set W) : entropy μ (Setoid.polar q) = binEntropy (μ.real q) := by
  rw [← entropy_mem .of_discrete, entropy,
    ← entropy_comp_of_injective μ .of_discrete .of_discrete
      (Setoid.kerLift_injective (· ∈ q))]
  rfl

/-! ### Polar questions -/

/-- Weakening the positive answer of a polar question raises the entropy of the question exactly
when it makes that answer more likely and no more likely than the old negative answer was. -/
theorem entropy_polar_lt_iff (h : q ⊆ q') :
    entropy μ (Setoid.polar q) < entropy μ (Setoid.polar q') ↔
      μ.real q < μ.real q' ∧ μ.real q + μ.real q' < 1 := by
  rw [entropy_polar, entropy_polar, binEntropy_lt_binEntropy_iff measureReal_nonneg
    (measureReal_mono h) measureReal_le_one]

-- Strengthening the positive answer of a polar question raises the entropy of the question
-- exactly when it makes that answer less likely and no less likely than the old negative answer
-- was.
theorem entropy_polar_lt_iff_of_superset (h : q' ⊆ q) :
    entropy μ (Setoid.polar q) < entropy μ (Setoid.polar q') ↔
      μ.real q' < μ.real q ∧ 1 < μ.real q + μ.real q' := by
  rw [entropy_polar, entropy_polar, binEntropy_lt_binEntropy_iff_of_ge measureReal_nonneg
    (measureReal_mono h) measureReal_le_one]

/-- When the positive answer is at least as likely as the negative one, no weakening of it raises
the entropy of the question. -/
theorem not_entropy_polar_lt_of_half_le (h : q ⊆ q') (hq : 2⁻¹ ≤ μ.real q) :
    ¬ entropy μ (Setoid.polar q) < entropy μ (Setoid.polar q') := fun hlt ↦ by
  have := (entropy_polar_lt_iff μ h).1 hlt
  linarith [this.1, this.2]

-- A settled question has no entropy.
theorem entropy_polar_of_measure_eq_zero (hq : μ q = 0) : entropy μ (Setoid.polar q) = 0 := by
  simp [entropy_polar, measureReal_def, hq]

-- A question settled in the negative becomes stronger under any weakening that leaves it
-- open.
theorem entropy_polar_lt_of_measure_eq_zero (hq : μ q = 0) (h0 : μ q' ≠ 0) (h1 : μ q' ≠ 1) :
    entropy μ (Setoid.polar q) < entropy μ (Setoid.polar q') := by
  rw [entropy_polar_of_measure_eq_zero μ hq, entropy_polar]
  refine binEntropy_pos (ENNReal.toReal_pos h0 (measure_ne_top μ q'))
    (lt_of_le_of_ne measureReal_le_one fun h ↦ h1 ?_)
  rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h

/-! ### Minimizers and the rhetorical reading -/

omit [DiscreteMeasurableSpace W] in
/-- A minimizer presupposes that the question is settled for each alternative, and the question
it stands in is open. Since each alternative entails the minimal value, each is settled in the
negative. -/
theorem measure_alternative_eq_zero {ι : Type*} {alt : ι → Set W} {qmin : Set W}
    (hsub : ∀ x, alt x ⊆ qmin) (hsettled : ∀ x, μ (alt x) = 0 ∨ μ (alt x) = 1)
    (hopen : μ qmin ≠ 1) (x : ι) : μ (alt x) = 0 :=
  (hsettled x).resolve_right fun h ↦
    hopen (le_antisymm prob_le_one (h ▸ measure_mono (hsub x)))

/-! ### A questioner with four equally likely worlds

One more world added to the positive answer raises the entropy of the question when the answer
had one world of the four, and lowers it when the answer had two. -/

section Example

private theorem real_singleton (i : Fin 4) :
    (uniformOn (Set.univ : Set (Fin 4))).real {i} = 4⁻¹ := by
  simp [uniformOn_univ_real_singleton]

private theorem real_pair : (uniformOn (Set.univ : Set (Fin 4))).real {0, 1} = 2⁻¹ := by
  rw [Set.insert_eq, measureReal_union (by simp) .of_discrete, real_singleton, real_singleton]
  norm_num

private theorem real_triple : (uniformOn (Set.univ : Set (Fin 4))).real {0, 1, 2} = 3 / 4 := by
  rw [Set.insert_eq, measureReal_union (by simp) .of_discrete, real_singleton,
    show ({1, 2} : Set (Fin 4)) = {1} ∪ {2} from Set.insert_eq _ _,
    measureReal_union (by simp) .of_discrete, real_singleton, real_singleton]
  norm_num

example : entropy (uniformOn Set.univ) (Setoid.polar ({0} : Set (Fin 4))) <
    entropy (uniformOn Set.univ) (Setoid.polar ({0, 1} : Set (Fin 4))) := by
  rw [entropy_polar_lt_iff _ (by simp), real_singleton, real_pair]
  norm_num

example : ¬ entropy (uniformOn Set.univ) (Setoid.polar ({0, 1} : Set (Fin 4))) <
    entropy (uniformOn Set.univ) (Setoid.polar ({0, 1, 2} : Set (Fin 4))) :=
  not_entropy_polar_lt_of_half_le _ (by simp [Set.insert_subset_iff]) real_pair.ge

example : entropy (uniformOn Set.univ) (Setoid.polar ({0, 1, 2} : Set (Fin 4))) <
    entropy (uniformOn Set.univ) (Setoid.polar ({0, 1} : Set (Fin 4))) := by
  rw [entropy_polar_lt_iff_of_superset _ (by simp [Set.insert_subset_iff]), real_pair,
    real_triple]
  norm_num

end Example

/-! ### Questions and the strengths of negation

A question is downward entailing only in the domain of its wh-phrase, so the strengths of negation
give it no profile, and no class is predicted to be possible in one. -/

-- §3.1
theorem question_notMem_region (k : PolarityItem.Distribution) :
    PolarityItem.LicensingContext.polarQuestion ∉ PolarityItem.Distribution.region k ∧
      PolarityItem.LicensingContext.constituentQuestion ∉ PolarityItem.Distribution.region k := by
  simp [PolarityItem.Distribution.region, PolarityItem.LicensingContext.Admits,
    PolarityItem.LicensingContext.negativity]

-- (8b), (9b), (12)
theorem mem_attested :
    PolarityItem.LicensingContext.polarQuestion ∈ English.PolarityItems.ever.attested ∧
      PolarityItem.LicensingContext.polarQuestion ∈ English.PolarityItems.liftAFinger.attested := by
  decide

end VanRooy2003a
