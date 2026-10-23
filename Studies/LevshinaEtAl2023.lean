module

public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Core.Probability.Moments.Covariance
public import Linglib.Data.WordOrder.Corpus.LevshinaEtAl2023

/-!
# Levshina et al. (2023): Why We Need a Gradient Approach to Word Order

This file formalizes the corpus illustrations of [levshina-etal-2023]'s case for describing
word order by continuous measures rather than categorical labels. The paper's two measures of a
binary order are the proportion of one order and the Shannon entropy of the order in bits; the
entropy is the entropy of the Bernoulli law of the order at that proportion
(`orderEntropy_eq_binEntropy`), so it is `0` when one order is fixed and `1` at an even split,
the worked values of section 4.1.1, and among languages that put the subject first more often
than not it ranks languages in reverse of the proportion (`orderEntropy_lt_iff`). In the 31
news corpora of Figure 1 the subject precedes the object in most clauses of every language
(`subject_usually_first`). Figure 3 plots the mutual information between case marking and
syntactic role against order entropy for 30 corpora: the two covary positively over the sample
(`covariance_entropy_caseInformation_pos`), the corpus of maximal entropy, Lithuanian, has the
most informative case marking (`freest_most_case_informative`), and the corpus of minimal
entropy has none (`most_rigid_least_case_informative`). The Russian register study of section
4.1.3 is the population of its 300 annotated clauses under the uniform measure: verb–object
order is less probable in conversation than in fiction (`conversation_lt_fiction`) and equally
probable in fiction and news (`fiction_eq_news`).

## Implementation notes

* The rows are the paper's OSF datasets, generated into `Data.WordOrder.Corpus.LevshinaEtAl2023`.
  The entropies of Figure 3 are the dataset's printed values from the paper's own extraction,
  not recomputed from the counts of Figure 1, which come from a different sample of the same
  corpora.
* The claim of Figure 1 that the proportions form a continuum with no natural cut-off is a
  visual one without a statistic and is not stated as a theorem; nor is the logistic regression
  of section 4.1.3, whose descriptive content is the conditional probabilities.

## References

* [levshina-etal-2023]
-/

@[expose] public section

open Data.WordOrder.Corpus Data.WordOrder.Corpus.LevshinaEtAl2023
open InformationTheory MeasureTheory ProbabilityTheory Real unitInterval
open scoped ProbabilityTheory

namespace LevshinaEtAl2023

/-! ### Proportion and entropy of a binary order (sections 1.1 and 4.1.1) -/

section Entropy

variable (r s : SubjectObjectCounts)

/-- The proportion of clauses with the subject before the object. -/
noncomputable def proportion : ℝ := r.subjectFirst / (r.subjectFirst + r.objectFirst)

theorem proportion_mem : proportion r ∈ I :=
  ⟨by unfold proportion; positivity, div_le_one_of_le₀ (by simp) (by positivity)⟩

theorem one_half_lt_proportion_iff : 1 / 2 < proportion r ↔ r.objectFirst < r.subjectFirst := by
  unfold proportion
  obtain h | h := eq_or_ne (r.subjectFirst + r.objectFirst) 0
  · simp [Nat.add_eq_zero_iff.1 h]
  · have : (0 : ℝ) < r.subjectFirst + r.objectFirst := by exact_mod_cast Nat.pos_of_ne_zero h
    rw [lt_div_iff₀ this, ← Nat.cast_lt (α := ℝ)]
    constructor <;> intro <;> linarith

/-- The law of subject–object order in a language's corpus, which puts the subject first with
the observed proportion. -/
noncomputable def orderLaw : Measure SubjectObject :=
  Ber(.subjectFirst, .objectFirst, ⟨proportion r, proportion_mem r⟩)

/-- The paper's word-order entropy, the Shannon entropy of the order in bits. -/
noncomputable def orderEntropy : ℝ := Hm[orderLaw r] / log 2

theorem orderEntropy_eq_binEntropy : orderEntropy r = binEntropy (proportion r) / log 2 := by
  rw [orderEntropy, orderLaw, measureEntropy_bernoulliMeasure (by decide)]

theorem orderEntropy_of_fixed (h : r.subjectFirst = 0 ∨ r.objectFirst = 0) :
    orderEntropy r = 0 := by
  rw [orderEntropy_eq_binEntropy, binEntropy_eq_zero.2, zero_div]
  rcases h with h | h
  · simp [proportion, h]
  · by_cases h0 : r.subjectFirst = 0 <;> simp [proportion, h, h0]

theorem orderEntropy_of_even (h : r.subjectFirst = r.objectFirst) (h0 : r.subjectFirst ≠ 0) :
    orderEntropy r = 1 := by
  have : proportion r = 2⁻¹ := by
    rw [proportion, ← h]
    field_simp
    ring
  rw [orderEntropy_eq_binEntropy, this, binEntropy_two_inv, div_self (log_pos one_lt_two).ne']

theorem orderEntropy_lt_iff (hr : 1 / 2 ≤ proportion r) (hs : 1 / 2 ≤ proportion s) :
    orderEntropy r < orderEntropy s ↔ proportion s < proportion r := by
  rw [orderEntropy_eq_binEntropy, orderEntropy_eq_binEntropy,
    div_lt_div_iff_of_pos_right (log_pos one_lt_two)]
  exact StrictAntiOn.lt_iff_gt binEntropy_strictAntiOn ⟨by simpa using hr, (proportion_mem r).2⟩
    ⟨by simpa using hs, (proportion_mem s).2⟩

end Entropy

/-! ### The subject–object proportions of Figure 1 -/

theorem subject_usually_first : ∀ r ∈ subjectObjectCounts, r.objectFirst < r.subjectFirst := by
  decide

/-- Across the corpora of Figure 1, ranking by entropy is ranking by proportion reversed. -/
theorem orderEntropy_lt_iff_of_mem {r s : SubjectObjectCounts} (hr : r ∈ subjectObjectCounts)
    (hs : s ∈ subjectObjectCounts) :
    orderEntropy r < orderEntropy s ↔ proportion s < proportion r :=
  orderEntropy_lt_iff r s ((one_half_lt_proportion_iff r).2 (subject_usually_first r hr)).le
    ((one_half_lt_proportion_iff s).2 (subject_usually_first s hs)).le

/-! ### Case marking against order entropy (Figure 3) -/

/-- The corpora of Figure 3. -/
abbrev Corpus := Fin subjectObjectStatistics.length

instance : Nonempty Corpus := ⟨⟨0, by decide⟩⟩

/-- The printed statistics of a corpus. -/
def statistics (i : Corpus) : SubjectObjectStatistics := subjectObjectStatistics.get i

/-- The entropy of subject–object order in a corpus, in bits. -/
noncomputable def entropy (i : Corpus) : ℝ := (statistics i).entropy1000 / 1000

/-- The mutual information between case marking and syntactic role in a corpus, in bits. -/
noncomputable def caseInformation (i : Corpus) : ℝ :=
  (statistics i).caseMutualInformation1000 / 1000

theorem covariance_entropy_caseInformation_pos :
    0 < cov[entropy, caseInformation; uniformOn Set.univ] := by
  rw [covariance_uniformOn_univ_pos_iff]
  have h : (∑ i, (statistics i).entropy1000) * (∑ i, (statistics i).caseMutualInformation1000)
      < Fintype.card Corpus
        * ∑ i, (statistics i).entropy1000 * (statistics i).caseMutualInformation1000 := by
    decide
  have h' := (Nat.cast_lt (α := ℝ)).2 h
  push_cast at h'
  simp only [entropy, caseInformation, div_mul_div_comm, ← Finset.sum_div]
  rw [mul_div_assoc']
  exact div_lt_div_of_pos_right h' (by norm_num)

theorem freest_most_case_informative :
    ∃ i, (statistics i).language = "Lithuanian" ∧ (∀ j, entropy j ≤ entropy i)
      ∧ ∀ j, caseInformation j ≤ caseInformation i := by
  have : ∃ i, (statistics i).language = "Lithuanian"
      ∧ (∀ j, (statistics j).entropy1000 ≤ (statistics i).entropy1000)
      ∧ ∀ j, (statistics j).caseMutualInformation1000
          ≤ (statistics i).caseMutualInformation1000 := by
    decide +kernel
  obtain ⟨i, hi, he, hm⟩ := this
  exact ⟨i, hi, fun j ↦ by unfold entropy; gcongr; exact he j,
    fun j ↦ by unfold caseInformation; gcongr; exact hm j⟩

theorem most_rigid_least_case_informative :
    ∃ i, (∀ j, entropy i ≤ entropy j) ∧ caseInformation i = 0 := by
  have : ∃ i, (∀ j, (statistics i).entropy1000 ≤ (statistics j).entropy1000)
      ∧ (statistics i).caseMutualInformation1000 = 0 := by
    decide +kernel
  obtain ⟨i, he, hm⟩ := this
  exact ⟨i, fun j ↦ by unfold entropy; gcongr; exact he j, by simp [caseInformation, hm]⟩

/-! ### Register and modality in Russian (section 4.1.3) -/

/-- The annotated clauses, as a population. -/
abbrev ClauseIndex := Fin clauses.length

/-- The order of object and verb in a clause. -/
def order (i : ClauseIndex) : ObjectVerb := (clauses.get i).order

/-- The text type of a clause. -/
def textType (i : ClauseIndex) : TextType := (clauses.get i).textType

/-- The probability of verb–object order in a text type, under the uniform measure on the
clauses. -/
noncomputable def verbObjectProbability (t : TextType) : ℝ :=
  (uniformOn Set.univ)[|textType ⁻¹' {t}].real (order ⁻¹' {.verbFirst})

-- The printed counts: 61 object-first clauses in conversation, 17 each in fiction and news.
example : (clauses.filter fun c ↦ c.textType = .conversation ∧ c.order = .objectFirst).length = 61
    ∧ (clauses.filter fun c ↦ c.textType = .fiction ∧ c.order = .objectFirst).length = 17
    ∧ (clauses.filter fun c ↦ c.textType = .news ∧ c.order = .objectFirst).length = 17 := by
  decide +kernel

-- Animate objects are rare: 38 of 300, the paper's 13%.
example : (clauses.filter (·.animate)).length = 38 := by decide +kernel

private theorem ncard_setOf (p : ClauseIndex → Prop) [DecidablePred p] :
    {i | p i}.ncard = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr
  ext
  simp

theorem verbObjectProbability_eq (t : TextType) :
    verbObjectProbability t
      = (Finset.univ.filter fun i ↦ textType i = t ∧ order i = .verbFirst).card
          / (Finset.univ.filter fun i ↦ textType i = t).card := by
  have e₁ : textType ⁻¹' {t} ∩ order ⁻¹' {.verbFirst}
      = {i | textType i = t ∧ order i = .verbFirst} := rfl
  have e₂ : textType ⁻¹' {t} = {i | textType i = t} := rfl
  rw [verbObjectProbability, uniformOn_univ_cond, uniformOn_real_apply, e₁, e₂, ncard_setOf,
    ncard_setOf]

theorem card_textType (t : TextType) : (Finset.univ.filter fun i ↦ textType i = t).card = 100 := by
  revert t
  decide +kernel

private theorem card_verbFirst :
    (Finset.univ.filter fun i ↦ textType i = .conversation ∧ order i = .verbFirst).card = 39
      ∧ (Finset.univ.filter fun i ↦ textType i = .fiction ∧ order i = .verbFirst).card = 83
      ∧ (Finset.univ.filter fun i ↦ textType i = .news ∧ order i = .verbFirst).card = 83 := by
  decide +kernel

theorem verbObjectProbability_conversation : verbObjectProbability .conversation = 39 / 100 := by
  rw [verbObjectProbability_eq, card_textType, card_verbFirst.1]
  norm_num

theorem verbObjectProbability_fiction : verbObjectProbability .fiction = 83 / 100 := by
  rw [verbObjectProbability_eq, card_textType, card_verbFirst.2.1]
  norm_num

theorem verbObjectProbability_news : verbObjectProbability .news = 83 / 100 := by
  rw [verbObjectProbability_eq, card_textType, card_verbFirst.2.2]
  norm_num

theorem conversation_lt_fiction :
    verbObjectProbability .conversation < verbObjectProbability .fiction := by
  rw [verbObjectProbability_conversation, verbObjectProbability_fiction]
  norm_num

theorem fiction_eq_news : verbObjectProbability .fiction = verbObjectProbability .news := by
  rw [verbObjectProbability_fiction, verbObjectProbability_news]

end LevshinaEtAl2023
