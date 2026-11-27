module

public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.UniformOn
public import Linglib.Core.Probability.WeightOfEvidence
public import Linglib.Semantics.Embedding.Preference.ExpectedValue
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Data.Examples.ChungMascarenhas2023
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Languages.English.Auxiliaries
public import Studies.Lassiter2017

/-!
# Chung and Mascarenhas (2023): Modality, expected utility, and hypothesis testing

Necessity modals are interpreted against a finite family `R` of relevant propositions, ideals on a
deontic reading and pieces of evidence on an epistemic one. The value of a world is the number of
members of `R` true at it, and the expected value of a proposition `φ` under a prior `p` is the
average of that number over `φ`, which is `∑ i, p[|φ].real (R i)`. For a threshold `θ` and a set
of alternatives, *must* holds of `φ` when the expected value of `φ` exceeds `θ` and that of no
alternative does, *ought* when it exceeds `θ` and that of every alternative, and *might* is the
dual of *must* with the negation of `φ` as alternative.

*Must* entails *ought*, and it depends on the prior only through the prior conditioned on the
prejacent and on each alternative. With one piece of evidence and the negation of the prejacent
as alternative, it holds at some threshold if and only if the evidence has positive weight for
the prejacent.

In the miners puzzle each *ought* and *must* sentence holds on an interval of thresholds, and no
threshold verifies both *we must block neither shaft* and *if the miners are in shaft s, we must
block s*. With the paper's likelihoods for the Linda scenario, *must* holds of a conjunction and
not of its conjunct. In the inheritance scenario *Kim must marry Pat* holds at some threshold
against its negation and at none against the other people Kim might marry.

## Implementation notes

* The relevant propositions are an indexed family and not a set: the ideals that more than `k`
  miners are saved coincide for several `k` on the six-world model, and each counts.
* The operators take one measure. A sentence with an if-clause is evaluated at the measure
  conditioned on the antecedent, with the alternatives unchanged.
* Alternative sets are arguments.
* *Must* is the threshold applied to the conditional evaluative, asserted of the prejacent and
  negated of each alternative.
* The models have uniform priors. The likelihoods the paper prints are hypotheses on the
  conditioned measure.

## TODO

* The alternative analysis by differences of expected value for alternatives other than the
  negation of the prejacent.
* The Korean construction is not built from entries of the Korean language file, whose modal
  inventory has *-ya ha-* and *-to toy-* and not *-(e)ya toy-*.
* No theorem reads the rows for Linda, Jack, the cold and the helicopter. The plausibility
  requirement on the prior of the prejacent and the felicity condition on a known prejacent are
  not formalized.

## References

* [chung-mascarenhas-2023]
* [kolodny-macfarlane-2010]
* [cariani-kaufmann-kaufmann-2013]
* [kratzer-1991]
* [lassiter-2017]
* [tversky-kahneman-1983]
* [kahneman-tversky-1973]
-/

@[expose] public section

namespace ChungMascarenhas2023

open MeasureTheory ProbabilityTheory Desire Set
open scoped ENNReal Finset

variable {W ι : Type*} [Fintype ι]

/-! ### The measure function -/

/-- (7): `μ_EVAL[R]` is the measure function of the evaluative predicate, the number of relevant
propositions `R i` true at a world. -/
scoped notation "μ_EVAL[" R "]" => ∑ i, Set.indicator (M := ℝ) (R i) 1

-- (7), (11)
theorem sum_indicator_one_apply (R : ι → Set W) (w : W) [∀ i, Decidable (w ∈ R i)] :
    μ_EVAL[R] w = #{i | w ∈ R i} := by
  simp [Finset.sum_apply, Set.indicator_apply, Finset.sum_boole]

/-! ### The operators -/

section Operators

variable [MeasurableSpace W] (p : Measure W) (R : ι → Set W) (alts : Set (Set W)) (θ : ℝ)

/-- (48): *must* holds of `φ` when the thresholded conditional *if `φ`, EVAL* holds of `φ` and of
none of its alternatives, so that `φ` is the only good-enough option or explanation. -/
def must : Set (Set W) :=
  {φ | θ < expectedValue p μ_EVAL[R] φ ∧ ∀ ψ ∈ alts, ¬ θ < expectedValue p μ_EVAL[R] ψ}

/-- (17): *ought* holds of `φ` when `φ` is the best good-enough option, above the threshold and
of greater expected value than each alternative. -/
def ought : Set (Set W) :=
  {φ | θ < expectedValue p μ_EVAL[R] φ ∧
    ∀ ψ ∈ alts, expectedValue p μ_EVAL[R] ψ < expectedValue p μ_EVAL[R] φ}

/-- (59): *might* holds of `φ` when *must*, with `φ` as the one alternative, does not hold of the
negation of `φ`. -/
def might : Set (Set W) := {φ | φᶜ ∉ must p R {φ} θ}

/-- `ofForce p R alts θ f` is the paper's entry for a modal of force `f`: (6) for necessity, (17)
for weak necessity and (59) for possibility. -/
def ofForce : Modality.ModalForce → Set (Set W)
  | .necessity => must p R alts θ
  | .weakNecessity => ought p R alts θ
  | .possibility => might p R θ

variable {p R alts θ} {alts' : Set (Set W)} {φ ψ : Set W}

-- (6)
theorem mem_must : φ ∈ must p R alts θ ↔
    θ < expectedValue p μ_EVAL[R] φ ∧ ∀ ψ ∈ alts, expectedValue p μ_EVAL[R] ψ ≤ θ := by
  simp only [must, mem_ofPred_eq, not_lt]

theorem mem_ought : φ ∈ ought p R alts θ ↔ θ < expectedValue p μ_EVAL[R] φ ∧
    ∀ ψ ∈ alts, expectedValue p μ_EVAL[R] ψ < expectedValue p μ_EVAL[R] φ :=
  Iff.rfl

-- §3.1
theorem must_subset_ought : must p R alts θ ⊆ ought p R alts θ :=
  fun _ h ↦ ⟨h.1, fun ψ hψ ↦ (not_lt.1 (h.2 ψ hψ)).trans_lt h.1⟩

-- fn. 19
theorem must_anti (h : alts ⊆ alts') : must p R alts' θ ⊆ must p R alts θ :=
  fun _ hφ ↦ ⟨hφ.1, fun ψ hψ ↦ hφ.2 ψ (h hψ)⟩

theorem notMem_must_of_mem_must (h : φ ∈ must p R alts θ) (hψ : ψ ∈ alts) :
    ψ ∉ must p R alts' θ :=
  fun h' ↦ h.2 ψ hψ h'.1

theorem notMem_must_of_le (hψ : ψ ∈ alts)
    (h : expectedValue p μ_EVAL[R] φ ≤ expectedValue p μ_EVAL[R] ψ) : φ ∉ must p R alts θ :=
  fun h' ↦ h'.2 ψ hψ (h'.1.trans_le h)

theorem mem_must_singleton : φ ∈ must p R {ψ} θ ↔
    θ ∈ Ico (expectedValue p μ_EVAL[R] ψ) (expectedValue p μ_EVAL[R] φ) := by
  simp [mem_must, and_comm]

-- (59)
theorem mem_might : φ ∈ might p R θ ↔
    expectedValue p μ_EVAL[R] φᶜ ≤ θ ∨ θ < expectedValue p μ_EVAL[R] φ := by
  simp [might, mem_must, imp_iff_not_or]

-- §6
theorem compl_mem_might_iff : φᶜ ∈ might p R θ ↔ φ ∉ must p R {φᶜ} θ := by
  rw [might, mem_ofPred_eq, compl_compl]

/-- *Must* depends on the prior only through the prior conditioned on the prejacent and on each
alternative. -/
theorem mem_must_congr_cond {q : Measure W} (h : ∀ ψ ∈ insert φ alts, p[|ψ] = q[|ψ]) :
    φ ∈ must p R alts θ ↔ φ ∈ must q R alts θ := by
  rw [mem_must, mem_must, expectedValue_congr_cond (h φ (mem_insert _ _))]
  exact and_congr_right fun _ ↦ forall₂_congr fun ψ hψ ↦ by
    rw [expectedValue_congr_cond (h ψ (mem_insert_of_mem _ hψ))]

end Operators

/-! ### Expected value -/

section ExpectedValue

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] {p : Measure W} {R : ι → Set W}
  {alts : Set (Set W)} {θ : ℝ} {φ ψ : Set W}

-- (12)
theorem expectedValue_eq_sum_cond (p : Measure W) (R : ι → Set W) (φ : Set W) :
    expectedValue p μ_EVAL[R] φ = ∑ i, p[|φ].real (R i) :=
  expectedValue_sum_indicator_one _ fun _ _ ↦ .of_discrete

theorem expectedValue_le_card : expectedValue p μ_EVAL[R] φ ≤ Fintype.card ι := by
  rw [expectedValue_eq_sum_cond]
  exact (Finset.sum_le_sum fun _ _ ↦ measureReal_le_one).trans_eq (by simp)

-- §7
theorem expectedValue_eq_card_of_subset [IsFiniteMeasure p] (hφ : p φ ≠ 0) (h : ∀ i, φ ⊆ R i) :
    expectedValue p μ_EVAL[R] φ = Fintype.card ι :=
  expectedValue_eq_of_forall_mem_eq .of_discrete hφ fun w hw ↦ by
    simp [Finset.sum_apply, indicator_of_mem (h _ hw)]

-- (49), (50), (60b)
theorem notMem_must_of_subset [IsFiniteMeasure p] (hψ : ψ ∈ alts) (h₀ : p ψ ≠ 0)
    (h : ∀ i, ψ ⊆ R i) :
    φ ∉ must p R alts θ :=
  notMem_must_of_le hψ (expectedValue_le_card.trans_eq (expectedValue_eq_card_of_subset h₀ h).symm)

-- §3.3: a density that is a positive finite constant on each hypothesis changes no *must*
theorem mem_must_withDensity_iff {f : W → ℝ≥0∞}
    (hf : ∀ ψ ∈ insert φ alts, ∃ c, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ w ∈ ψ, f w = c) :
    φ ∈ must (p.withDensity f) R alts θ ↔ φ ∈ must p R alts θ :=
  mem_must_congr_cond fun ψ hψ ↦
    let ⟨_, hc₀, hc, hfc⟩ := hf ψ hψ
    cond_withDensity_of_forall_mem_eq p .of_discrete hc₀ hc hfc

end ExpectedValue

/-! ### The likelihood ratio measure (§2, §6) -/

section LikelihoodRatio

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] {p : Measure W} {e φ : Set W} {θ : ℝ}

/-- (14): on the alternative analysis with one piece of evidence and the polar alternative,
*must* holds of `φ` when the likelihood ratio measure of `φ` on the evidence, the weight of
evidence, exceeds the threshold. -/
def mustLog (p : Measure W) (e : Set W) (θ : ℝ) : Set (Set W) :=
  {φ | (θ : EReal) < weightOfEvidence p φ e}

/-- (62): *might* on the alternative analysis is the dual of `mustLog`. -/
def mightLog (p : Measure W) (e : Set W) (θ : ℝ) : Set (Set W) :=
  {φ | φᶜ ∉ mustLog p e θ}

omit [DiscreteMeasurableSpace W] in
-- (62)
theorem mem_mightLog :
    φ ∈ mightLog p e θ ↔ ((-θ : ℝ) : EReal) ≤ weightOfEvidence p φ e := by
  rw [mightLog, mem_ofPred_eq, mustLog, mem_ofPred_eq, not_lt, weightOfEvidence_compl,
    EReal.neg_le, EReal.coe_neg]

-- (14): where both likelihoods are positive the measure is the difference of their logarithms
theorem weightOfEvidence_eq_log_sub_log (h : p[e | φ] ≠ 0) (h' : p[e | φᶜ] ≠ 0) :
    weightOfEvidence p φ e =
      (Real.log (expectedValue p μ_EVAL[![e]] φ) -
        Real.log (expectedValue p μ_EVAL[![e]] φᶜ) : ℝ) := by
  have hr {ψ : Set W} (hψ : p[e | ψ] ≠ 0) : p[|ψ].real e ≠ 0 :=
    (ENNReal.toReal_pos hψ (measure_ne_top _ _)).ne'
  rw [weightOfEvidence_eq_coe_log h h', Real.log_div (hr h) (hr h'), expectedValue_eq_sum_cond,
    expectedValue_eq_sum_cond, Fin.sum_univ_one, Fin.sum_univ_one, Matrix.cons_val_zero]

/-- With one piece of evidence and the polar alternative, *must* holds of `φ` at some threshold
exactly when the evidence has positive weight for `φ`. -/
theorem exists_mem_must_compl_iff :
    (∃ θ, φ ∈ must p ![e] {φᶜ} θ) ↔ 0 < weightOfEvidence p φ e := by
  rw [weightOfEvidence_pos_iff,
    ← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [mem_must_singleton, Fin.sum_univ_one, Matrix.cons_val_zero,
    expectedValue_indicator_one MeasurableSet.of_discrete, measureReal_def]
  exact ⟨fun ⟨_, h⟩ ↦ h.1.trans_lt h.2, fun h ↦ ⟨_, le_rfl, h⟩⟩

end LikelihoodRatio

/-! ### The words of the rows -/

/-- The English auxiliary that a lexeme of the rows names. -/
def Examples.Lexeme.entry : Examples.Lexeme → ModalAuxiliary
  | .must => English.Auxiliaries.must
  | .ought => English.Auxiliaries.ought

theorem entry_mem_modals : ∀ l : Examples.Lexeme, l.entry ∈ English.Auxiliaries.modals := by
  decide

-- every span that names a modal is an English word written as its entry
theorem lexeme_forms :
    ∀ x : Examples.Example, ∀ sp ∈ x.datum.spans, ∀ l ∈ Examples.lexeme? sp,
      x.datum.language = .english ∧
        ∃ w ∈ (sp.words x.datum).head?, w.word = l.entry.form.toList := by
  decide +kernel

/-! ### The miners puzzle (§3.1) -/

namespace Miners

/-- The two shafts of the mine. -/
inductive Shaft
  | A | B
  deriving DecidableEq, Fintype

/-- The actions open to us are to block one of the shafts or to block neither. -/
inductive Action
  | block (s : Shaft) | blockNeither
  deriving DecidableEq, Fintype

/-- A world settles the action taken and the shaft the miners are in (Table 1). -/
abbrev World := Action × Shaft

instance : MeasurableSpace Shaft := ⊤

instance : DiscreteMeasurableSpace Shaft := ⟨fun _ ↦ trivial⟩

instance : MeasurableSpace Action := ⊤

instance : DiscreteMeasurableSpace Action := ⟨fun _ ↦ trivial⟩

/-- The proposition that action `a` is taken. -/
abbrev act (a : Action) : Set World := Prod.fst ⁻¹' {a}

/-- The proposition that the miners are in shaft `s`. -/
abbrev inShaft (s : Shaft) : Set World := Prod.snd ⁻¹' {s}

instance (a : Action) : DecidablePred (· ∈ act a) := fun w ↦ decEq w.1 a

instance (s : Shaft) : DecidablePred (· ∈ inShaft s) := fun w ↦ decEq w.2 s

/-- The alternatives to an action are the other actions. -/
abbrev others (a : Action) : Set (Set World) := act '' {a}ᶜ

/-- Table 1: the miners saved at each world. -/
def saved : World → ℕ
  | (.block s, s') => if s = s' then 10 else 0
  | (.blockNeither, _) => 9

/-- (18): the ideals, after Cariani, Kaufmann and Kaufmann, of which the `k`th holds where more
than `k` miners are saved. -/
abbrev ideals (k : Fin 10) : Set World := {w | k < saved w}

-- (8)
theorem sum_indicator_ideals (w : World) : μ_EVAL[ideals] w = saved w := by
  rw [sum_indicator_one_apply]
  exact_mod_cast (by decide : ∀ w : World, #{k : Fin 10 | w ∈ ideals k} = saved w) w

theorem forall_mem_others {a : Action} {P : Set World → Prop} :
    (∀ ψ ∈ others a, P ψ) ↔ ∀ b ≠ a, P (act b) :=
  forall_mem_image

variable {p : Measure World} [IsFiniteMeasure p] {θ : ℝ}

-- (19)
theorem expectedValue_blockNeither (h : p (act .blockNeither) ≠ 0) :
    expectedValue p μ_EVAL[ideals] (act .blockNeither) = 9 := by
  refine expectedValue_eq_of_forall_mem_eq .of_discrete h fun ⟨a, s⟩ hw ↦ ?_
  obtain rfl : a = .blockNeither := hw
  rw [sum_indicator_ideals]
  norm_num [saved]

-- (20), (21)
theorem expectedValue_block (p : Measure World) (s : Shaft) :
    expectedValue p μ_EVAL[ideals] (act (.block s)) =
      10 * p[|act (.block s)].real (inShaft s) := by
  rw [← expectedValue_indicator_one .of_discrete, ← expectedValue_const_mul]
  refine expectedValue_congr_fun .of_discrete fun ⟨a, s'⟩ hw ↦ ?_
  obtain rfl : a = .block s := hw
  rw [sum_indicator_ideals]
  by_cases h : s = s'
  · simp [saved, h, indicator]
  · simp [saved, h, indicator, Ne.symm h]

-- (23)
theorem expectedValue_cond_inShaft {s : Shaft} {a : Action} (h : p (inShaft s ∩ act a) ≠ 0) :
    expectedValue p[|inShaft s] μ_EVAL[ideals] (act a) = saved (a, s) := by
  rw [expectedValue_cond .of_discrete .of_discrete]
  refine expectedValue_eq_of_forall_mem_eq .of_discrete h fun ⟨a', s'⟩ hw ↦ ?_
  obtain ⟨rfl, rfl⟩ : s' = s ∧ a' = a := hw
  exact sum_indicator_ideals _

/-! The paper's assumptions on the prior: whatever is done, the miners are as likely to be in
one shaft as in the other. -/

section Equiprobable

variable (h : ∀ a s, p[|act a].real (inShaft s) = 1 / 2)
include h

omit [IsFiniteMeasure p] in
theorem measure_inShaft_inter_act_ne_zero (s : Shaft) (a : Action) :
    p (inShaft s ∩ act a) ≠ 0 := fun h₀ ↦ by
  have := h a s
  rw [cond_real_apply _ .of_discrete, inter_comm, measureReal_def, h₀] at this
  norm_num at this

omit [IsFiniteMeasure p] in
theorem measure_act_ne_zero (a : Action) : p (act a) ≠ 0 := fun h₀ ↦
  measure_inShaft_inter_act_ne_zero h .A a (measure_mono_null inter_subset_right h₀)

omit [IsFiniteMeasure p] in
-- (20), (21)
theorem expectedValue_block_eq (s : Shaft) :
    expectedValue p μ_EVAL[ideals] (act (.block s)) = 5 := by
  rw [expectedValue_block, h]
  norm_num

-- (22)
theorem mem_ought_blockNeither :
    act .blockNeither ∈ ought p ideals (others .blockNeither) θ ↔ θ < 9 := by
  rw [mem_ought, expectedValue_blockNeither (measure_act_ne_zero h _), forall_mem_others]
  refine and_iff_left fun b hb ↦ ?_
  obtain s | _ := b
  · rw [expectedValue_block_eq h]; norm_num
  · exact absurd rfl hb

-- (26a)
theorem mem_must_blockNeither :
    act .blockNeither ∈ must p ideals (others .blockNeither) θ ↔ θ ∈ Ico 5 9 := by
  rw [mem_must, expectedValue_blockNeither (measure_act_ne_zero h _), forall_mem_others, mem_Ico,
    and_comm]
  refine and_congr_left' ⟨fun H ↦ ?_, fun h5 b hb ↦ ?_⟩
  · simpa [expectedValue_block_eq h] using H (.block .A) (by simp)
  · obtain s | _ := b
    · rwa [expectedValue_block_eq h]
    · exact absurd rfl hb

-- (24), for (15b) and (15c)
theorem mem_ought_block (s : Shaft) :
    act (.block s) ∈ ought p[|inShaft s] ideals (others (.block s)) θ ↔ θ < 10 := by
  have hE (a : Action) := expectedValue_cond_inShaft (measure_inShaft_inter_act_ne_zero h s a)
  rw [mem_ought, forall_mem_others, hE]
  refine (and_iff_left fun b hb ↦ ?_).trans (by simp [saved])
  rw [hE]
  obtain s' | _ := b
  · have : s' ≠ s := fun hs ↦ hb (hs ▸ rfl)
    simp [saved, this]
  · norm_num [saved]

-- (25b), (25c)
theorem mem_must_block (s : Shaft) :
    act (.block s) ∈ must p[|inShaft s] ideals (others (.block s)) θ ↔ θ ∈ Ico 9 10 := by
  have hE (a : Action) := expectedValue_cond_inShaft (measure_inShaft_inter_act_ne_zero h s a)
  rw [mem_must, forall_mem_others, hE, mem_Ico, and_comm]
  refine and_congr ⟨fun H ↦ ?_, fun h9 b hb ↦ ?_⟩ (by simp [saved])
  · simpa [hE, saved] using H .blockNeither (by simp)
  · rw [hE]
    obtain s' | _ := b
    · have : s' ≠ s := fun hs ↦ hb (hs ▸ rfl)
      simp only [saved, this, ite_false, Nat.cast_zero]
      linarith
    · simpa [saved] using h9

-- no threshold verifies both the unconditional *must* and a conditional one
theorem not_exists_must (s : Shaft) :
    ¬ ∃ θ, act .blockNeither ∈ must p ideals (others .blockNeither) θ ∧
      act (.block s) ∈ must p[|inShaft s] ideals (others (.block s)) θ := fun ⟨_, h₁, h₂⟩ ↦
  ((mem_must_blockNeither h).1 h₁).2.not_ge ((mem_must_block h s).1 h₂).1

end Equiprobable

/-- The uniform prior over the six worlds. -/
noncomputable abbrev prior : Measure World := uniformOn univ

theorem prior_cond (a : Action) (s : Shaft) : prior[|act a].real (inShaft s) = 1 / 2 := by
  rw [uniformOn_univ_cond, uniformOn_real_apply,
    show (act a ∩ inShaft s).ncard = 1 by rw [ncard_eq_toFinset_card']; revert a s; decide,
    show (act a).ncard = 2 by rw [ncard_eq_toFinset_card']; revert a; decide]
  norm_num

example : act .blockNeither ∈ must prior ideals (others .blockNeither) 7 :=
  (mem_must_blockNeither prior_cond).2 ⟨by norm_num, by norm_num⟩

-- fn. 17
theorem expectedValue_prior_inShaft (s : Shaft) :
    expectedValue prior μ_EVAL[ideals] (inShaft s) = 19 / 3 := by
  rw [expectedValue_congr_fun (V' := fun w ↦ (saved w : ℝ)) .of_discrete fun w _ ↦
    sum_indicator_ideals w, expectedValue_eq_sum]
  simp only [uniformOn_univ_real_singleton, ← Finset.mul_sum, ← Nat.cast_sum, Finset.sum_const,
    nsmul_eq_mul]
  rw [show ∑ w with w ∈ inShaft s, saved w = 19 by revert s; decide,
    show #{w | w ∈ inShaft s} = 3 by revert s; decide,
    show Fintype.card World = 6 by decide]
  norm_num

-- fn. 17
theorem expectedValue_univ_lt_blockNeither (s : Shaft) :
    expectedValue prior[|inShaft s] μ_EVAL[ideals] univ <
      expectedValue prior[|inShaft s] μ_EVAL[ideals] (act .blockNeither) := by
  rw [expectedValue_cond_inShaft (measure_inShaft_inter_act_ne_zero prior_cond s _),
    expectedValue_cond .of_discrete .univ, inter_univ, expectedValue_prior_inShaft]
  norm_num [saved]

open Modality in
-- (16)
theorem not_bestWorlds_subset {V : Type*} (f g : Background V) (w : V) {inA inB bA bB bN : Set V}
    (hbest : (f.bestWorlds g w).Nonempty) (hcover : f.accessibleWorlds w ⊆ inA ∪ inB)
    (hA : Disjoint bA bN) (hB : Disjoint bB bN) :
    ¬ (f.bestWorlds g w ⊆ bN ∧ (f.restrict inA).bestWorlds g w ⊆ bA ∧
        (f.restrict inB).bestWorlds g w ⊆ bB) := by
  rintro ⟨hN, hAB, hBB⟩
  obtain ⟨v, hv⟩ := hbest
  -- (16d), (16e)
  have key (α : Set V) (hα : v ∈ α) : v ∈ (f.restrict α).bestWorlds g w :=
    Background.mem_bestWorlds_of_subset
      (fun _ hu ↦ (Background.mem_accessibleWorlds_restrict.1 hu).1) hv
      (Background.mem_accessibleWorlds_restrict.2 ⟨hv.1, hα⟩)
  rcases hcover hv.1 with hv' | hv'
  · exact disjoint_left.1 hA (hAB (key inA hv')) (hN hv)
  · exact disjoint_left.1 hB (hBB (key inB hv')) (hN hv)

/-! The sentences of (15), (25) and (26), read from the rows. -/

/-- The action a row's prejacent names. -/
def action : Examples.Prejacent → Action
  | .blockNeither => .blockNeither
  | .blockA => .block .A
  | .blockB => .block .B

/-- The prior a row is judged against, the uniform prior conditioned on the antecedent if the
row has one. -/
noncomputable def priorOf : Option Examples.Antecedent → Measure World
  | none => prior
  | some .minersInA => prior[|inShaft .A]
  | some .minersInB => prior[|inShaft .B]

theorem exists_mem_ofForce_blockNeither {f : Modality.ModalForce} (hf : f ≠ .possibility) :
    ∃ θ, act .blockNeither ∈ ofForce prior ideals (others .blockNeither) θ f := by
  obtain _ | _ | _ := f
  · exact ⟨7, (mem_must_blockNeither prior_cond).2 ⟨by norm_num, by norm_num⟩⟩
  · exact ⟨7, (mem_ought_blockNeither prior_cond).2 (by norm_num)⟩
  · exact absurd rfl hf

theorem exists_mem_ofForce_block (s : Shaft) {f : Modality.ModalForce} (hf : f ≠ .possibility) :
    ∃ θ, act (.block s) ∈ ofForce prior[|inShaft s] ideals (others (.block s)) θ f := by
  obtain _ | _ | _ := f
  · exact ⟨9, (mem_must_block prior_cond s).2 ⟨le_rfl, by norm_num⟩⟩
  · exact ⟨9, (mem_ought_block prior_cond s).2 (by norm_num)⟩
  · exact absurd rfl hf

/-- (15), (25), (26): each sentence of the miners puzzle is true at some threshold, on the entry
its modal has for the force the English auxiliary expresses, and the paper judges none false. -/
theorem rows (x : Examples.Example) (a : Examples.Prejacent) (hx : x.prejacent = some a) :
    (∀ l ∈ x.lexemes .modal, ∀ f ∈ l.entry.forces,
        ∃ θ, act (action a) ∈ ofForce (priorOf x.antecedent) ideals (others (action a)) θ f) ∧
      x.datum.verdict ≠ some false := by
  have hm : ∀ x : Examples.Example, ∀ a, x.prejacent = some a → (a, x.antecedent) ∈
      [(.blockNeither, none), (.blockA, some .minersInA), (.blockB, some .minersInB)] := by
    decide
  have hf : ∀ x : Examples.Example, ∀ l ∈ x.lexemes .modal, ∀ f ∈ l.entry.forces,
      f ≠ .possibility := by decide
  have hv : ∀ x : Examples.Example, ∀ a, x.prejacent = some a → x.datum.verdict ≠ some false := by
    decide
  refine ⟨fun l hl f hfm ↦ ?_, hv x a hx⟩
  have h := hm x a hx
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  obtain ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ := h <;> rw [h]
  exacts [exists_mem_ofForce_blockNeither (hf x l hl f hfm),
    exists_mem_ofForce_block .A (hf x l hl f hfm), exists_mem_ofForce_block .B (hf x l hl f hfm)]

end Miners

/-! ### The modal conjunction fallacy (§3.2) -/

section Linda

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] {p : Measure W} {R : Fin 2 → Set W}
  {teller feminist : Set W} {θ : ℝ}

-- (30), (31), (32), (33), (34)
theorem mem_must_teller_inter_feminist
    (h₁ : p[|teller].real (R 0) = 0.3) (h₂ : p[|teller].real (R 1) = 0.2)
    (h₃ : p[|teller ∩ feminist].real (R 0) = 0.8) (h₄ : p[|teller ∩ feminist].real (R 1) = 0.7) :
    teller ∩ feminist ∈ must p R {teller} θ ↔ θ ∈ Ico 0.5 1.5 := by
  rw [mem_must_singleton, expectedValue_eq_sum_cond, expectedValue_eq_sum_cond, Fin.sum_univ_two,
    Fin.sum_univ_two, h₁, h₂, h₃, h₄]
  norm_num

/-- The modal conjunction fallacy: with the likelihoods (30) and (31), *must* holds of the
conjunction and not of its conjunct at every threshold from 0.5 up to 1.5. -/
theorem modal_conjunction_fallacy
    (h₁ : p[|teller].real (R 0) = 0.3) (h₂ : p[|teller].real (R 1) = 0.2)
    (h₃ : p[|teller ∩ feminist].real (R 0) = 0.8) (h₄ : p[|teller ∩ feminist].real (R 1) = 0.7)
    (hθ : θ ∈ Ico (0.5 : ℝ) 1.5) :
    teller ∩ feminist ∈ must p R {teller} θ ∧ teller ∉ must p R {teller ∩ feminist} θ :=
  have h := (mem_must_teller_inter_feminist h₁ h₂ h₃ h₄).2 hθ
  ⟨h, notMem_must_of_mem_must h (mem_singleton _)⟩

end Linda

open Modality in
-- Table 2: Kratzer's necessity is closed under consequence
theorem mem_necessity_of_subset {f g : Background W} {w : W} {φ ψ : Set W} (h : φ ⊆ ψ)
    (hφ : φ ∈ f.necessity g w) : ψ ∈ f.necessity g w :=
  Filter.mem_of_superset hφ h

-- Table 2: and so is a threshold on probability
theorem mem_pos_must_of_subset [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {θ : Lassiter2017.EpistemicItem → ℝ} {φ ψ : Set W} (h : φ ⊆ ψ)
    (hφ : φ ∈ Lassiter2017.pos P θ .must) : ψ ∈ Lassiter2017.pos P θ .must :=
  (show θ .must ≤ P.real φ from hφ).trans (measureReal_mono h)

/-! A model of the likelihoods (30) and (31): fifty equiprobable people, forty of them bank
tellers and ten of those feminists. -/

namespace Linda

/-- The bank tellers. -/
abbrev teller : Set (Fin 50) := {w | w.val < 40}

/-- The people active in the feminist movement. -/
abbrev feminist : Set (Fin 50) := {w | w.val < 10 ∨ 40 ≤ w.val}

/-- The people concerned with social justice. -/
abbrev socialJustice : Set (Fin 50) := {w | w.val < 8 ∨ (10 ≤ w.val ∧ w.val < 14)}

/-- The people who took part in anti-nuclear protests. -/
abbrev antiNuclear : Set (Fin 50) := {w | w.val < 7 ∨ w.val = 14}

example : teller ∩ feminist ∈ must (uniformOn univ) ![socialJustice, antiNuclear] {teller} 1 := by
  refine (mem_must_teller_inter_feminist ?_ ?_ ?_ ?_).2 ⟨by norm_num, by norm_num⟩
  all_goals rw [uniformOn_univ_cond, uniformOn_real_apply]
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [show (teller ∩ socialJustice).ncard = 12 by rw [ncard_eq_toFinset_card']; decide,
      show teller.ncard = 40 by rw [ncard_eq_toFinset_card']; decide]
    norm_num
  · rw [show (teller ∩ antiNuclear).ncard = 8 by rw [ncard_eq_toFinset_card']; decide,
      show teller.ncard = 40 by rw [ncard_eq_toFinset_card']; decide]
    norm_num
  · rw [show (teller ∩ feminist ∩ socialJustice).ncard = 8 by
        rw [ncard_eq_toFinset_card']; decide,
      show (teller ∩ feminist).ncard = 10 by rw [ncard_eq_toFinset_card']; decide]
    norm_num
  · rw [show (teller ∩ feminist ∩ antiNuclear).ncard = 7 by
        rw [ncard_eq_toFinset_card']; decide,
      show (teller ∩ feminist).ncard = 10 by rw [ncard_eq_toFinset_card']; decide]
    norm_num

end Linda

/-! ### Lawyers and engineers (§3.3) -/

section Lawyers

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] {p : Measure W} {R : Fin 2 → Set W}
  {engineer lawyer : Set W} {θ : ℝ}

-- (37), (38), (39), (40), (41)
theorem mem_must_engineer
    (h₁ : p[|engineer].real (R 0) = 0.78) (h₂ : p[|engineer].real (R 1) = 0.55)
    (h₃ : p[|lawyer].real (R 0) = 0.35) (h₄ : p[|lawyer].real (R 1) = 0.28) :
    engineer ∈ must p R {lawyer} θ ↔ θ ∈ Ico 0.63 1.33 := by
  rw [mem_must_singleton, expectedValue_eq_sum_cond, expectedValue_eq_sum_cond, Fin.sum_univ_two,
    Fin.sum_univ_two, h₁, h₂, h₃, h₄]
  norm_num

end Lawyers

/-! ### Focus and alternatives (§6) -/

namespace Inheritance

/-- Whom Kim marries: Pat, someone else, or nobody. -/
inductive Marriage
  | pat | another | nobody
  deriving DecidableEq, Fintype

instance : MeasurableSpace Marriage := ⊤

instance : DiscreteMeasurableSpace Marriage := ⟨fun _ ↦ trivial⟩

/-- The goal: Kim inherits, which takes being married. -/
abbrev goal : Fin 1 → Set Marriage := fun _ ↦ {.nobody}ᶜ

/-- The prejacent, that Kim marries Pat. -/
abbrev marryPat : Set Marriage := {.pat}

/-- The uniform prior over the three outcomes. -/
noncomputable abbrev prior : Measure Marriage := uniformOn univ

-- (60a)
theorem mem_must_polar {θ : ℝ} : marryPat ∈ must prior goal {marryPatᶜ} θ ↔ θ ∈ Ico (1 / 2) 1 := by
  rw [mem_must_singleton, expectedValue_eq_sum_cond, expectedValue_eq_sum_cond, Fin.sum_univ_one,
    Fin.sum_univ_one, uniformOn_univ_cond, uniformOn_univ_cond, uniformOn_real_apply,
    uniformOn_real_apply,
    show (marryPatᶜ ∩ goal 0).ncard = 1 by rw [ncard_eq_toFinset_card']; decide,
    show (marryPatᶜ : Set Marriage).ncard = 2 by rw [ncard_eq_toFinset_card']; decide,
    show (marryPat ∩ goal 0).ncard = 1 by rw [ncard_eq_toFinset_card']; decide,
    show marryPat.ncard = 1 by rw [ncard_eq_toFinset_card']; decide]
  norm_num

-- (60b)
theorem notMem_must_focus {θ : ℝ} : marryPat ∉ must prior goal {{.another}} θ :=
  notMem_must_of_subset (mem_singleton _) (uniformOn_univ_singleton_ne_zero _)
    fun _ _ h ↦ by rintro rfl; cases h

/-- The alternatives to the prejacent: its negation by default, and under focus on *Pat* the
other people Kim might marry (fn. 8). -/
def alternatives : Option Examples.Focus → Set (Set Marriage)
  | none => {marryPatᶜ}
  | some .pat => {{.another}}

/-- (60): *Kim must marry Pat in order to inherit* is true at some threshold with neutral focus
and at none with focus on *Pat*, as the paper judges. -/
theorem rows (x : Examples.Example) (hx : x = .ex_60a ∨ x = .ex_60b) :
    ∀ l ∈ x.lexemes .modal, ∀ f ∈ l.entry.forces,
      (∃ θ, marryPat ∈ ofForce prior goal (alternatives x.focus) θ f) ↔
        x.datum.verdict = some true := by
  have hf : ∀ l ∈ Examples.Example.ex_60a.lexemes .modal ++ Examples.Example.ex_60b.lexemes .modal,
      ∀ f ∈ l.entry.forces, f = .necessity := by decide
  obtain rfl | rfl := hx <;> intro l hl f hfm
  · obtain rfl := hf l (List.mem_append_left _ hl) f hfm
    exact iff_of_true ⟨1 / 2, mem_must_polar.2 ⟨le_rfl, by norm_num⟩⟩ rfl
  · obtain rfl := hf l (List.mem_append_right _ hl) f hfm
    exact iff_of_false (fun ⟨_, h⟩ ↦ notMem_must_focus h) (by decide)

end Inheritance

end ChungMascarenhas2023
