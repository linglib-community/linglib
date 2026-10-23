module

public import Linglib.Core.Probability.Kernel.Posterior

/-!
# Rees, Reksnes, and Rohde (2026): Why are you telling me this? The availability and timing of relevance inferences

Rees, Reksnes and Rohde ask why an addressee takes a trivial remark such as *the library walls
are blue* to mean that the walls used to be a different colour. A speaker makes a remark only
when it is worth enough to her, and a quiet speaker's bar is higher. Here the addressee
conditions a prior over whether the situation changed on the pasts in which the speaker would
have spoken; a change can make a trivial remark worth making only to a speaker who knows the
situation over time. Across four experiments the inference is drawn more often for a
knowledgeable speaker and, in the second, for a quiet one. Two verification experiments with
opposite question polarity locate a cost when the inference is endorsed, which the paper
attributes to considering the alternative situation.

## Main statements

* `Speaker.prior_lt_posterior_iff`: speaking raises the probability that the situation changed
  exactly when the remark is trivial on its own and a change would make it worth making.
* `Speaker.posterior_eq_prior_of_not_knowledgeable`: a speaker who does not know the situation
  over time conveys nothing about its past by speaking.
* `Speaker.prior_lt_posterior_of_bar_le`: a quieter speaker licenses whatever a more talkative
  one does, as long as a change would still be worth mentioning to her.
* `ResponseModel.exp3_no_eq_exp4_no`, `AdditiveModel.yes_eq_yes_of_no_eq_no`: if considering the
  alternative is the cost, the *no* answers of the two experiments take equally long, as found;
  separate costs of a negative answer and of the inference could not also give the slower
  inference-endorsing *yes*.

## Implementation notes

Conditioning on the decision to speak is Rohde, Hoek, Keshev and Franke's account of the
listener's expectation, which the paper cites. The speaker speaks exactly when the remark's
worth to her meets her bar, so the model says which inferences are available, not how often
participants draw them. Every item describes a situation that may plausibly have changed. The emphasis cue and the paper's post hoc account of
the interaction in its second experiment are not modelled.

## References

* [A. Rees, V. Reksnes, H. Rohde, *Why are you telling me this? The availability and timing
  of relevance inferences* (2026)][rees-reksnes-rohde-2026]
* [H. Rohde, J. Hoek, M. Keshev, M. Franke, *This better be interesting: a speaker's decision
  to speak cues listeners to expect informative content* (2022)][rohde-etal-2022]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ReesReksnesRohde2026

/-! ### The decision to speak -/

/-- A past of the described situation says whether, a few months ago, it was the same as now
or different. -/
inductive Past
  | same
  | different
  deriving DecidableEq, Fintype

instance : MeasurableSpace Past := ⊤
instance : DiscreteMeasurableSpace Past := ⟨fun _ ↦ trivial⟩
instance : Nonempty Past := ⟨.same⟩

/-- The addressee models the speaker making a remark by what the remark is worth to her in each
past of the situation and by the bar a remark must clear for her to make it. -/
structure Speaker where
  worth : Past → ℝ
  bar : ℝ

namespace Speaker

variable (s : Speaker)

/-- The speaker knows the situation over time when the worth of her remark depends on its
past. -/
def Knowledgeable : Prop := s.worth .same ≠ s.worth .different

/-- The remark is trivial when, with nothing changed, it falls short of the speaker's bar. -/
def Trivial : Prop := s.worth .same < s.bar

/-- The speaker makes the remark exactly in the pasts in which it is worth it to her. -/
noncomputable def spoke : Kernel Past Bool :=
  Kernel.deterministic (fun p ↦ decide (s.bar ≤ s.worth p)) .of_discrete

instance : IsMarkovKernel s.spoke := by unfold spoke; infer_instance

private theorem preimage_spoke :
    (fun p ↦ decide (s.bar ≤ s.worth p)) ⁻¹' {true} = {p | s.bar ≤ s.worth p} := by
  ext; simp

theorem spoke_real_true (p : Past) :
    (s.spoke p).real {true} = if s.bar ≤ s.worth p then 1 else 0 := by
  rw [measureReal_def, spoke, Kernel.deterministic_apply' _ _ (MeasurableSet.singleton _)]
  split_ifs with h <;> simp [h]

variable {s} {t : Speaker} (μ : Measure Past)

theorem spoke_comp_apply_true : (s.spoke ∘ₘ μ) {true} = μ {p | s.bar ≤ s.worth p} := by
  rw [← preimage_spoke, ← Measure.map_apply .of_discrete (measurableSet_singleton _),
    ← Measure.deterministic_comp_eq_map]
  rfl

theorem Trivial.mono (h : s.Trivial) (hw : s.worth = t.worth) (hb : s.bar ≤ t.bar) :
    t.Trivial :=
  lt_of_lt_of_le (hw ▸ h) hb

theorem spoke_comp_apply_true_eq_zero (hk : ¬ s.Knowledgeable) (ht : s.Trivial) :
    (s.spoke ∘ₘ μ) {true} = 0 := by
  have h₁ : s.worth .same < s.bar := ht
  have h₂ : s.worth .different < s.bar := by rw [← not_not.1 hk]; exact ht
  have : {p | s.bar ≤ s.worth p} = ∅ := by
    ext p; cases p <;> simp [not_le.2 h₁, not_le.2 h₂]
  simp [spoke_comp_apply_true, this]

private theorem pair_support : ∀ p, μ {p} ≠ 0 → p = Past.different ∨ p = Past.same :=
  fun p _ ↦ by cases p <;> simp

variable [IsProbabilityMeasure μ]

theorem posterior_spoke (hx : (s.spoke ∘ₘ μ) {true} ≠ 0) :
    (s.spoke†μ) true = μ[|{p | s.bar ≤ s.worth p}] := by
  have := posterior_deterministic_eq_cond μ (f := fun p ↦ decide (s.bar ≤ s.worth p))
    .of_discrete (x := true) (by rwa [preimage_spoke, ← spoke_comp_apply_true])
  rwa [preimage_spoke] at this

/-- Speaking raises the probability that the situation used to be different exactly when the
remark is trivial with nothing changed and worth making had the situation changed. -/
theorem prior_lt_posterior_iff (hx : (s.spoke ∘ₘ μ) {true} ≠ 0) (hs : μ {.same} ≠ 0)
    (hd : μ {.different} ≠ 0) :
    μ.real {.different} < ((s.spoke†μ) true).real {.different} ↔
      s.Trivial ∧ s.bar ≤ s.worth .different := by
  rw [real_lt_posterior_real_singleton_iff_of_pair s.spoke μ (by decide) (pair_support μ) hx
    hd hs, spoke_real_true, spoke_real_true, Trivial]
  by_cases h₁ : s.bar ≤ s.worth .same <;> by_cases h₂ : s.bar ≤ s.worth .different <;>
    simp [h₁, h₂, not_le.mp]

/-- A speaker who does not know the situation over time makes the remark in every past or in
none, so hearing it leaves the prior unchanged. -/
theorem posterior_eq_prior_of_not_knowledgeable (hk : ¬ s.Knowledgeable)
    (hx : (s.spoke ∘ₘ μ) {true} ≠ 0) : (s.spoke†μ) true = μ := by
  have hpre : {p | s.bar ≤ s.worth p} = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    by_contra hp
    refine hx ?_
    have h : ∀ q, ¬ s.bar ≤ s.worth q := fun q ↦ by
      cases p <;> cases q <;> simpa [not_not.1 hk] using hp
    simp [spoke_comp_apply_true, h]
  rw [posterior_spoke μ hx, hpre, cond_univ]

theorem not_prior_lt_posterior_of_not_knowledgeable (hk : ¬ s.Knowledgeable)
    (hx : (s.spoke ∘ₘ μ) {true} ≠ 0) :
    ¬ μ.real {.different} < ((s.spoke†μ) true).real {.different} := by
  rw [posterior_eq_prior_of_not_knowledgeable μ hk hx]
  exact lt_irrefl _

/-- A quieter speaker with the same view of the situation licenses the inference whenever a
more talkative one does, as long as a change would still be worth mentioning to her. -/
theorem prior_lt_posterior_of_bar_le (hw : s.worth = t.worth) (hb : s.bar ≤ t.bar)
    (ht : t.bar ≤ t.worth .different) (hx : (s.spoke ∘ₘ μ) {true} ≠ 0)
    (hx' : (t.spoke ∘ₘ μ) {true} ≠ 0) (hs : μ {.same} ≠ 0) (hd : μ {.different} ≠ 0)
    (h : μ.real {.different} < ((s.spoke†μ) true).real {.different}) :
    μ.real {.different} < ((t.spoke†μ) true).real {.different} :=
  (prior_lt_posterior_iff μ hx' hs hd).2
    ⟨((prior_lt_posterior_iff μ hx hs hd).1 h).1.mono hw hb, ht⟩

end Speaker

/-- A speaker to whom the remark is worth making only if the situation changed licenses the
inference under a uniform prior. -/
example : (uniformOn (Set.univ : Set Past)).real {.different} <
    (((Speaker.spoke ⟨fun | .same => 0 | .different => 1, 1⟩)†(uniformOn Set.univ)) true).real
      {.different} := by
  have hd := uniformOn_univ_singleton_ne_zero (W := Past) .different
  refine (Speaker.prior_lt_posterior_iff _ ?_ (uniformOn_univ_singleton_ne_zero _) hd).2
    ⟨show (0 : ℝ) < 1 by norm_num, le_rfl⟩
  rw [Speaker.spoke_comp_apply_true]
  exact fun h ↦ hd (measure_mono_null (fun p hp ↦ by simp_all) h)

/-! ### The timing of the inference -/

/-- The past that a *yes* or a *no* to *was it `q` a few months ago?* asserts. -/
def asserted : Past → Bool → Past
  | q, true => q
  | .same, false => .different
  | .different, false => .same

/-- An answer endorses the inference when it asserts that the situation was different, as *no*
to *was it the same?* does in Experiment 3 and *yes* to *was it different?* in Experiment 4. -/
def Endorses (q : Past) (a : Bool) : Prop := asserted q a = .different

/-- Answering considers the alternative to the situation as presented when the answer is
negative or endorses the inference. -/
def ConsidersAlternative (q : Past) (a : Bool) : Prop := a = false ∨ Endorses q a

instance : DecidableRel Endorses := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidableRel ConsidersAlternative := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- In the paper's account of the verification times, an answer takes a base time, and longer by
a fixed cost when it considers the alternative to the situation as presented. -/
structure ResponseModel where
  base : ℝ
  alternative : ℝ

/-- The predicted time to answer `a` to *was it `q`?*. -/
def ResponseModel.rt (m : ResponseModel) (q : Past) (a : Bool) : ℝ :=
  m.base + if ConsidersAlternative q a then m.alternative else 0

/-- An additive model of the verification times with separate costs of a negative answer and of
endorsing the inference. -/
structure AdditiveModel where
  base : ℝ
  negative : ℝ
  inference : ℝ

/-- The predicted time to answer `a` to *was it `q`?*. -/
def AdditiveModel.rt (m : AdditiveModel) (q : Past) (a : Bool) : ℝ :=
  m.base + (if a = false then m.negative else 0) + if Endorses q a then m.inference else 0

namespace ResponseModel

variable (m : ResponseModel)

theorem exp3_contrast : m.rt .same false - m.rt .same true = m.alternative := by
  simp [rt, ConsidersAlternative, Endorses, asserted]

theorem exp4_yes_eq_no : m.rt .different true = m.rt .different false := by
  simp [rt, ConsidersAlternative, Endorses, asserted]

theorem yes_contrast : m.rt .different true - m.rt .same true = m.alternative := by
  simp [rt, ConsidersAlternative, Endorses, asserted]

/-- The *no* answers of the two experiments take equally long, since both consider the
alternative. -/
theorem exp3_no_eq_exp4_no : m.rt .same false = m.rt .different false := by
  simp [rt, ConsidersAlternative, Endorses, asserted]

end ResponseModel

namespace AdditiveModel

variable (m : AdditiveModel)

theorem exp3_confounded : m.rt .same false - m.rt .same true = m.negative + m.inference := by
  simp [rt, Endorses, asserted]; ring

theorem yes_contrast : m.rt .different true - m.rt .same true = m.inference := by
  simp [rt, Endorses, asserted]

/-- If the *no* answers of the two experiments take equally long, so do the *yes* answers, so the
additive model cannot give the paper's pattern. -/
theorem yes_eq_yes_of_no_eq_no (h : m.rt .same false = m.rt .different false) :
    m.rt .different true = m.rt .same true := by
  simp [rt, Endorses, asserted] at h ⊢; linarith

end AdditiveModel

end ReesReksnesRohde2026
