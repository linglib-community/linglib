module

public import Studies.KehlerRohde2013

/-!
# Audience design in the choice of referring expressions

This file models a speaker who weighs each referring expression for a referent by two factors: how
surely a listener with prior `π` recovers the referent from the expression's literal meaning, the
literal listener of the rational speech act model, and the utterance prior of the expression's form
in the speaker's current state, which may include the plan for the continuation. When the pronoun is
unambiguous the utterance prior alone fixes the pronoun rate, whatever the listener's prior. When it
is ambiguous and the utterance prior ignores the referent, the pronoun is used more for the more
expected character, so it is inert exactly under a uniform prior, and it moves interpretation away
from the less expected character, which Kehler and Rohde's passive rules out, the pronoun raising
the less expected subject from .24 to .60.

The conjecture recorded here is that the utterance prior reads the referent's thematic role, and so
its predictability, only in continuations that focus the end state of the previous eventuality. With
different-gender characters, predictability effects on pronominalization then appear only in
Occasion and Result continuations. Kravtchenko's noisy channel, in which *he* and *she* are
sometimes confused, predicts them in every continuation, so the two accounts part on
different-gender, non-end-state continuations.

## Main statements

* `speaker_real_pronoun_of_unambiguous`: an unambiguous pronoun's rate ignores the listener's prior.
* `not_audienceDesign_passive`: no referent-blind speaker prints Kehler and Rohde's passive.
* `speaker_pronoun_eq_iff`: such a speaker's pronoun is inert iff the prior is uniform.
* `pronounRate_eq_of_not_focusesEndState`: under the conjecture, outside end-state continuations
  the unambiguous pronoun rate depends on the referent's position alone.
* `noisySpeaker_real_pronoun_lt`: through a noisy channel that rate rises with the prior.

## Implementation notes

* Provenance. No paper states the conjecture; it is proposed here. The speaker is Orita, Vornov,
  Feldman and Daumé's at `α = 1`, whose inverse cost is the utterance prior here, as in
  Kravtchenko's prior over expressions. Kravtchenko's rational speech act model already adds a
  grammatical bias to the cost and observes that without channel noise predictability cannot
  affect unambiguous pronouns; the factorization and its strong form are Kehler and Rohde's; and
  the link between transfer verbs, end-state continuations and predictability effects is Rosa and
  Arnold's suggestion, weakly supported in Liao, Brochhagen, Boleda and Mayol's meta-analysis.
  What is proposed here is an utterance prior that reads the continuation's plan, which confines
  predictability effects on unambiguous pronouns to end-state continuations, where Kravtchenko's
  noisy channel predicts weaker effects in every continuation.
* State. Untested, since the test crosses character gender, the referent's thematic role at a
  fixed position, and the continuation's coherence relation, and no study reports those cells. Rosa
  and Arnold find the Goal effect in Occasion and Result continuations, pooled over gender;
  Medina Fetterman, Vazquez and Arnold find it with same-gender characters only; Rohde and
  Kehler find production insensitive to implicit-causality bias even with ambiguous pronouns.

## References

* [orita-vornov-feldman-daume-2015]
* [frank-goodman-2012]
* [kravtchenko-2022]
* [kehler-rohde-2013]
* [rohde-kehler-2014]
* [rosa-arnold-2017]
* [liao-brochhagen-boleda-mayol-2025]
* [medina-fetterman-vazquez-arnold-2022]
-/

@[expose] public section

namespace Lab.ReferringExpressions

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open KehlerRohde2013 (Form Role Relation FocusesEndState RoundsTo)

/-- A referring expression for referents of type `R` is the pronoun or a name of a referent. -/
inductive Expression (R : Type*) where
  | pronoun
  | name (r : R)
  deriving DecidableEq

namespace Expression

variable {R : Type*}

/-- The equivalence of expressions with optional referents, the pronoun being `none`. -/
def equivOption : Expression R ≃ Option R where
  toFun
    | pronoun => none
    | name r => some r
  invFun
    | none => pronoun
    | some r => name r
  left_inv e := by cases e <;> rfl
  right_inv o := by cases o <;> rfl

instance [Fintype R] : Fintype (Expression R) := Fintype.ofEquiv _ equivOption.symm

theorem sum_eq [Fintype R] {M : Type*} [AddCommMonoid M] (f : Expression R → M) :
    ∑ e, f e = f pronoun + ∑ r, f (name r) := by
  rw [← Fintype.sum_equiv equivOption.symm (fun o ↦ f (equivOption.symm o)) f (fun _ ↦ rfl),
    Fintype.sum_option]
  rfl

/-- The form of an expression. -/
def form : Expression R → Form
  | pronoun => .pronoun
  | name _ => .other

/-- The literal meaning of an expression, given the referents `P` the pronoun's φ-features fit. -/
def sem (P : Set R) : Expression R → Set R
  | pronoun => P
  | name r => {r}

instance : MeasurableSpace (Expression R) := ⊤
instance : DiscreteMeasurableSpace (Expression R) := ⟨fun _ ↦ trivial⟩

end Expression

open Expression

variable {R S : Type*} [MeasurableSpace R] [Fintype R] [DiscreteMeasurableSpace R]
  [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] {π : Measure R}

/-- The literal listener conditions the prior on an expression's literal meaning. -/
noncomputable def literalListener (π : Measure R) (P : Set R) (e : Expression R) : Measure R :=
  π[|e.sem P]

/-- In a state `s` about the referent `ref s`, the speaker weighs each expression by the literal
listener's mass on the referent and the utterance prior of its form. -/
noncomputable def speaker (π : Measure R) (P : Set R) (ref : S → R) (κ : Form → S → ℝ≥0∞) :
    Kernel S (Expression R) :=
  Kernel.ofWeights fun s e ↦ literalListener π P e {ref s} * κ e.form s

instance (P : Set R) (e : Expression R) : IsZeroOrProbabilityMeasure (literalListener π P e) := by
  unfold literalListener; infer_instance

instance (P : Set R) (ref : S → R) (κ : Form → S → ℝ≥0∞) : IsFiniteKernel (speaker π P ref κ) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

theorem literalListener_apply_self [IsFiniteMeasure π] {P : Set R} {e : Expression R} {r : R}
    (h : e.sem P = {r}) (hπ : π {r} ≠ 0) : literalListener π P e {r} = 1 := by
  rw [literalListener, h, cond_apply (.singleton r), Set.inter_self,
    ENNReal.inv_mul_cancel hπ (measure_ne_top _ _)]

theorem literalListener_name_apply_of_ne {P : Set R} {r r' : R} (h : r' ≠ r) :
    literalListener π P (name r') {r} = 0 := by
  rw [literalListener, sem, cond_apply (.singleton r'),
    Set.singleton_inter_eq_empty.2 (Set.mem_singleton_iff.not.2 h), measure_empty, mul_zero]

/-- With an unambiguous pronoun the utterance prior fixes the pronoun rate, whatever the listener's
prior. -/
theorem speaker_real_pronoun_of_unambiguous [IsFiniteMeasure π] {ref : S → R}
    {κ : Form → S → ℝ≥0∞} {s : S} (hπ : π {ref s} ≠ 0) (hκ : ∀ f, κ f s ≠ ∞) :
    (speaker π {ref s} ref κ s).real {.pronoun} =
      (κ .pronoun s).toReal / ((κ .pronoun s).toReal + (κ .other s).toReal) := by
  classical
  have hp : literalListener π {ref s} pronoun {ref s} = 1 :=
    literalListener_apply_self (by rfl) hπ
  have hn : ∀ r, literalListener π {ref s} (name r) {ref s} * κ (name r).form s =
      if r = ref s then κ .other s else 0 := fun r ↦ by
    split_ifs with h
    · subst h; rw [literalListener_apply_self (by rfl) hπ, one_mul]; rfl
    · rw [literalListener_name_apply_of_ne h, zero_mul]
  have htop : ∀ e : Expression R, literalListener π {ref s} e {ref s} * κ e.form s ≠ ∞ :=
    fun e ↦ ENNReal.mul_ne_top (prob_le_one.trans_lt ENNReal.one_lt_top).ne (hκ _)
  rw [speaker, Kernel.ofWeights_real_singleton _ _ htop, Expression.sum_eq]
  simp only [hp, one_mul, hn]
  rw [Finset.sum_eq_single (ref s) (fun r _ h ↦ by simp [h]) (by simp)]
  simp [form]

theorem speaker_comap_fst {C : Type*} [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] (P : Set R) (κ : Form → R → ℝ≥0∞) :
    speaker π P Prod.fst (fun f s ↦ κ f s.1) =
      (speaker π P id κ).comap (Prod.fst : R × C → R) measurable_fst := by
  ext1 s
  rfl

theorem speaker_real_pronoun_of_ambiguous [IsFiniteMeasure π] {κ : Form → R → ℝ≥0∞} {r : R}
    (hπ : π {r} ≠ 0) (hκ : ∀ f, κ f r ≠ ∞) :
    (speaker π Set.univ id κ r).real {.pronoun} =
      (π[|Set.univ] {r}).toReal * (κ .pronoun r).toReal /
        ((π[|Set.univ] {r}).toReal * (κ .pronoun r).toReal + (κ .other r).toReal) := by
  classical
  have hn : ∀ r', literalListener π Set.univ (name r') {r} * κ (name r').form r =
      if r' = r then κ .other r else 0 := fun r' ↦ by
    split_ifs with h
    · subst h; rw [literalListener_apply_self (by rfl) hπ, one_mul]; rfl
    · rw [literalListener_name_apply_of_ne h, zero_mul]
  have htop : ∀ e : Expression R, literalListener π Set.univ e {r} * κ e.form r ≠ ∞ :=
    fun e ↦ ENNReal.mul_ne_top (prob_le_one.trans_lt ENNReal.one_lt_top).ne (hκ _)
  rw [speaker, Kernel.ofWeights_real_singleton _ _ htop, Expression.sum_eq]
  simp only [id_eq, hn]
  rw [Finset.sum_eq_single r (fun r' _ h ↦ by simp [h]) (by simp)]
  simp [form, literalListener, sem, ENNReal.toReal_mul]

/-- The prior that weighs the two characters equally. -/
noncomputable def evenPrior : Measure Role := Measure.ofWeights fun _ ↦ 1

/-- The prior that favours the Goal three to one. -/
noncomputable def goalPrior : Measure Role :=
  Measure.ofWeights fun r ↦ match r with
    | .source => 1
    | .goal => 3

instance : IsFiniteMeasure evenPrior :=
  Measure.isFiniteMeasure_ofWeights fun _ ↦ ENNReal.one_ne_top

instance : IsFiniteMeasure goalPrior :=
  Measure.isFiniteMeasure_ofWeights fun r ↦ by cases r <;> simp

theorem cond_univ_goal_real (w : Role → ℝ≥0∞) (hw : ∀ r, w r ≠ ∞) :
    ((Measure.ofWeights w)[|Set.univ] {.goal}).toReal =
      (w .goal).toReal / ((w .source).toReal + (w .goal).toReal) := by
  rw [cond_apply .univ, Set.univ_inter, ← Finset.coe_univ, Measure.ofWeights_apply_finset,
    Measure.ofWeights_apply_singleton,
    show (Finset.univ : Finset Role) = {.source, .goal} by decide,
    Finset.sum_pair (by decide), ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_add (hw _) (hw _)]
  ring

/-- With same-gender characters and a uniform utterance prior the Goal's pronoun rate is `1 / 3`
under the even prior and `3 / 7` under the prior favouring the Goal. -/
example :
    (speaker evenPrior Set.univ id (fun _ _ ↦ 1) .goal).real {.pronoun} = 1 / 3 ∧
      (speaker goalPrior Set.univ id (fun _ _ ↦ 1) .goal).real {.pronoun} = 3 / 7 := by
  constructor
  · rw [speaker_real_pronoun_of_ambiguous (π := evenPrior) (κ := fun _ _ ↦ 1) (r := .goal)
      (by simp [evenPrior]) (fun _ ↦ ENNReal.one_ne_top),
      evenPrior, cond_univ_goal_real _ (fun _ ↦ ENNReal.one_ne_top)]
    norm_num
  · rw [speaker_real_pronoun_of_ambiguous (π := goalPrior) (κ := fun _ _ ↦ 1) (r := .goal)
      (by simp [goalPrior]) (fun _ ↦ ENNReal.one_ne_top),
      goalPrior, cond_univ_goal_real _ (fun r ↦ by cases r <;> simp)]
    norm_num

/-- With different-gender characters it is `1 / 2` under either prior. -/
example :
    (speaker evenPrior {.goal} id (fun _ _ ↦ 1) .goal).real {.pronoun} = 1 / 2 ∧
      (speaker goalPrior {.goal} id (fun _ _ ↦ 1) .goal).real {.pronoun} = 1 / 2 := by
  constructor
  · exact (speaker_real_pronoun_of_unambiguous (π := evenPrior) (ref := id) (κ := fun _ _ ↦ 1)
      (s := .goal) (by simp [evenPrior]) (fun _ ↦ ENNReal.one_ne_top)).trans (by norm_num)
  · exact (speaker_real_pronoun_of_unambiguous (π := goalPrior) (ref := id) (κ := fun _ _ ↦ 1)
      (s := .goal) (by simp [goalPrior]) (fun _ ↦ ENNReal.one_ne_top)).trans (by norm_num)

/-! ### Audience design alone -/

section AudienceDesign

open KehlerRohde2013 (Position)

variable (μ : Measure Position) (κ : Form → ℝ≥0∞)

/-- The listener who inverts the audience-design speaker with a referent-blind utterance prior,
Kehler and Rohde's interpretation (13) with that speaker as production kernel. -/
noncomputable def listener : Kernel (Expression Position) Position :=
  Kernel.ofDensity μ fun e r ↦ speaker μ Set.univ id (fun f _ ↦ κ f) r {e}

theorem listener_real_subject [IsFiniteMeasure μ] :
    (listener μ κ .pronoun).real {.subject} =
      (speaker μ Set.univ id (fun f _ ↦ κ f) .subject).real {.pronoun} * μ.real {.subject} /
        ((speaker μ Set.univ id (fun f _ ↦ κ f) .subject).real {.pronoun} * μ.real {.subject} +
          (speaker μ Set.univ id (fun f _ ↦ κ f) .nonSubject).real {.pronoun} *
            μ.real {.nonSubject}) := by
  rw [measureReal_def, listener, Kernel.ofDensity_apply_singleton,
    show (Finset.univ : Finset Position) = {.subject, .nonSubject} by decide,
    Finset.sum_pair (by decide), ENNReal.toReal_div, ENNReal.toReal_add
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  rfl

theorem lt_of_prior_lt {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hxy : x < y) :
    x * a / (x * a + b) < y * a / (y * a + b) := by
  rw [div_lt_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_pos ha hb]

theorem listener_real_subject_lt [IsProbabilityMeasure μ] (hμ : 0 < μ.real {.subject})
    (hlt : μ.real {.subject} < μ.real {.nonSubject}) (ha : κ .pronoun ≠ 0) (hb : κ .other ≠ 0)
    (hfin : ∀ f, κ f ≠ ∞) :
    (listener μ κ .pronoun).real {.subject} < μ.real {.subject} := by
  have hs : μ {.subject} ≠ 0 := fun h ↦ by simp [measureReal_def, h] at hμ
  have ho : μ {.nonSubject} ≠ 0 := fun h ↦ by
    simp only [measureReal_def, h, ENNReal.toReal_zero] at hlt
    exact absurd hlt (not_lt.2 ENNReal.toReal_nonneg)
  have ha' : 0 < (κ .pronoun).toReal := ENNReal.toReal_pos ha (hfin _)
  have hb' : 0 < (κ .other).toReal := ENNReal.toReal_pos hb (hfin _)
  have hsum : μ.real {.subject} + μ.real {.nonSubject} = 1 := by
    rw [show ({.nonSubject} : Set Position) = {.subject}ᶜ by ext p; cases p <;> simp,
      measureReal_compl (.singleton _)]
    simp
  rw [listener_real_subject, speaker_real_pronoun_of_ambiguous hs hfin,
    speaker_real_pronoun_of_ambiguous ho hfin, cond_univ, ← measureReal_def, ← measureReal_def]
  set x := μ.real {.subject}
  set y := μ.real {.nonSubject}
  have hS := lt_of_prior_lt ha' hb' hμ.le hlt
  set Sx := x * (κ .pronoun).toReal / (x * (κ .pronoun).toReal + (κ .other).toReal)
  set Sy := y * (κ .pronoun).toReal / (y * (κ .pronoun).toReal + (κ .other).toReal)
  have hSx : 0 < Sx := by positivity
  have hy : 0 < y := by linarith
  have key : 0 < (Sy - Sx) * (x * y) := mul_pos (sub_pos.2 hS) (mul_pos hμ hy)
  have e : Sx * x = Sx * x * (x + y) := by rw [hsum, mul_one]
  rw [div_lt_iff₀ (add_pos (mul_pos hSx hμ) (mul_pos (hSx.trans hS) hy))]
  nlinarith [key, e]

/-- No audience-design speaker with a referent-blind utterance prior prints Kehler and Rohde's
passive interpretation, since their passive subject is the less expected character (Table 7) and the
pronoun raises its interpretation to .60 (Table 10). -/
theorem not_audienceDesign_passive [IsProbabilityMeasure μ] (hμ : 0 < μ.real {.subject})
    (hlt : μ.real {.subject} < μ.real {.nonSubject}) (ha : κ .pronoun ≠ 0) (hb : κ .other ≠ 0)
    (hfin : ∀ f, κ f ≠ ∞) :
    ¬ RoundsTo ((listener μ κ .pronoun).real {.subject})
      (KehlerRohde2013.subjectBiases .passive).actual := by
  have hL := listener_real_subject_lt μ κ hμ hlt ha hb hfin
  have hsum : μ.real {.subject} + μ.real {.nonSubject} = 1 := by
    rw [show ({.nonSubject} : Set Position) = {.subject}ᶜ by ext p; cases p <;> simp,
      measureReal_compl (.singleton _)]
    simp
  intro h
  simp only [RoundsTo, KehlerRohde2013.subjectBiases, Data.Statistics.Decimal.toRat, abs_le] at h
  norm_num at h
  linarith [h.1]

/-- The passive's subject is the less expected character in Table 7. -/
example : KehlerRohde2013.voicePrior .passive .subject <
    KehlerRohde2013.voicePrior .passive .nonSubject := by
  decide

/-- With a referent-blind utterance prior the pronoun is produced at one rate for both characters
exactly when the listener's prior is uniform, so Hobbs's inert pronoun is audience design over a
uniform prior. -/
theorem speaker_pronoun_eq_iff [IsProbabilityMeasure μ] (hs : μ {.subject} ≠ 0)
    (ho : μ {.nonSubject} ≠ 0) (ha : κ .pronoun ≠ 0) (hb : κ .other ≠ 0) (hfin : ∀ f, κ f ≠ ∞) :
    (speaker μ Set.univ id (fun f _ ↦ κ f) .subject).real {.pronoun} =
        (speaker μ Set.univ id (fun f _ ↦ κ f) .nonSubject).real {.pronoun} ↔
      μ.real {.subject} = μ.real {.nonSubject} := by
  have ha' : 0 < (κ .pronoun).toReal := ENNReal.toReal_pos ha (hfin _)
  have hb' : 0 < (κ .other).toReal := ENNReal.toReal_pos hb (hfin _)
  rw [speaker_real_pronoun_of_ambiguous hs hfin, speaker_real_pronoun_of_ambiguous ho hfin,
    cond_univ, ← measureReal_def, ← measureReal_def]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (lt_of_prior_lt ha' hb' measureReal_nonneg hlt).ne h
  · exact (lt_of_prior_lt ha' hb' measureReal_nonneg hlt).ne h.symm

end AudienceDesign

/-! ### The conjecture -/

/-- Outside the continuations that focus the end state, the utterance prior depends on the
referent only through its position. -/
def EndStateConfined (pos : R → KehlerRohde2013.Position) (κ : Form → R × Relation → ℝ≥0∞) :
    Prop :=
  ∀ f r r' c, ¬ FocusesEndState c.toCoherence → pos r = pos r' → κ f (r, c) = κ f (r', c)

/-- Under the conjecture, outside end-state continuations, the unambiguous pronoun rate of two
referents in the same position is the same, whatever their thematic roles and priors. -/
theorem pronounRate_eq_of_not_focusesEndState {pos : R → KehlerRohde2013.Position}
    {κ : Form → R × Relation → ℝ≥0∞} (hκ : EndStateConfined pos κ) (hfin : ∀ f s, κ f s ≠ ∞)
    {π π' : Measure R} [IsFiniteMeasure π] [IsFiniteMeasure π'] {r r' : R} {c : Relation}
    (hc : ¬ FocusesEndState c.toCoherence) (hpos : pos r = pos r') (hπ : π {r} ≠ 0)
    (hπ' : π' {r'} ≠ 0) :
    (speaker π {r} Prod.fst κ (r, c)).real {.pronoun} =
      (speaker π' {r'} Prod.fst κ (r', c)).real {.pronoun} := by
  have h₁ := speaker_real_pronoun_of_unambiguous (ref := Prod.fst) (κ := κ) (s := (r, c)) hπ
    (hfin · _)
  have h₂ := speaker_real_pronoun_of_unambiguous (ref := Prod.fst) (κ := κ) (s := (r', c)) hπ'
    (hfin · _)
  dsimp only at h₁ h₂
  rw [h₁, h₂, hκ .pronoun r r' c hc hpos, hκ .other r r' c hc hpos]

/-! ### The noisy channel -/

section NoisyChannel

open scoped Classical in
/-- The likelihood of an expression for a referent through a channel in which a pronoun that does
not fit the referent is heard as one that does with probability `ε`, and a name is heard as
said. -/
noncomputable def noisyLikelihood (P : Set R) (ε : ℝ≥0∞) : Expression R → R → ℝ≥0∞
  | pronoun, r => if r ∈ P then 1 else ε
  | name r', r => if r = r' then 1 else 0

/-- The noisy literal listener reweights the prior by the noisy likelihood. -/
noncomputable def noisyListener (π : Measure R) (P : Set R) (ε : ℝ≥0∞) :
    Kernel (Expression R) R :=
  Kernel.ofDensity π (noisyLikelihood P ε)

/-- The speaker who reasons about the noisy literal listener. -/
noncomputable def noisySpeaker (π : Measure R) (P : Set R) (ε : ℝ≥0∞) (ref : S → R)
    (κ : Form → S → ℝ≥0∞) : Kernel S (Expression R) :=
  Kernel.ofWeights fun s e ↦ noisyListener π P ε e {ref s} * κ e.form s

instance (π : Measure R) (P : Set R) (ε : ℝ≥0∞) (ref : S → R) (κ : Form → S → ℝ≥0∞) :
    IsFiniteKernel (noisySpeaker π P ε ref κ) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

omit [MeasurableSpace R] [Fintype R] [DiscreteMeasurableSpace R] in
theorem noisyLikelihood_zero (P : Set R) :
    noisyLikelihood P 0 = fun e ↦ (e.sem P).indicator 1 := by
  classical
  funext e r
  cases e <;> simp [noisyLikelihood, sem, Set.indicator_apply]

theorem noisyListener_zero (π : Measure R) (P : Set R) (e : Expression R) :
    noisyListener π P 0 e = literalListener π P e := by
  rw [noisyListener, noisyLikelihood_zero,
    Kernel.ofDensity_indicator_one_apply π (fun e ↦ e.sem P) e .of_discrete]
  rfl

theorem noisySpeaker_zero (π : Measure R) (P : Set R) (ref : S → R) (κ : Form → S → ℝ≥0∞) :
    noisySpeaker π P 0 ref κ = speaker π P ref κ := by
  simp only [noisySpeaker, speaker, noisyListener_zero]

theorem noisyListener_name_apply [IsFiniteMeasure π] {P : Set R} {ε : ℝ≥0∞} {r : R}
    (hπ : π {r} ≠ 0) : noisyListener π P ε (name r) {r} = 1 := by
  classical
  rw [noisyListener, Kernel.ofDensity_apply_singleton,
    Finset.sum_eq_single r (fun r' _ h ↦ by simp [noisyLikelihood, h]) (by simp)]
  simp [noisyLikelihood, ENNReal.div_self hπ (measure_ne_top _ _)]

theorem noisyListener_name_apply_of_ne {P : Set R} {ε : ℝ≥0∞} {r r' : R} (h : r' ≠ r) :
    noisyListener π P ε (name r') {r} = 0 := by
  classical
  rw [noisyListener, Kernel.ofDensity_apply_singleton]
  simp [noisyLikelihood, Ne.symm h]

theorem noisySpeaker_real_pronoun [IsFiniteMeasure π] {ε : ℝ≥0∞} {κ : Form → R → ℝ≥0∞} {r : R}
    (hπ : π {r} ≠ 0) (hκ : ∀ f, κ f r ≠ ∞) (hfin : noisyListener π {r} ε pronoun {r} ≠ ∞) :
    (noisySpeaker π {r} ε id κ r).real {.pronoun} =
      (noisyListener π {r} ε pronoun {r}).toReal * (κ .pronoun r).toReal /
        ((noisyListener π {r} ε pronoun {r}).toReal * (κ .pronoun r).toReal +
          (κ .other r).toReal) := by
  classical
  have hn : ∀ r', noisyListener π {r} ε (name r') {r} * κ (name r').form r =
      if r' = r then κ .other r else 0 := fun r' ↦ by
    split_ifs with h
    · subst h; rw [noisyListener_name_apply hπ, one_mul]; rfl
    · rw [noisyListener_name_apply_of_ne h, zero_mul]
  have htop : ∀ e : Expression R, noisyListener π {r} ε e {r} * κ e.form r ≠ ∞ := fun e ↦ by
    cases e with
    | pronoun => exact ENNReal.mul_ne_top hfin (hκ _)
    | name r' => rw [hn]; split_ifs <;> simp [hκ]
  rw [noisySpeaker, Kernel.ofWeights_real_singleton _ _ htop, Expression.sum_eq]
  simp only [id_eq, hn]
  rw [Finset.sum_eq_single r (fun r' _ h ↦ by simp [h]) (by simp)]
  simp [form, ENNReal.toReal_mul]

theorem noisyListener_real_pronoun (π : Measure Role) [IsProbabilityMeasure π] (r : Role)
    {ε : ℝ≥0∞} (hε : ε ≠ ∞) :
    (noisyListener π {r} ε pronoun {r}).toReal =
      π.real {r} / (π.real {r} + ε.toReal * (1 - π.real {r})) := by
  have hsum : π.real {.source} + π.real {.goal} = 1 := by
    rw [show ({.goal} : Set Role) = {.source}ᶜ by ext p; cases p <;> simp,
      measureReal_compl (.singleton _)]
    simp
  rw [noisyListener, Kernel.ofDensity_apply_singleton,
    show (Finset.univ : Finset Role) = {.source, .goal} by decide, Finset.sum_pair (by decide)]
  cases r <;> simp only [noisyLikelihood, Set.mem_singleton_iff, reduceCtorEq, ite_true, ite_false,
    one_mul, ENNReal.toReal_div, ← measureReal_def]
  · rw [ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.mul_ne_top hε (measure_ne_top _ _)),
      ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
      show π.real {.goal} = 1 - π.real {.source} by linarith]
  · rw [ENNReal.toReal_add (ENNReal.mul_ne_top hε (measure_ne_top _ _)) (measure_ne_top _ _),
      ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
      show π.real {.source} = 1 - π.real {.goal} by linarith, add_comm]

/-- Through a noisy channel, a pronoun that fits only the intended character still depends on the
prior, its rate rising with the character's prior mass. With the same utterance prior in both
contexts, as for two characters in the same position, Kravtchenko's noisy channel predicts a
predictability effect with different-gender characters in every continuation, where the end-state
conjecture predicts none outside Occasion and Result (`pronounRate_eq_of_not_focusesEndState`). -/
theorem noisySpeaker_real_pronoun_lt {π π' : Measure Role} [IsProbabilityMeasure π]
    [IsProbabilityMeasure π'] {r r' : Role} {ε : ℝ≥0∞} (hε0 : ε ≠ 0) (hε : ε ≠ ∞)
    {κ : Form → ℝ≥0∞} (ha : κ .pronoun ≠ 0) (hb : κ .other ≠ 0) (hfin : ∀ f, κ f ≠ ∞)
    (hπ : 0 < π.real {r}) (hlt : π.real {r} < π'.real {r'}) (hlt1 : π'.real {r'} < 1) :
    (noisySpeaker π {r} ε id (fun f _ ↦ κ f) r).real {.pronoun} <
      (noisySpeaker π' {r'} ε id (fun f _ ↦ κ f) r').real {.pronoun} := by
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε0 hε
  have ha' : 0 < (κ .pronoun).toReal := ENNReal.toReal_pos ha (hfin _)
  have hb' : 0 < (κ .other).toReal := ENNReal.toReal_pos hb (hfin _)
  have hπ' : 0 < π'.real {r'} := hπ.trans hlt
  have h0 : π {r} ≠ 0 := fun h ↦ by simp [measureReal_def, h] at hπ
  have h0' : π' {r'} ≠ 0 := fun h ↦ by simp [measureReal_def, h] at hπ'
  have hq : noisyListener π {r} ε pronoun {r} ≠ ∞ := by
    unfold noisyListener; exact measure_ne_top _ _
  have hq' : noisyListener π' {r'} ε pronoun {r'} ≠ ∞ := by
    unfold noisyListener; exact measure_ne_top _ _
  rw [noisySpeaker_real_pronoun h0 (fun f ↦ hfin f) hq,
    noisySpeaker_real_pronoun h0' (fun f ↦ hfin f) hq', noisyListener_real_pronoun π r hε,
    noisyListener_real_pronoun π' r' hε]
  refine lt_of_prior_lt ha' hb' (div_nonneg hπ.le (by nlinarith)) ?_
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_pos he (sub_pos.2 hlt)]

end NoisyChannel

end Lab.ReferringExpressions
