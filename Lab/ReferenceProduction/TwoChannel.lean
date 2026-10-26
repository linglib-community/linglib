module

public import Studies.KehlerRohde2013

/-!
# Two channels of pronoun production

This file models a speaker who weighs each referring expression for a referent by two factors:
how surely a listener with prior `π` recovers the referent from the expression's literal meaning,
the literal listener of the rational speech act model, and how easy the expression's form is for
the speaker in the speaker's current state, which may include the plan for the continuation. When
the pronoun is unambiguous the listener's factor is the same for the pronoun and the name, so the
pronoun rate is the ratio of the two eases, whatever the prior. A speaker whose ease ignores the
plan has a production kernel on referents, as in Kehler and Rohde's factorization, but when the
pronoun is ambiguous its rate depends on the prior, against the strong form of their model.

The conjecture recorded here is that the ease reads the referent's thematic role, and so the
predictability of the referent, only in continuations that focus the end state of the previous
eventuality. With different-gender characters, predictability effects on pronominalization then
appear only in Occasion and Result continuations; with same-gender characters they may also
appear through the prior.

## Main statements

* `speaker_real_pronoun_of_unambiguous`: with an unambiguous pronoun the rate is the ease ratio.
* `speaker_comap_fst`: a plan-blind ease gives a production kernel on referents.
* `speaker_real_pronoun_of_ambiguous`: with an ambiguous pronoun the rate depends on the prior.
* `pronounRate_eq_of_not_focusesEndState`: under the conjecture, outside end-state continuations
  the unambiguous pronoun rate depends on the referent's position alone.

## Implementation notes

* Provenance. No paper states the conjecture; it is proposed here. The speaker over a salience
  prior is Orita, Vornov, Feldman and Daumé's at `α = 1`, with their cost replaced by an ease
  that may depend on the referent and the plan. The larger predictability effects expected with
  same-gender characters are Kravtchenko's prediction, and the factorization and its strong form
  are Kehler and Rohde's. That predictability effects are larger with transfer-of-possession
  verbs, whose Goal bias lives in continuations that advance the narrative, is Rosa and Arnold's
  suggestion, weakly supported in Liao, Brochhagen, Boleda and Mayol's meta-analysis.
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

namespace Lab.ReferenceProduction

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open KehlerRohde2013 (Form Role Relation FocusesEndState)

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
listener's mass on the referent and the ease of its form. -/
noncomputable def speaker (π : Measure R) (P : Set R) (ref : S → R) (κ : Form → S → ℝ≥0∞) :
    Kernel S (Expression R) :=
  Kernel.ofWeights fun s e ↦ literalListener π P e {ref s} * κ e.form s

instance (P : Set R) (e : Expression R) : IsZeroOrProbabilityMeasure (literalListener π P e) := by
  unfold literalListener; infer_instance

theorem literalListener_apply_self [IsFiniteMeasure π] {P : Set R} {e : Expression R} {r : R}
    (h : e.sem P = {r}) (hπ : π {r} ≠ 0) : literalListener π P e {r} = 1 := by
  rw [literalListener, h, cond_apply (.singleton r), Set.inter_self,
    ENNReal.inv_mul_cancel hπ (measure_ne_top _ _)]

theorem literalListener_name_apply_of_ne {P : Set R} {r r' : R} (h : r' ≠ r) :
    literalListener π P (name r') {r} = 0 := by
  rw [literalListener, sem, cond_apply (.singleton r'),
    Set.singleton_inter_eq_empty.2 (Set.mem_singleton_iff.not.2 h), measure_empty, mul_zero]

/-- With an unambiguous pronoun the pronoun rate is the ratio of the eases, whatever the prior. -/
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

/-- A speaker whose ease ignores the plan for the continuation has a production kernel on
referents, as in Kehler and Rohde's factorization. -/
theorem speaker_comap_fst {C : Type*} [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] (P : Set R) (κ : Form → R → ℝ≥0∞) :
    speaker π P Prod.fst (fun f s ↦ κ f s.1) =
      (speaker π P id κ).comap (Prod.fst : R × C → R) measurable_fst := by
  ext1 s
  rfl

/-- With a pronoun that fits every referent the pronoun rate rises with the referent's normalized
prior mass, so it depends on the prior. -/
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

/-- With same-gender characters and equal eases the Goal's pronoun rate is `1 / 3` under the even
prior and `3 / 7` under the prior favouring the Goal. -/
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

/-! ### The conjecture -/

/-- Outside the continuations that focus the end state, the ease depends on the referent only
through its position. -/
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

end Lab.ReferenceProduction
