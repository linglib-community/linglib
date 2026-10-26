module

public import Studies.CremersWilcoxSpector2023
public import Studies.Spector2017
public import Linglib.Logic.Trivalent.Supervaluation
public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Semantics.Composition.Tree
public import Linglib.Data.Examples.Spector2025

/-!
# Spector (2025): Supervaluationist RSA

Spector argues against reading exhaustification as presuppositional, Bassi, Del Pinal and
Sauerland's trivalent `pex` under Strong Kleene projection with Doron and Wehbe's
Post-Accommodation Informativity. In the marbles context of (11), where the marbles are expected
to behave alike, *some of the marbles sank* passes that constraint yet is odd, while *some but not
all of the marbles sank* is fine. He replaces `pex` by a bivalent exhaustivity operator and lets
every sentence be underspecified between a parse with the operator and one without. A speaker who
is maximally averse to the risk of being misread values a message at a world by its least utility
over its parses, the log of the literal listener's probability of the world less the message's
cost (the MaxiMin rule (28)), and chooses by a softmax of that value.

The parse of a scalar item with the operator is the K3 reading of its `pex` meaning and the parse
without it the LP reading, and Strong Kleene logic is supervaluation over these readings, each
occurrence read at its own standard. So the model is the MaxiMin speaker over the two readings of
a trivalent meaning. She uses a message exactly where it is true, its K3 reading, and she ranks the
messages true at a world by the surprisal of their LP reading less the cost, the LP reading being
the weaker, whatever the world and the rationality. Silence beats a message whose LP reading is
too probable, and where some but not all is improbable *some but not all* beats *some* and *not
all*.

## Main statements

* `eval_strongKleene_pexIE_eq_one_iff`: a sentence is true by Strong Kleene, its scalar items read
  by `pex`, exactly when all its parses are true, (21)–(24).
* `supervaluationOn_parses_eq_of_monotone`: under a raised monotone quantifier, truth on all parses
  is the Strong Kleene value.
* `exactlyTwo_parses_false_entitywise_undefined`: under *exactly two* it is not.
* `speaker_readings_real_lt_iff`: the speaker ranks the true messages by the surprisal of their LP
  reading less the cost.
* `judgments_11`: in the marbles context *some* passes Post-Accommodation Informativity and loses to
  *some but not all*.

## Implementation notes

* The speaker's weight for a message is the exponential of the rationality times its MaxiMin
  value, written without logarithms as `RSA.speaker` writes an expected utility: the least
  literal-listener mass over the parses, to the power of the rationality, times the cost weight.
  The speaker takes any finite family of parses; the model's parses are the readings of the `pex`
  meaning at the two designation standards.
* The worlds are those of `Spector2017`, no marble, some but not all, or all of them sank. *Some* is
  exhaustified against *all* and *not all* against *no*; the other messages have no other
  alternatives.
* Priors, rationality and costs are arguments, of which the paper's tables are instances.

## Errata

* Footnote 13 says that the normalizing sum is positive exactly when at each world some message is
  true "under a certain parse". The MaxiMin speaker gives no weight to a message false under one
  of its parses, nor at a world of prior probability zero (`speaker_apply_singleton_ne_zero_iff`),
  so the condition is that at each world of positive prior some message be true under all its
  parses.

## TODO

* Under a downward-entailing operator the least informative parse reads the item with the
  operator ((22), (25)): the weakest bivalent variant of a sentence reads each occurrence by its
  polarity. The Magri effects (18) and (26) fit a three-world model of *no*, *one* and *several*
  pets or hats; (17) needs a quantifier, and the gradience of (29) a model with degrees.
* Footnote 12: the expected-utility speaker of `Spector2017` and `CremersWilcoxSpector2023` also
  derives Truth on all parses, and ranks by a geometric mean of the readings' probabilities.
* The contrast of (11a) with *only some*, (11c), and the QUD-sensitive refinement of §8.

## References

* [spector-2025]
* [spector-2017]
* [cremers-wilcox-spector-2023]
* [bassi-delpinal-sauerland-2021]
* [doron-wehbe-2022]
* [wehbe-doron-2025]
* [degen-etal-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Exhaustification Presupposition
open scoped ENNReal

namespace Spector2025

/-! ### Readings of a trivalent meaning -/

section Readings

variable {W U : Type*}

/-- The reading of a trivalent meaning at a designation standard: where a message is true, at K3,
or not false, at LP. -/
def readings (m : U → W → SignType) (d : Trivalent.Designation) (σ : U) : Set W :=
  {w | d.threshold ≤ m σ w}

instance (m : U → W → SignType) (d : Trivalent.Designation) (σ : U) :
    DecidablePred (· ∈ readings m d σ) :=
  fun w ↦ inferInstanceAs (Decidable (d.threshold ≤ m σ w))

variable {m : U → W → SignType} {w : W} {σ : U}

theorem forall_mem_readings_iff : (∀ d, w ∈ readings m d σ) ↔ m σ w = 1 := by
  cases h : m σ w <;> simp only [readings, Set.mem_ofPred_eq, h] <;> decide

theorem readings_lp : readings m .lp σ = {w | m σ w ≠ -1} := by
  ext; simp [readings]

/-- The LP reading is the weaker. -/
theorem readings_k3_subset_lp : readings m .k3 σ ⊆ readings m .lp σ := fun _ h ↦
  (show Trivalent.Designation.lp.threshold ≤ Trivalent.Designation.k3.threshold by decide).trans h

variable {ALT : U → Set (Set W)} {lit : U → Set W}

/-- The K3 reading of `pex` is its parse with the exhaustivity operator. -/
theorem readings_pexIE_k3 :
    readings (fun σ ↦ pexIE (ALT σ) (lit σ) (ALT σ)) .k3 σ = exhIE (ALT σ) (lit σ) := by
  have h1 (a : SignType) : 1 ≤ a ↔ a = 1 := by cases a <;> decide
  ext; simp [readings, h1, pexIE_eq_one_iff_mem_exhIE subset_rfl]

/-- The LP reading of `pex` is its parse without the exhaustivity operator. -/
theorem readings_pexIE_lp : readings (fun σ ↦ pexIE (ALT σ) (lit σ) (ALT σ)) .lp σ = lit σ := by
  ext; simp [readings, pexIE_eq_neg_one_iff]

/-- A sentence whose scalar items are read by `pex` is true by Strong Kleene exactly where each of
its bivalent variants is true, the variant reading each item at its own standard, by its parse with
the operator at K3 (`readings_pexIE_k3`) and without it at LP (`readings_pexIE_lp`) (§5). -/
theorem eval_strongKleene_pexIE_eq_one_iff [DecidableEq U] (φ : Trivalent.Formula U) :
    Trivalent.Formula.eval .strongKleene (fun σ ↦ pexIE (ALT σ) (lit σ) (ALT σ) w) φ = 1 ↔
      ∀ ψ ∈ φ.bivalentVariants, Trivalent.Formula.evalBool (fun x ↦
        decide (w ∈ readings (fun σ ↦ pexIE (ALT σ) (lit σ) (ALT σ)) x.2 x.1)) ψ = true := by
  rw [Trivalent.Formula.eval_strongKleene_eq_supervaluation, SignType.supervaluation_eq_one_iff]
  rfl

end Readings

/-! ### Quantifiers on the composition engine (§5)

Spector says that Truth on all parses extends to quantifiers. A parse resolves each occurrence of
a word before interpretation (`PhraseStructure.Tree.readings`), so a raised quantifier's parses
read its scalar predicate at one standard for every entity it ranges over. Strong Kleene reads
each entity at a standard of its own, as the set effect does. The two agree under a monotone or
antitone quantifier and come apart under *exactly two*. -/

section Quantifiers

open Montague PhraseStructure
open Trivalent (Designation)

/-- The words of a sentence whose quantifier is raised over a scalar predicate. -/
inductive QWord
  | quant
  | scalar
  deriving DecidableEq

variable {E : Type} (Q : (E → Prop) → Prop) (p : E → SignType)

/-- The quantifier, and the trivalent scalar predicate read at both standards. -/
def lexicon : QWord → Option (Denotation E Unit SetM)
  | .quant => some ⟨(.e ⇒ .t) ⇒ .t, pure Q⟩
  | .scalar => some ⟨.e ⇒ .t, Set.range fun (d : Designation) x ↦ d.threshold ≤ p x⟩

/-- The quantifier raised over the scalar predicate, `[Q [λ₁ [t₁ scalar]]]`. -/
def raised : Tree Unit QWord := .bin (.leaf .quant) (.binder 1 (.bin (.tr 1) (.leaf .scalar)))

/-- The parses of a sentence: its truth values when each occurrence of a word is resolved to one
of the values its denotation collects. -/
def parses (lex : QWord → Option (Denotation E Unit SetM)) (g : Assignment E)
    (t : Tree Unit QWord) : Set Prop :=
  {b | (⟨.t, b⟩ : Denotation E Unit Id) ∈ Tree.readings (Tree.wordReadings lex) g t}

/-- The parses of a raised quantifier read the scalar predicate at one standard for every entity. -/
theorem parses_raised (g : Assignment E) :
    parses (lexicon Q p) g raised =
      Set.range fun d : Designation ↦ Q fun x ↦ d.threshold ≤ p x := by
  ext b
  simp only [parses, raised, Set.mem_ofPred_eq, Tree.mem_readings_node_binary,
    Tree.readings_terminal, Tree.mem_readings_bind, Set.mem_range]
  constructor
  · rintro ⟨⟨τ₁, v₁⟩, ⟨X₁, h₁, hm₁⟩, d₂, ⟨r, hr, hd₂⟩, hb⟩
    simp only [lexicon, Option.some.injEq, Sigma.mk.inj_iff] at h₁
    obtain ⟨rfl, h₁⟩ := h₁
    obtain rfl := eq_of_heq h₁
    obtain rfl : Q = v₁ := hm₁.symm
    obtain ⟨cs, rfl, hcs⟩ := Tree.map_eq_node_iff.1 hr
    obtain ⟨r₁, cs₁, rfl, h₁, hcs₁⟩ := List.map_eq_cons_iff.mp hcs
    obtain ⟨r₂, cs₂, rfl, h₂, hcs₂⟩ := List.map_eq_cons_iff.mp hcs₁
    obtain rfl := List.map_eq_nil_iff.mp hcs₂
    obtain rfl := Tree.map_eq_trace_iff.1 h₁
    obtain ⟨⟨⟨w, τ, v⟩, X, hX, hv⟩, rfl, hw⟩ := Tree.map_eq_terminal_iff.1 h₂
    clear hr hcs hcs₁ hcs₂ h₁ h₂
    obtain rfl : w = .scalar := hw
    simp only [lexicon, Option.some.injEq, Sigma.mk.inj_iff] at hX
    obtain ⟨rfl, hX⟩ := hX
    obtain rfl := eq_of_heq hX
    obtain ⟨d, hd⟩ := id hv
    subst hd
    obtain rfl := Option.some.inj hd₂
    exact ⟨d, eq_of_heq (Sigma.mk.inj_iff.1 (Option.some.inj hb)).2⟩
  · rintro ⟨d, rfl⟩
    exact ⟨⟨(.e ⇒ .t) ⇒ .t, Q⟩, ⟨_, rfl, rfl⟩, ⟨.e ⇒ .t, fun x ↦ d.threshold ≤ p x⟩,
      ⟨.bin (.tr 1) (.leaf ⟨(.scalar, ⟨.e ⇒ .t, fun x ↦ d.threshold ≤ p x⟩), _, rfl, d, rfl⟩),
        rfl, rfl⟩, rfl⟩

/-- Under the set effect the raised quantifier reads the scalar predicate at a standard for each
entity. -/
theorem interp_raised (g : Assignment E) :
    Tree.interp (lexicon Q p) g raised = some ⟨.t,
      (Set.range fun c : E → Designation ↦ Q fun x ↦ (c x).threshold ≤ p x : Set Prop)⟩ := by
  refine congrArg (fun v : Set Prop ↦ some (⟨.t, v⟩ : Denotation E Unit SetM)) ?_
  simp only [Mode.evalM, Set.pure_def, Set.fmap_eq_image, Set.image_singleton, Term.evalM,
    Function.update_self, Set.seq_eq_set_seq, Option.map_some, Option.bind_some, Set.singleton_seq,
    Mode.eval, ← Set.range_comp, Option.getD_some]
  change Q '' Set.univ.pi (fun x ↦ Set.range fun d : Designation ↦ d.threshold ≤ p x) = _
  rw [← Set.range_piMap, ← Set.range_comp]
  rfl

/-- Under the universal, the set effect computes the Strong Kleene universal. -/
example [Fintype E] [DecidableEq E] (g : Assignment E) {X : SetM Prop}
    (hX : Tree.interp (lexicon (fun P ↦ ∀ x, P x) p) g raised = some ⟨.t, X⟩) :
    SignType.supervaluationOn X.run id = Trivalent.forallStrong p := by
  obtain rfl := sigma_mk_injective (Option.some_injective _ (hX.symm.trans (interp_raised _ p g)))
  dsimp only [SetM.run]
  rw [← Set.image_univ, SignType.supervaluationOn_image, Function.id_comp, ← Finset.coe_univ,
    SignType.supervaluationOn_coe_finset, Trivalent.forallStrong_eq_supervaluation]

variable {Q}

/-- Under a raised monotone quantifier, truth on all parses is the Strong Kleene value. -/
theorem supervaluationOn_parses_eq_of_monotone (hQ : Monotone Q) (g : Assignment E)
    {X : SetM Prop} (hX : Tree.interp (lexicon Q p) g raised = some ⟨.t, X⟩) :
    SignType.supervaluationOn (parses (lexicon Q p) g raised) id =
      SignType.supervaluationOn X.run id := by
  obtain rfl := sigma_mk_injective (Option.some_injective _ (hX.symm.trans (interp_raised Q p g)))
  dsimp only [SetM.run]
  rw [parses_raised, ← Set.image_univ, ← Set.image_univ, SignType.supervaluationOn_image,
    SignType.supervaluationOn_image]
  exact (Trivalent.supervaluationOn_pi_eq_const_of_monotone p hQ).symm

/-- Under a raised antitone quantifier, truth on all parses is the Strong Kleene value. -/
theorem supervaluationOn_parses_eq_of_antitone (hQ : Antitone Q) (g : Assignment E)
    {X : SetM Prop} (hX : Tree.interp (lexicon Q p) g raised = some ⟨.t, X⟩) :
    SignType.supervaluationOn (parses (lexicon Q p) g raised) id =
      SignType.supervaluationOn X.run id := by
  obtain rfl := sigma_mk_injective (Option.some_injective _ (hX.symm.trans (interp_raised Q p g)))
  dsimp only [SetM.run]
  rw [parses_raised, ← Set.image_univ, ← Set.image_univ, SignType.supervaluationOn_image,
    SignType.supervaluationOn_image]
  exact (Trivalent.supervaluationOn_pi_eq_const_of_antitone p hQ).symm

end Quantifiers

/-! ### The MaxiMin speaker (§6) -/

section Speaker

variable {W U ι : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W] [Fintype U]
  [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype ι] [Nonempty ι]

/-- The MaxiMin speaker (28) weighs a message at a world by the least mass the literal listener of
one of its parses gives the world, to the power of the rationality, times the cost weight. -/
noncomputable def speaker (μ : Measure W) (α : ℝ) (C : U → ℝ) (parse : ι → U → Set W) :
    Kernel W U :=
  Kernel.ofWeights fun w σ ↦
    (⨅ i, listener μ (truthful (parse i)) σ {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C σ)))

instance (μ : Measure W) (α : ℝ) (C : U → ℝ) (parse : ι → U → Set W) :
    IsFiniteKernel (speaker μ α C parse) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

variable {μ : Measure W} [IsFiniteMeasure μ] {α : ℝ} {C : U → ℝ} {parse : ι → U → Set W} {w : W}
  {σ τ : U}

omit [Fintype W] [DiscreteMeasurableSpace W] [Fintype ι] [IsFiniteMeasure μ] in
private theorem weight_ne_top (hα : 0 ≤ α) (w : W) (σ : U) :
    (⨅ i, listener μ (truthful (parse i)) σ {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C σ))) ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα
    (ne_top_of_le_ne_top (measure_ne_top _ _) (iInf_le _ (Classical.arbitrary ι))))
    ENNReal.ofReal_ne_top

omit [Fintype W] in
private theorem weight_eq_zero_iff (hα : 0 < α) :
    (⨅ i, listener μ (truthful (parse i)) σ {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C σ))) = 0 ↔
      ∃ i, w ∉ parse i σ ∨ μ {w} = 0 := by
  rw [mul_eq_zero, or_iff_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne',
    ENNReal.rpow_eq_zero_iff_of_pos hα]
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ le_antisymm ((iInf_le _ i).trans ?_) bot_le⟩
  · obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i ↦ listener μ (truthful (parse i)) σ {w})
    refine ⟨i, ?_⟩
    by_contra! hc
    exact (listener_truthful_apply_singleton_ne_zero_iff μ (parse i) σ w).2 hc (hi.trans h)
  · exact (not_not.1 fun hne ↦ ((listener_truthful_apply_singleton_ne_zero_iff μ (parse i) σ w).1
      hne).elim fun h₁ h₂ ↦ hi.elim (· h₁) h₂).le

/-- The speaker uses a message at a world of positive prior mass exactly when it is true there on
all its parses, the principle of Truth on all parses. -/
theorem speaker_apply_singleton_ne_zero_iff (hα : 0 < α) (hw : μ {w} ≠ 0) :
    speaker μ α C parse w {σ} ≠ 0 ↔ ∀ i, w ∈ parse i σ := by
  refine ⟨fun h i ↦ by_contra fun hi ↦ h (Kernel.ofWeights_apply_singleton_eq_zero
    ((weight_eq_zero_iff hα).2 ⟨i, .inl hi⟩)), fun h ↦ ?_⟩
  refine Kernel.ofWeights_apply_singleton_ne_zero (fun h0 ↦ ?_) (weight_ne_top hα.le w)
  obtain ⟨i, hi | hi⟩ := (weight_eq_zero_iff hα).1 h0
  exacts [hi (h i), hw hi]

theorem speaker_apply_singleton_eq_zero (hα : 0 < α) {i : ι} (h : w ∉ parse i σ) :
    speaker μ α C parse w {σ} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero ((weight_eq_zero_iff hα).2 ⟨i, .inl h⟩)

theorem listener_apply_singleton_ne_zero_iff_forall_mem (hα : 0 < α) :
    listener μ (speaker μ α C parse) σ {w} ≠ 0 ↔ μ {w} ≠ 0 ∧ ∀ i, w ∈ parse i σ := by
  rw [RSA.listener_apply_singleton_ne_zero_iff]
  exact and_congr_right fun hw ↦ speaker_apply_singleton_ne_zero_iff hα hw

omit [Fintype W] [DiscreteMeasurableSpace W] [Fintype U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [Fintype ι] in
private theorem toReal_iSup_pos (hw : μ {w} ≠ 0) (h : ∀ i, w ∈ parse i σ) :
    0 < (⨆ i, μ (parse i σ)).toReal :=
  ENNReal.toReal_pos ((pos_iff_ne_zero.2 hw).trans_le ((measure_mono (Set.singleton_subset_iff.2
    (h (Classical.arbitrary ι)))).trans (le_iSup (fun i ↦ μ (parse i σ)) _))).ne'
    (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
      (iSup_le fun _ ↦ measure_mono (Set.subset_univ _)))

omit [Fintype W] [Fintype ι] in
private theorem weight_toReal (hw : μ {w} ≠ 0) (h : ∀ i, w ∈ parse i σ) :
    ((⨅ i, listener μ (truthful (parse i)) σ {w}) ^ α *
        ENNReal.ofReal (Real.exp (-(α * C σ)))).toReal =
      Real.exp (α * (Real.log (μ.real {w}) - Real.log (⨆ i, μ (parse i σ)).toReal - C σ)) := by
  have hM := toReal_iSup_pos hw h
  have hμw : 0 < μ.real {w} := ENNReal.toReal_pos hw (measure_ne_top _ _)
  rw [iInf_congr fun i ↦ listener_truthful_apply_singleton μ (parse i) (h i),
    ← ENNReal.iInf_mul fun h ↦ absurd h (measure_ne_top _ _), ← ENNReal.inv_iSup,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ← measureReal_def,
    Real.rpow_def_of_pos (mul_pos (inv_pos.2 hM) hμw), ← Real.exp_add,
    Real.log_mul (inv_pos.2 hM).ne' hμw.ne', Real.log_inv]
  ring_nf

/-- Among messages true on all their parses at a world, the speaker ranks by the surprisal of the
least informative parse less the cost, whatever the world and the rationality. -/
theorem speaker_real_lt_iff (hα : 0 < α) (hw : μ {w} ≠ 0) (hσ : ∀ i, w ∈ parse i σ)
    (hτ : ∀ i, w ∈ parse i τ) :
    (speaker μ α C parse w).real {σ} < (speaker μ α C parse w).real {τ} ↔
      -Real.log (⨆ i, μ (parse i σ)).toReal - C σ <
        -Real.log (⨆ i, μ (parse i τ)).toReal - C τ := by
  have hσ0 := (weight_eq_zero_iff (C := C) hα).not.2 fun ⟨i, hi⟩ ↦ hi.elim (· (hσ i)) hw
  rw [speaker, Kernel.ofWeights_real_singleton_lt_iff w
      (fun h ↦ hσ0 (Finset.sum_eq_zero_iff.1 h σ (Finset.mem_univ _)))
      (ENNReal.sum_ne_top.2 fun _ _ ↦ weight_ne_top hα.le w _),
    ← ENNReal.toReal_lt_toReal (weight_ne_top hα.le w _) (weight_ne_top hα.le w _),
    weight_toReal hw hσ, weight_toReal hw hτ, Real.exp_lt_exp, mul_lt_mul_iff_of_pos_left hα]
  constructor <;> intro h <;> linarith

/-- A message true on all its parses loses to the null message, true everywhere and free, exactly
when one of its parses has prior probability above the cost weight: every parse must be
informative enough (§6). -/
theorem speaker_real_lt_null_iff [IsProbabilityMeasure μ] {ν : U} (hν : ∀ i, parse i ν = .univ)
    (hCν : C ν = 0) (hα : 0 < α) (hw : μ {w} ≠ 0) (hσ : ∀ i, w ∈ parse i σ) :
    (speaker μ α C parse w).real {σ} < (speaker μ α C parse w).real {ν} ↔
      Real.exp (-C σ) < (⨆ i, μ (parse i σ)).toReal := by
  rw [speaker_real_lt_iff hα hw hσ fun i ↦ by rw [hν]; trivial]
  simp only [hν, measure_univ, iSup_const, ENNReal.toReal_one, Real.log_one, hCν, neg_zero,
    sub_zero]
  rw [← Real.lt_log_iff_exp_lt (toReal_iSup_pos hw hσ)]
  constructor <;> intro h <;> linarith

/-! #### The readings of a trivalent meaning as the parses -/

variable {m : U → W → SignType}

/-- The speaker uses a message exactly where it is true. -/
theorem speaker_readings_ne_zero_iff (hα : 0 < α) (hw : μ {w} ≠ 0) :
    speaker μ α C (readings m) w {σ} ≠ 0 ↔ m σ w = 1 := by
  rw [speaker_apply_singleton_ne_zero_iff hα hw, forall_mem_readings_iff]

/-- The listener reads a message as true. -/
theorem listener_readings_ne_zero_iff (hα : 0 < α) :
    listener μ (speaker μ α C (readings m)) σ {w} ≠ 0 ↔ μ {w} ≠ 0 ∧ m σ w = 1 := by
  rw [listener_apply_singleton_ne_zero_iff_forall_mem hα, forall_mem_readings_iff]

omit [Fintype W] [DiscreteMeasurableSpace W] [Fintype U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [IsFiniteMeasure μ] in
theorem iSup_measure_readings (σ : U) : ⨆ d, μ (readings m d σ) = μ (readings m .lp σ) :=
  le_antisymm (iSup_le fun d ↦ by cases d; exacts [measure_mono readings_k3_subset_lp, le_rfl])
    (le_iSup (fun d ↦ μ (readings m d σ)) .lp)

/-- Among the messages true at a world, the speaker ranks by the surprisal of their LP reading less
the cost. -/
theorem speaker_readings_real_lt_iff (hα : 0 < α) (hw : μ {w} ≠ 0) (hσ : m σ w = 1)
    (hτ : m τ w = 1) :
    (speaker μ α C (readings m) w).real {σ} < (speaker μ α C (readings m) w).real {τ} ↔
      -Real.log (μ.real (readings m .lp σ)) - C σ <
        -Real.log (μ.real (readings m .lp τ)) - C τ := by
  rw [speaker_real_lt_iff hα hw (forall_mem_readings_iff.2 hσ) (forall_mem_readings_iff.2 hτ),
    iSup_measure_readings, iSup_measure_readings, ← measureReal_def, ← measureReal_def]

end Speaker

private theorem neg_log_sub_lt_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -Real.log b - c < -Real.log a - d ↔ a * Real.exp (d - c) < b := by
  rw [← Real.log_lt_log_iff (mul_pos ha (Real.exp_pos _)) hb,
    Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp]
  constructor <;> intro h <;> linarith

/-! ### The model of §6 -/

section Model

open Spector2017 (World)

/-- The messages: *some*, *all*, *some but not all*, *not all*, *no* and silence. -/
inductive Message
  | some | all | someButNotAll | notAll | no | null
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Message := ⊤
instance : DiscreteMeasurableSpace Message := ⟨fun _ ↦ trivial⟩

/-- The literal meanings. -/
def literal : Message → Set World
  | .some => {w | w ≠ .none}
  | .all => {.all}
  | .someButNotAll => {.justSome}
  | .notAll => {w | w ≠ .all}
  | .no => {.none}
  | .null => .univ

/-- *Some* is exhaustified against *all* and *not all* against *no*. -/
def alternatives : Message → Set (Set World)
  | .some => {literal .some, literal .all}
  | .notAll => {literal .notAll, literal .no}
  | σ => {literal σ}

/-- The `pex` meaning of a message. -/
noncomputable def meaning (σ : Message) : World → SignType :=
  pexIE (alternatives σ) (literal σ) (alternatives σ)

theorem readings_lp_meaning (σ : Message) : readings meaning .lp σ = literal σ :=
  readings_pexIE_lp

private theorem exhIE_singleton {σ : Message} (h : alternatives σ = {literal σ}) :
    exhIE (alternatives σ) (literal σ) = literal σ := by
  rw [h]
  exact exhIE_eq_self_of_forall _ _ fun a ha _ ↦ (Set.mem_singleton_iff.1 ha).ge

theorem meaning_eq_one_iff {σ : Message} {w : World} :
    meaning σ w = 1 ↔ w ∈ exhIE (alternatives σ) (literal σ) :=
  pexIE_eq_one_iff_mem_exhIE subset_rfl

theorem meaning_some_eq_one_iff {w : World} : meaning .some w = 1 ↔ w = .justSome := by
  rw [meaning_eq_one_iff]
  change w ∈ exhIE {literal .some, literal .all} (literal .some) ↔ _
  rw [exhIE_pair_sdiff (φ := literal .some) (d := literal .all) ⟨.justSome, by simp [literal]⟩]
  cases w <;> simp [literal]

theorem meaning_notAll_eq_one_iff {w : World} : meaning .notAll w = 1 ↔ w = .justSome := by
  rw [meaning_eq_one_iff]
  change w ∈ exhIE {literal .notAll, literal .no} (literal .notAll) ↔ _
  rw [exhIE_pair_sdiff (φ := literal .notAll) (d := literal .no) ⟨.justSome, by simp [literal]⟩]
  cases w <;> simp [literal]

theorem meaning_someButNotAll_eq_one_iff {w : World} :
    meaning .someButNotAll w = 1 ↔ w = .justSome := by
  rw [meaning_eq_one_iff, exhIE_singleton rfl]
  simp [literal]

theorem readings_null (d : Trivalent.Designation) : readings meaning d .null = .univ :=
  Set.eq_univ_of_forall fun w ↦ (forall_mem_readings_iff.2
    (meaning_eq_one_iff.2 (by rw [exhIE_singleton rfl]; trivial))) d

/-- Three students: two solved every problem, one some but not all. -/
def solved : Fin 3 → World := ![.all, .all, .justSome]

/-- *Exactly two students solved some of the problems*, *some* read by `pex`, is false on both
parses (one student solved some but not all, three solved some), so false by Truth on all parses,
and undefined entity-wise: reading *some* with the operator for one of the two who solved every
problem leaves exactly two. -/
theorem exactlyTwo_parses_false_entitywise_undefined (g : Assignment (Fin 3)) {X : SetM Prop}
    (hX : PhraseStructure.Tree.interp (lexicon (fun P ↦ {x | P x}.ncard = 2)
      fun x ↦ meaning .some (solved x)) g raised = some ⟨.t, X⟩) :
    SignType.supervaluationOn (parses (lexicon (fun P ↦ {x | P x}.ncard = 2)
      fun x ↦ meaning .some (solved x)) g raised) id = -1 ∧
      SignType.supervaluationOn X.run id = 0 := by
  obtain rfl := sigma_mk_injective (Option.some_injective _ (hX.symm.trans (interp_raised _ _ g)))
  dsimp only [SetM.run]
  rw [parses_raised]
  have hk3 (x : Fin 3) : 1 ≤ meaning .some (solved x) ↔ x = 2 := by
    rw [show ∀ a : SignType, 1 ≤ a ↔ a = 1 by decide, meaning_some_eq_one_iff]
    fin_cases x <;> simp [solved]
  have hlp (x : Fin 3) : 0 ≤ meaning .some (solved x) := by
    rw [show ∀ a : SignType, 0 ≤ a ↔ a ≠ -1 by decide, Ne, meaning, pexIE_eq_neg_one_iff]
    fin_cases x <;> simp [solved, literal]
  refine ⟨SignType.supervaluationOn_eq_neg_one_iff.2 ⟨Set.range_nonempty _, ?_⟩,
    SignType.supervaluationOn_eq_zero_iff.2 ⟨⟨_, ⟨![.lp, .k3, .k3], rfl⟩, ?_⟩,
      ⟨_, ⟨fun _ ↦ .k3, rfl⟩, ?_⟩⟩⟩
  · rintro _ ⟨d, rfl⟩
    cases d <;> simp [hk3, hlp]
  · show Set.ncard _ = 2
    rw [show {x : Fin 3 | _} = {0, 2} by ext x; fin_cases x <;> simp [hk3, hlp]]
    exact Set.ncard_pair (by decide)
  · simp [hk3]

/-- Negation does not see the exhaustivity operator: *it is not the case that some* is true by
Strong Kleene exactly where none, (22). -/
theorem not_some_eq_one_iff (w : World) :
    Trivalent.Formula.eval .strongKleene (meaning · w) (.neg (.atom .some)) = 1 ↔ w = .none := by
  simp [meaning, pexIE_eq_neg_one_iff, literal]

variable {μ : Measure World} [IsFiniteMeasure μ] {α : ℝ} {C : Message → ℝ}

private theorem measureReal_literal_pos {σ : Message} (h : World.justSome ∈ literal σ)
    (hsome : μ {.justSome} ≠ 0) : 0 < μ.real (literal σ) :=
  ENNReal.toReal_pos (fun h0 ↦ hsome (measure_mono_null (Set.singleton_subset_iff.2 h) h0))
    (measure_ne_top _ _)

/-- A speaker who knows that some but not all of the marbles sank prefers *some but not all* to
*some*, and to *not all*, exactly when its prior mass, weighted by its extra cost, is below that of
the literal meaning of the other: in the marbles context some but not all is improbable next to
both none and all, so she says *some but not all* (§6), while *some*, read by `pex`, is informative
after accommodation, false where no marble sank (§2). -/
theorem judgments_11 (hα : 0 < α) (hsome : μ {.justSome} ≠ 0) (hnone : μ {.none} ≠ 0) :
    Examples.ex_11a.judgment = .unacceptable ∧ Examples.ex_11b.judgment = .acceptable ∧
      ((speaker μ α C (readings meaning) .justSome).real {.some} <
          (speaker μ α C (readings meaning) .justSome).real {.someButNotAll} ↔
        μ.real {.justSome} * Real.exp (C .someButNotAll - C .some) < μ.real (literal .some)) ∧
      ((speaker μ α C (readings meaning) .justSome).real {.notAll} <
          (speaker μ α C (readings meaning) .justSome).real {.someButNotAll} ↔
        μ.real {.justSome} * Real.exp (C .someButNotAll - C .notAll) <
          μ.real (literal .notAll)) ∧
      PostAccommodationInformative {w | μ {w} ≠ 0} (meaning .some) := by
  have hjs : 0 < μ.real {World.justSome} := ENNReal.toReal_pos hsome (measure_ne_top _ _)
  refine ⟨rfl, rfl, ?_, ?_, postAccommodationInformative_iff.2
    ⟨.none, hnone, pexIE_eq_neg_one_iff.2 (by simp [literal])⟩⟩
  · rw [speaker_readings_real_lt_iff hα hsome (meaning_some_eq_one_iff.2 rfl)
      (meaning_someButNotAll_eq_one_iff.2 rfl), readings_lp_meaning, readings_lp_meaning]
    exact neg_log_sub_lt_iff hjs (measureReal_literal_pos (by simp [literal]) hsome)
  · rw [speaker_readings_real_lt_iff hα hsome (meaning_notAll_eq_one_iff.2 rfl)
      (meaning_someButNotAll_eq_one_iff.2 rfl), readings_lp_meaning, readings_lp_meaning]
    exact neg_log_sub_lt_iff hjs (measureReal_literal_pos (by simp [literal]) hsome)

/-- Where the common ground makes *some* nearly certain, *some* loses to silence once the
probability that some marble sank exceeds its cost weight, and where the common ground entails
*some*, its `pex` reading is not informative after accommodation, the prediction of Wehbe and Doron
([wehbe-doron-2025]): both accounts reject (14a) (§1.2, §3). -/
theorem judgments_14 [IsProbabilityMeasure μ] (hα : 0 < α) (hsome : μ {.justSome} ≠ 0)
    (hCnull : C .null = 0) :
    Examples.ex_14a.judgment = .unacceptable ∧
      ((speaker μ α C (readings meaning) .justSome).real {.some} <
          (speaker μ α C (readings meaning) .justSome).real {.null} ↔
        Real.exp (-C .some) < 1 - μ.real {.none}) ∧
      (μ {.none} = 0 → ¬ PostAccommodationInformative {w | μ {w} ≠ 0} (meaning .some)) := by
  refine ⟨rfl, ?_, fun hnone h ↦ ?_⟩
  · have hlit : literal .some = {World.none}ᶜ := by
      ext w; cases w <;> simp [literal]
    rw [speaker_real_lt_null_iff readings_null hCnull hα hsome
      (forall_mem_readings_iff.2 (meaning_some_eq_one_iff.2 rfl)), iSup_measure_readings,
      readings_lp_meaning, hlit, ← measureReal_def,
      probReal_compl_eq_one_sub (measurableSet_singleton _)]
  · obtain ⟨w, hw, hf⟩ := postAccommodationInformative_iff.1 h
    cases w <;> simp_all [meaning, pexIE_eq_neg_one_iff, literal]

/-- (15) extends the contrast of (14) between *some* and *not all* to a context where *some* is not
wholly uninformative: a speaker who knows that not all talks were in English prefers *not all*
exactly when its literal meaning, weighted by its extra cost, is less probable than that of
*some*. -/
theorem judgments_15 (hα : 0 < α) (hsome : μ {.justSome} ≠ 0) :
    Examples.ex_15a.judgment = .unacceptable ∧ Examples.ex_15c.judgment = .acceptable ∧
      ((speaker μ α C (readings meaning) .justSome).real {.some} <
          (speaker μ α C (readings meaning) .justSome).real {.notAll} ↔
        μ.real (literal .notAll) * Real.exp (C .notAll - C .some) < μ.real (literal .some)) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [speaker_readings_real_lt_iff hα hsome (meaning_some_eq_one_iff.2 rfl)
    (meaning_notAll_eq_one_iff.2 rfl), readings_lp_meaning, readings_lp_meaning]
  exact neg_log_sub_lt_iff (measureReal_literal_pos (by simp [literal]) hsome)
    (measureReal_literal_pos (by simp [literal]) hsome)

end Model

/-! ### Two marbles, (19)

The model of Cremers, Wilcox and Spector: *the blue marble sank* (*A*), *the blue and the red
marbles sank* (*A and B*) and *only the blue marble sank* (*A and not B*), with *A* exhaustified
against *A and B*. -/

namespace TwoMarbles

open CremersWilcoxSpector2023 (World truth Setting)

/-- The literal meanings. -/
def literal (u : CremersWilcoxSpector2023.Message) : Set World := {w | truth u w = true}

/-- The alternatives of Cremers, Wilcox and Spector, as sets of worlds: *A* has the scale-mate
*A and B*. -/
def alternatives (u : CremersWilcoxSpector2023.Message) : Set (Set World) :=
  (fun f ↦ {w | f w = true}) '' {f | f ∈ CremersWilcoxSpector2023.alternatives u}

/-- The `pex` meaning of a message. -/
noncomputable def meaning (u : CremersWilcoxSpector2023.Message) : World → SignType :=
  pexIE (alternatives u) (literal u) (alternatives u)

theorem readings_lp_meaning (u : CremersWilcoxSpector2023.Message) :
    readings meaning .lp u = literal u :=
  readings_pexIE_lp

theorem alternatives_a : alternatives .a = {literal .a, literal .aAndB} := by
  rw [alternatives, show {f | f ∈ CremersWilcoxSpector2023.alternatives .a} =
    {truth .a, truth .aAndB} by ext; simp [CremersWilcoxSpector2023.alternatives],
    Set.image_insert_eq, Set.image_singleton]
  rfl

theorem alternatives_aAndNotB : alternatives .aAndNotB = {literal .aAndNotB} := by
  rw [alternatives, show {f | f ∈ CremersWilcoxSpector2023.alternatives .aAndNotB} =
    {truth .aAndNotB} by ext; simp [CremersWilcoxSpector2023.alternatives], Set.image_singleton]
  rfl

theorem meaning_a_eq_one_iff {w : World} : meaning .a w = 1 ↔ w = .wa := by
  rw [meaning, pexIE_eq_one_iff_mem_exhIE subset_rfl, alternatives_a,
    exhIE_pair_sdiff (φ := literal .a) (d := literal .aAndB) ⟨.wa, by simp [literal, truth]⟩]
  cases w <;> simp [literal, truth]

theorem meaning_aAndNotB_eq_one_iff {w : World} : meaning .aAndNotB w = 1 ↔ w = .wa := by
  rw [meaning, pexIE_eq_one_iff_mem_exhIE subset_rfl, alternatives_aAndNotB,
    exhIE_eq_self_of_forall _ _ fun a ha _ ↦ (Set.mem_singleton_iff.1 ha).ge]
  cases w <;> simp [literal, truth]

/-- Spector does not work (19) out in §6; this is his model on the messages of Cremers, Wilcox and
Spector. *The blue marble sank* (19b) never conveys that both marbles sank: false there, it is not
used there, so the listener gives that world no mass after it at any prior, rationality and costs,
where the baseline listener raises it for a prior biased enough
(`CremersWilcoxSpector2023.prior_lt_listener_iff`). Where only the blue marble sank, the speaker
prefers *only the blue marble sank* exactly when the baseline speaker does. -/
theorem judgments_19 (s : Setting) :
    Examples.ex_19b.judgment = .unacceptable ∧
      listener s.prior (speaker s.prior s.lam s.cost (readings meaning)) .a {.wab} = 0 ∧
      ((speaker s.prior s.lam s.cost (readings meaning) .wa).real {.a} <
          (speaker s.prior s.lam s.cost (readings meaning) .wa).real {.aAndNotB} ↔
        (s.speaker CremersWilcoxSpector2023.literal .wa).real {.a} <
          (s.speaker CremersWilcoxSpector2023.literal .wa).real {.aAndNotB}) := by
  refine ⟨rfl, listener_apply_singleton_eq_zero (speaker_apply_singleton_eq_zero s.lam_pos
    (i := .k3) fun h ↦ absurd (meaning_a_eq_one_iff.1 ((show (1 : SignType) ≤ _ ↔ _ by
      cases meaning .a .wab <;> decide).1 h)) (by decide)), ?_⟩
  have hlit : literal .a = .univ := by ext w; cases w <;> simp [literal, truth]
  have hwa : literal .aAndNotB = {.wa} := by ext w; cases w <;> simp [literal, truth]
  rw [speaker_readings_real_lt_iff s.lam_pos (s.prior_ne_zero .wa)
      (meaning_a_eq_one_iff.2 rfl) (meaning_aAndNotB_eq_one_iff.2 rfl),
    readings_lp_meaning, readings_lp_meaning, CremersWilcoxSpector2023.baseline_a_lt_aAndNotB_iff,
    hlit, hwa, measureReal_def, measure_univ, ENNReal.toReal_one, Setting.prior_real_wa,
    Real.log_one]
  change -0 - 0 < -Real.log (1 - s.p) - s.cAndNotB ↔ _
  constructor <;> intro h <;> linarith

end TwoMarbles

end Spector2025
