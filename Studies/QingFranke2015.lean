module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Data.Statistics.QingFranke2015
public import Linglib.Pragmatics.RSA.Decision
public import Studies.FrankGoodman2012
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Qing and Franke (2015): Variations on a Bayesian Theme

Qing and Franke decompose the rational speech act model of Frank and Goodman's referential game
along its design choices. The literal listener conditions a prior on the extension of the word,
and the prior is uniform or the measured salience of the objects. The speaker's goal is
belief-oriented, the log of the literal listener's probability of the referent, or action-oriented,
that probability itself, and colour adjectives carry a cost. The listener inverts a speaker against
its own prior and may act on the result by a further soft maximization. The context has a square
and a circle of one colour and a circle of the other, and the paper compares the models on the
choices of speakers and listeners by their Bayes factors.

## Implementation notes

* The lexicon and the model of a context are those of `FrankGoodman2012`, and the belief-oriented
  speaker is `RSA.speaker` against the literal listener. The action-oriented speaker is the
  softmax of its utility over the true words, the restriction the paper applies in its model
  comparison.
* The salience prior weights each object by its count in the salience condition, without
  normalizing.
* The action-oriented listener is `RSA.policy` for the game that rewards choosing the referent. It
  is not restricted to the objects the word is true of, which does not change their order.
* The Bayesian model comparison is not formalized. The findings are the directions of preference
  each model predicts, as conditions on its parameters.

## References

* [qing-franke-2015]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Real
open scoped Denotes
open FrankGoodman2012 (Attribute Colour Shape Word)
open scoped ENNReal Denotes.Superscript

namespace QingFranke2015

/-! ### The context, the cost and the salience prior -/

instance : MeasurableSpace Object := ⊤
instance : DiscreteMeasurableSpace Object := ⟨fun _ ↦ trivial⟩
instance : Nonempty Object := ⟨.greenSquare⟩

/-- The model `M` of the sample context gives each object its colour and its shape. -/
def M : Object → (a : Attribute) → a.Value Colour Shape
  | .greenSquare, .colour => Colour.green
  | .greenSquare, .shape => Shape.square
  | .greenCircle, .colour => Colour.green
  | .greenCircle, .shape => Shape.circle
  | .blueCircle, .colour => Colour.blue
  | .blueCircle, .shape => Shape.circle

/-- The colour adjectives cost `c` and the shape nouns nothing (11). -/
def cost (c : ℝ) : Word Colour Shape → ℝ
  | ⟨.colour, _⟩ => c
  | ⟨.shape, _⟩ => 0

theorem cost_zero : cost 0 = 0 := funext fun ⟨a, _⟩ ↦ by cases a <;> rfl

/-- The salience prior `S` weights each object by the number of listeners who chose it when they
could not understand the speaker. -/
noncomputable def salience : Measure Object :=
  Measure.ofWeights fun t ↦ ((listenerChoice .salience t).count : ℝ≥0∞)

instance : IsFiniteMeasure salience :=
  Measure.isFiniteMeasure_ofWeights fun _ ↦ ENNReal.natCast_ne_top _

theorem salience_real_singleton (t : Object) :
    salience.real {t} = (listenerChoice .salience t).count := by
  rw [salience, Measure.ofWeights_real_singleton, ENNReal.toReal_natCast]

theorem salience_real_finset (s : Finset Object) :
    salience.real ↑s = ∑ t ∈ s, ((listenerChoice .salience t).count : ℝ) := by
  rw [measureReal_def, salience, Measure.ofWeights_apply_finset,
    ENNReal.toReal_sum fun _ _ ↦ ENNReal.natCast_ne_top _]
  simp only [ENNReal.toReal_natCast]

theorem salience_apply_singleton_ne_zero (t : Object) : salience {t} ≠ 0 := by
  rw [salience, Measure.ofWeights_apply_singleton]
  cases t <;> simp [listenerChoice]

/-! ### The literal listener and the speakers -/

/-- The literal listener at a prior (1) conditions the prior on the extension of the word. -/
noncomputable def literal (μ : Measure Object) : Kernel (Word Colour Shape) Object :=
  listener μ (truthful fun u : Word Colour Shape ↦ (↑⟦u⟧ᴹ : Set Object))

instance (μ : Measure Object) : IsFiniteKernel (literal μ) :=
  inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The speaker's goal is belief-oriented or action-oriented. -/
inductive Goal
  | belief | action
  deriving DecidableEq, Repr

/-- The goal's measure of the literal listener's probability of the referent, its logarithm (10)
or the probability itself (9). -/
noncomputable def Goal.value : Goal → ℝ → ℝ
  | .belief => log
  | .action => id

variable {g : Goal} {μ : Measure Object} {lam c : ℝ} {t : Object} {u u' : Word Colour Shape}

/-- The utility of a word for a referent (4) is the goal's measure of the literal listener's
probability of the referent, less the cost of the word. -/
noncomputable def utility (g : Goal) (μ : Measure Object) (c : ℝ) (t : Object)
    (u : Word Colour Shape) : ℝ :=
  g.value ((literal μ u).real {t}) - cost c u

/-- The speaker models `σ_xy` with goal `x`, belief `y` about the literal listener's prior,
rationality `lam` and adjective cost `c`. The belief-oriented speaker is the rational speech act
speaker against the literal listener, and the action-oriented speaker soft-maximizes its utility
over the true words. -/
noncomputable def speaker : Goal → Measure Object → ℝ → ℝ → Kernel Object (Word Colour Shape)
  | .belief, μ, lam, c => RSA.speaker lam (cost c) (literal μ) Measure.dirac
  | .action, μ, lam, c => Kernel.softmax fun t u ↦
      if t ∈ ⟦u⟧ᴹ then ((lam * utility .action μ c t u : ℝ) : EReal) else ⊥

instance (g : Goal) (μ : Measure Object) (lam c : ℝ) : IsFiniteKernel (speaker g μ lam c) := by
  cases g
  · exact inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))
  · exact inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

theorem literal_uniform : literal (uniformOn .univ) = FrankGoodman2012.literal M :=
  rfl

/-- At the uniform prior and no cost the belief-oriented speaker is Frank and Goodman's. -/
theorem speaker_belief_uniform (lam : ℝ) :
    speaker .belief (uniformOn .univ) lam 0 = FrankGoodman2012.speaker M lam := by
  rw [speaker, cost_zero]
  rfl

section Preference

variable [IsFiniteMeasure μ]

/-- Every speaker of the family soft-maximizes its utility over the true words, (9) and (10). -/
theorem speaker_eq_softmax (hlam : 0 < lam) (hμ : ∀ t, μ {t} ≠ 0) (g : Goal) :
    speaker g μ lam c = Kernel.softmax fun t u ↦
      if t ∈ ⟦u⟧ᴹ then ((lam * utility g μ c t u : ℝ) : EReal) else ⊥ := by
  cases g
  swap
  · rfl
  rw [speaker, speaker_dirac_eq_softmax]
  refine congrArg Kernel.softmax (funext fun t ↦ funext fun u ↦ ?_)
  split_ifs with h
  · have h0 : literal μ u {t} ≠ 0 :=
      (listener_truthful_apply_singleton_ne_zero_iff μ _ u t).2 ⟨Finset.mem_coe.2 h, hμ t⟩
    rw [ENNReal.log_pos_real h0 (measure_ne_top _ _), utility, Goal.value, measureReal_def,
      mul_sub, EReal.coe_sub, EReal.coe_mul, EReal.coe_mul]
  · rw [literal, listener_truthful_apply_singleton_of_notMem μ _ (by simpa using h),
      ENNReal.log_zero, EReal.coe_mul_bot_of_pos hlam, EReal.bot_sub]

theorem speaker_lt_iff (hlam : 0 < lam) (hμ : ∀ t, μ {t} ≠ 0) (g : Goal) (hu : t ∈ ⟦u⟧ᴹ)
    (hu' : t ∈ ⟦u'⟧ᴹ) :
    (speaker g μ lam c t).real {u} < (speaker g μ lam c t).real {u'} ↔
      utility g μ c t u < utility g μ c t u' := by
  rw [speaker_eq_softmax hlam hμ, Kernel.softmax_real_singleton_lt_iff
    (fun v ↦ by split_ifs; exacts [EReal.coe_ne_top _, bot_ne_top])
    ⟨u, by rw [ite_eq_left hu]; exact EReal.coe_ne_bot _⟩, ite_eq_left hu, ite_eq_left hu',
    EReal.coe_lt_coe_iff, mul_lt_mul_iff_right₀ hlam]

theorem speaker_real_singleton (hlam : 0 < lam) (hμ : ∀ t, μ {t} ≠ 0) (g : Goal) (hu : t ∈ ⟦u⟧ᴹ)
    (hu' : t ∈ ⟦u'⟧ᴹ) (h : u.1 ≠ u'.1) :
    (speaker g μ lam c t).real {u} =
      sigmoid (lam * (utility g μ c t u - utility g μ c t u')) := by
  rw [speaker_eq_softmax hlam hμ, Kernel.softmax_real_singleton_of_pair
    (fun huu' ↦ h (congrArg Sigma.fst huu')) (by rw [ite_eq_left hu]; exact EReal.coe_ne_bot _)
    (by rw [ite_eq_left hu']; exact EReal.coe_ne_bot _)
    (fun v ↦ by split_ifs; exacts [EReal.coe_ne_top _, bot_ne_top]) fun v hv ↦ ?_,
    ite_eq_left hu, ite_eq_left hu', EReal.toReal_coe, EReal.toReal_coe, mul_sub]
  have hv' : t ∈ ⟦v⟧ᴹ := by by_contra hn; exact hv (ite_eq_right hn)
  obtain ⟨a, x⟩ := u
  obtain ⟨a', x'⟩ := u'
  obtain ⟨b, y⟩ := v
  rw [FrankGoodman2012.mem_denote] at hu hu' hv'
  simp only at hu hu' hv' h
  subst hu hu' hv'
  cases a <;> cases a' <;> cases b <;> simp_all

end Preference

/-! ### Speakers who ignore salience

At the uniform prior a word is worth the goal's measure of the reciprocal of its extension's size.
Every word of the context is true of one object or of two, and the difference in their worth is
`log 2` to the belief-oriented speaker and `1/2` to the action-oriented one. -/

theorem literal_uniform_real (h : t ∈ ⟦u⟧ᴹ) :
    (literal (uniformOn .univ) u).real {t} = (⟦u⟧ᴹ.card : ℝ)⁻¹ := by
  rw [literal_uniform, FrankGoodman2012.literal, listener_uniformOn_truthful_real_singleton,
    ite_eq_left h]

/-- The informativity gap between a word true of the referent alone and a word true of two
objects, on the goal's measure. -/
noncomputable def Goal.gap (g : Goal) : ℝ :=
  g.value 1 - g.value 2⁻¹

@[simp] theorem Goal.gap_belief : Goal.belief.gap = log 2 := by
  simp [Goal.gap, Goal.value]

@[simp] theorem Goal.gap_action : Goal.action.gap = 2⁻¹ := by
  norm_num [Goal.gap, Goal.value]

theorem Goal.gap_pos (g : Goal) : 0 < g.gap := by
  cases g <;> simp [log_pos]

theorem Goal.support_lt_gap (g : Goal) : 0.4 < g.gap := by
  cases g
  · linarith [gap_belief, log_two_gt_d9]
  · norm_num

private theorem utility_uniform (g : Goal) (c : ℝ) {n : ℕ} (h : t ∈ ⟦u⟧ᴹ) (hn : ⟦u⟧ᴹ.card = n) :
    utility g (uniformOn .univ) c t u = g.value (n : ℝ)⁻¹ - cost c u := by
  rw [utility, literal_uniform_real h, hn]

/-- At the blue circle the speaker prefers *blue*, which only it satisfies, to *circle* exactly
when the adjective costs less than the informativity gap. -/
theorem prefers_unique_colour_iff (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .blueCircle).real {.circle} <
      (speaker g (uniformOn .univ) lam c .blueCircle).real {.blue} ↔ c < g.gap := by
  rw [speaker_lt_iff hlam uniformOn_univ_singleton_ne_zero g (by decide) (by decide),
    utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 1) (by decide) (by decide), Goal.gap]
  simp only [cost, Nat.cast_one, Nat.cast_ofNat, inv_one]
  constructor <;> intro h <;> linarith

theorem prefers_unique_shape_iff (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .greenSquare).real {.green} <
      (speaker g (uniformOn .univ) lam c .greenSquare).real {.square} ↔ -g.gap < c := by
  rw [speaker_lt_iff hlam uniformOn_univ_singleton_ne_zero g (by decide) (by decide),
    utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 1) (by decide) (by decide), Goal.gap]
  simp only [cost, Nat.cast_one, Nat.cast_ofNat, inv_one]
  constructor <;> intro h <;> linarith

/-- At the green circle, whose colour and shape are each shared, the two words are equally
informative and the speaker prefers the noun exactly when it is the cheaper. -/
theorem prefers_noun_iff (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .greenCircle).real {.green} <
      (speaker g (uniformOn .univ) lam c .greenCircle).real {.circle} ↔ 0 < c := by
  rw [speaker_lt_iff hlam uniformOn_univ_singleton_ne_zero g (by decide) (by decide),
    utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 2) (by decide) (by decide)]
  simp only [cost]
  constructor <;> intro h <;> linarith

/-! ### The belief-oriented speaker who heeds salience -/

theorem literal_salience_real (h : t ∈ ⟦u⟧ᴹ) :
    (literal salience u).real {t} = (listenerChoice .salience t).count /
      ∑ t' ∈ ⟦u⟧ᴹ, ((listenerChoice .salience t').count : ℝ) := by
  rw [literal, listener_truthful_real_singleton salience
    (fun u : Word Colour Shape ↦ (↑⟦u⟧ᴹ : Set Object)) (Finset.mem_coe.2 h),
    salience_real_singleton, salience_real_finset]

private theorem literal_salience_blue : (literal salience .blue).real {.blueCircle} = 1 := by
  rw [literal_salience_real (by decide), show ⟦Word.blue⟧ᴹ = {.blueCircle} by decide,
    Finset.sum_singleton]
  norm_num [listenerChoice]

private theorem literal_salience_circle_blueCircle :
    (literal salience .circle).real {.blueCircle} = 139 / 169 := by
  rw [literal_salience_real (by decide),
    show ⟦Word.circle⟧ᴹ = {.greenCircle, .blueCircle} by decide, Finset.sum_pair (by decide)]
  norm_num [listenerChoice]

private theorem literal_salience_circle_greenCircle :
    (literal salience .circle).real {.greenCircle} = 30 / 169 := by
  rw [literal_salience_real (by decide),
    show ⟦Word.circle⟧ᴹ = {.greenCircle, .blueCircle} by decide, Finset.sum_pair (by decide)]
  norm_num [listenerChoice]

private theorem literal_salience_green :
    (literal salience .green).real {.greenCircle} = 30 / 101 := by
  rw [literal_salience_real (by decide),
    show ⟦Word.green⟧ᴹ = {.greenSquare, .greenCircle} by decide, Finset.sum_pair (by decide)]
  norm_num [listenerChoice]

-- (7)
theorem salience_prefers_unique_colour_iff (hlam : 0 < lam) :
    (speaker .belief salience lam c .blueCircle).real {.circle} <
      (speaker .belief salience lam c .blueCircle).real {.blue} ↔ c < log (169 / 139) := by
  rw [speaker_lt_iff hlam salience_apply_singleton_ne_zero .belief (by decide) (by decide),
    utility, utility, literal_salience_circle_blueCircle, literal_salience_blue,
    log_div (by norm_num) (by norm_num)]
  simp only [Goal.value, cost, log_one, log_div (by norm_num : (139 : ℝ) ≠ 0)
    (by norm_num : (169 : ℝ) ≠ 0)]
  constructor <;> intro h <;> linarith

theorem salience_prefers_adjective_iff (hlam : 0 < lam) :
    (speaker .belief salience lam c .greenCircle).real {.circle} <
      (speaker .belief salience lam c .greenCircle).real {.green} ↔ c < log (169 / 101) := by
  rw [speaker_lt_iff hlam salience_apply_singleton_ne_zero .belief (by decide) (by decide),
    utility, utility, literal_salience_circle_greenCircle, literal_salience_green,
    log_div (by norm_num) (by norm_num)]
  simp only [Goal.value, cost, log_div (by norm_num : (30 : ℝ) ≠ 0) (by norm_num : (169 : ℝ) ≠ 0),
    log_div (by norm_num : (30 : ℝ) ≠ 0) (by norm_num : (101 : ℝ) ≠ 0)]
  constructor <;> intro h <;> linarith

theorem salience_thresholds : log (169 / 139) < 0.4 ∧ (0.4 : ℝ) < log (169 / 101) := by
  refine ⟨?_, ?_⟩
  · rw [log_lt_iff_lt_exp (by norm_num)]
    linarith [add_one_lt_exp (by norm_num : (0.4 : ℝ) ≠ 0)]
  · rw [lt_log_iff_exp_lt (by norm_num)]
    exact (exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans_lt (by norm_num)

/-! ### Listeners

The belief-oriented listener (15) is `RSA.listener` at its prior and a speaker, and the paper's
listeners take the speaker to ignore salience. The action-oriented listener (14) soft-maximizes
that belief. -/

private theorem circle_blueCircle (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .blueCircle).real {.circle} =
      sigmoid (lam * (c - g.gap)) := by
  rw [speaker_real_singleton hlam uniformOn_univ_singleton_ne_zero g (u' := .blue) (by decide)
      (by decide) (by decide), utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 1) (by decide) (by decide), Goal.gap]
  simp only [cost, Nat.cast_one, Nat.cast_ofNat, inv_one]
  ring_nf

private theorem circle_greenCircle (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .greenCircle).real {.circle} = sigmoid (lam * c) := by
  rw [speaker_real_singleton hlam uniformOn_univ_singleton_ne_zero g (u' := .green) (by decide)
      (by decide) (by decide), utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 2) (by decide) (by decide)]
  simp only [cost]
  ring_nf

private theorem green_greenSquare (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .greenSquare).real {.green} =
      sigmoid (-(lam * (c + g.gap))) := by
  rw [speaker_real_singleton hlam uniformOn_univ_singleton_ne_zero g (u' := .square) (by decide)
      (by decide) (by decide), utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 1) (by decide) (by decide), Goal.gap]
  simp only [cost, Nat.cast_one, Nat.cast_ofNat, inv_one]
  ring_nf

private theorem green_greenCircle (hlam : 0 < lam) (g : Goal) :
    (speaker g (uniformOn .univ) lam c .greenCircle).real {.green} = sigmoid (-(lam * c)) := by
  rw [speaker_real_singleton hlam uniformOn_univ_singleton_ne_zero g (u' := .circle) (by decide)
      (by decide) (by decide), utility_uniform g c (n := 2) (by decide) (by decide),
    utility_uniform g c (n := 2) (by decide) (by decide)]
  simp only [cost]
  ring_nf

/-- A listener with a uniform prior who hears *circle* prefers the green circle, since for the
blue circle the speaker had *blue*. -/
theorem uniform_listener_narrows_circle (hlam : 0 < lam) (g : Goal) :
    (listener (uniformOn .univ) (speaker g (uniformOn .univ) lam c) .circle).real {.blueCircle} <
      (listener (uniformOn .univ) (speaker g (uniformOn .univ) lam c) .circle).real
        {.greenCircle} := by
  rw [listener_real_singleton_lt_iff, uniformOn_univ_real_singleton, circle_blueCircle hlam,
    uniformOn_univ_real_singleton, circle_greenCircle hlam]
  exact mul_lt_mul_of_pos_left (sigmoid_lt (by nlinarith [g.gap_pos])) (by positivity)

theorem uniform_listener_narrows_green (hlam : 0 < lam) (g : Goal) :
    (listener (uniformOn .univ) (speaker g (uniformOn .univ) lam c) .green).real {.greenSquare} <
      (listener (uniformOn .univ) (speaker g (uniformOn .univ) lam c) .green).real
        {.greenCircle} := by
  rw [listener_real_singleton_lt_iff, uniformOn_univ_real_singleton, green_greenSquare hlam,
    uniformOn_univ_real_singleton, green_greenCircle hlam]
  exact mul_lt_mul_of_pos_left (sigmoid_lt (by nlinarith [g.gap_pos])) (by positivity)

theorem salience_listener_circle_iff (hlam : 0 < lam) (g : Goal) :
    (listener salience (speaker g (uniformOn .univ) lam c) .circle).real {.greenCircle} <
      (listener salience (speaker g (uniformOn .univ) lam c) .circle).real {.blueCircle} ↔
      30 * sigmoid (lam * c) < 139 * sigmoid (lam * (c - g.gap)) := by
  rw [listener_real_singleton_lt_iff, salience_real_singleton, circle_greenCircle hlam,
    salience_real_singleton, circle_blueCircle hlam]
  simp only [listenerChoice, Nat.cast_ofNat]

theorem salience_listener_green_iff (hlam : 0 < lam) (g : Goal) :
    (listener salience (speaker g (uniformOn .univ) lam c) .green).real {.greenSquare} <
      (listener salience (speaker g (uniformOn .univ) lam c) .green).real {.greenCircle} ↔
      71 * sigmoid (-(lam * (c + g.gap))) < 30 * sigmoid (-(lam * c)) := by
  rw [listener_real_singleton_lt_iff, salience_real_singleton, green_greenSquare hlam,
    salience_real_singleton, green_greenCircle hlam]
  simp only [listenerChoice, Nat.cast_ofNat]

/-- Without cost a listener with the salience prior follows salience on *circle* and narrows on
*green*, as the paper's listeners did, exactly on a window of rationalities of the speaker. -/
theorem salience_listener_window (hlam : 0 < lam) (g : Goal) :
    ((listener salience (speaker g (uniformOn .univ) lam 0) .circle).real {.greenCircle} <
        (listener salience (speaker g (uniformOn .univ) lam 0) .circle).real {.blueCircle} ∧
      (listener salience (speaker g (uniformOn .univ) lam 0) .green).real {.greenSquare} <
        (listener salience (speaker g (uniformOn .univ) lam 0) .green).real {.greenCircle}) ↔
      56 / 15 < exp (lam * g.gap) ∧ exp (lam * g.gap) < 124 / 15 := by
  have hE : 0 < 1 + exp (lam * g.gap) := by positivity
  rw [salience_listener_circle_iff hlam, salience_listener_green_iff hlam, mul_zero, neg_zero,
    sigmoid_zero, zero_sub, zero_add, mul_neg, sigmoid_def, neg_neg, ← div_eq_mul_inv 139,
    ← div_eq_mul_inv 71, lt_div_iff₀ hE, div_lt_iff₀ hE]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Frank and Goodman's listener at the measured salience and rationality one takes *green* to
refer to the salient green square. -/
theorem frankGoodman_listener_green :
    (FrankGoodman2012.listener M salience 1 .green).real {.greenCircle} <
      (FrankGoodman2012.listener M salience 1 .green).real {.greenSquare} := by
  rw [FrankGoodman2012.listener, ← speaker_belief_uniform, listener_real_singleton_lt_iff,
    salience_real_singleton, green_greenCircle one_pos, salience_real_singleton,
    green_greenSquare one_pos, Goal.gap_belief, mul_zero, neg_zero, sigmoid_zero, zero_add,
    one_mul, sigmoid_def, neg_neg, exp_log two_pos]
  norm_num [listenerChoice]

-- (14)
theorem action_listener_window (hlam : 0 < lam) {lamL : ℝ} (hlamL : 0 < lamL)
    {ρ : Kernel (Word Colour Shape) Object}
    (hρ : ρ = policy lamL (listener salience (speaker .action (uniformOn .univ) lam 0))
      fun t ↦ Pi.single t 1) :
    ((ρ .circle).real {.greenCircle} < (ρ .circle).real {.blueCircle} ∧
      (ρ .green).real {.greenSquare} < (ρ .green).real {.greenCircle}) ↔
      56 / 15 < exp (lam / 2) ∧ exp (lam / 2) < 124 / 15 := by
  rw [hρ, policy_single_real_lt_iff _ hlamL, policy_single_real_lt_iff _ hlamL,
    salience_listener_window hlam, Goal.gap_action, ← div_eq_mul_inv]

end QingFranke2015
