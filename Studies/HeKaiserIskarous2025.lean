module

public import Linglib.Data.Examples.HeKaiserIskarous2025
public import Linglib.Pragmatics.Probabilistic.LexicalUncertainty
public import Mathlib.Tactic.DeriveFintype

/-!
# He, Kaiser and Iskarous (2025): Modeling sentence polarity asymmetries

He, Kaiser and Iskarous model a speaker who says of a whole that it has a part, that it lacks it,
or nothing. Under the Boolean meaning, at equal priors [the positive sentence is the likelier
exactly when it is the cheaper](##Setting.likelihood_standardSpeaker_neg_lt_pos_iff), against
their participants' preference for low-prior negatives. Under the fuzzy meaning [the speaker
prefers silence to a positive sentence of low prior](##Setting.fuzzySpeaker_pos_lt_null). In the
wonky-world model [the listener revises toward the wonky world exactly when the described state's
prior exceeds one half](##Setting.lt_wonkiness_iff), and [the typicality she infers rises above
the prior exactly when that belief falls](##Setting.statePrior_lt_expectedTypicality_iff).

## Implementation notes

* The sigmoid of (13) in the wonky world takes that world's prior of the positive state, one
  half; the paper does not say which prior it takes there.
* The `P(world)` of (17) is the listener's posterior over the worlds, as the prose around it says.
* The wonkiness depends on the polarity only through the cost, so the polarities coincide at equal
  costs; the paper's costs differ, and its remark that the model does not differentiate the
  polarities holds of the direction of the wonkiness update, not of its size.

## TODO

* The best-fit predictions of Figures 4, 5 and 7 and the mean squared errors of §4.2 and §5.2.
* The funky listener's typicality difference between the polarities (§6.2).

## References

* [he-kaiser-iskarous-2025]
* [frank-goodman-2012]
* [degen-etal-2015]
* [cremers-wilcox-spector-2023]
* [degen-etal-2020]
* [horn-1989]
-/

@[expose] public section

namespace HeKaiserIskarous2025

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### States, utterances and meanings -/

/-- In one state the whole has the part, in the other it lacks it. -/
inductive State where
  | pos
  | neg
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ ↦ trivial⟩

/-- The speaker says the positive sentence, its negation, or nothing. -/
inductive Utterance where
  | pos
  | neg
  | null
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- A state is described by the sentence of its polarity. -/
def State.utterance : State → Utterance
  | .pos => .pos
  | .neg => .neg

theorem sum_state {β : Type*} [AddCommMonoid β] (f : State → β) :
    ∑ st, f st = f .pos + f .neg := by
  rw [show ∑ st, f st = f .pos + (f .neg + 0) from rfl, add_zero]

/-- Under the Boolean meaning of (2), each sentence is true at its state alone and silence
everywhere. -/
def extension : Utterance → Set State
  | .pos => {.pos}
  | .neg => {.neg}
  | .null => Set.univ

theorem extension_utterance (st : State) : extension st.utterance = {st} := by cases st <;> rfl

theorem eq_or_eq_null_of_mem_extension {st : State} {u : Utterance} (h : st ∈ extension u) :
    u = st.utterance ∨ u = .null := by
  cases u <;> cases st <;> simp_all [extension, State.utterance]

theorem not_mem_extension_utterance {st st' : State} (h : st' ≠ st) :
    st' ∉ extension st.utterance := by
  rw [extension_utterance]; exact h

/-- Under the fuzzy meaning of (11) and (12), the negative sentence holds at its state to the
degree `n` and the positive sentence to the degree `σ`, each to the complementary degree at the
other state, and silence holds everywhere. -/
def fuzzy (n σ : ℝ) : Utterance → State → ℝ
  | .pos, .pos => σ
  | .pos, .neg => 1 - σ
  | .neg, .neg => n
  | .neg, .pos => 1 - n
  | .null, _ => 1

theorem fuzzy_nonneg {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (u : Utterance) (st : State) : 0 ≤ fuzzy n σ u st := by
  cases u <;> cases st <;> simp [fuzzy] <;> linarith

/-- The sigmoid of (13) has a height, a steepness, a midpoint and an offset. -/
structure Sigmoid where
  /-- The height. -/
  L : ℝ
  /-- The steepness. -/
  k : ℝ
  /-- The midpoint. -/
  x0 : ℝ
  /-- The offset. -/
  c : ℝ

namespace Sigmoid

variable (θ : Sigmoid)

/-- The sigmoid of (13) gives the degree of the positive sentence at its state as a function of
that state's prior. -/
noncomputable def eval (x : ℝ) : ℝ := θ.L * Real.sigmoid (θ.k * (x - θ.x0)) + θ.c

/-- The prior below which the sigmoid degree is below one half. -/
noncomputable def threshold : ℝ :=
  θ.x0 + Real.log ((1 / 2 - θ.c) / (θ.L + θ.c - 1 / 2)) / θ.k

theorem eval_lt_half_iff (hk : 0 < θ.k) (hL : 0 < θ.L) (hc : θ.c < 1 / 2)
    (hLc : 1 / 2 < θ.L + θ.c) (x : ℝ) : θ.eval x < 1 / 2 ↔ x < θ.threshold := by
  have ht0 : 0 < (1 / 2 - θ.c) / θ.L := div_pos (by linarith) hL
  have ht1 : (1 / 2 - θ.c) / θ.L < 1 := (div_lt_one hL).2 (by linarith)
  have key : (1 / 2 - θ.c) / θ.L / (1 - (1 / 2 - θ.c) / θ.L) =
      (1 / 2 - θ.c) / (θ.L + θ.c - 1 / 2) := by
    have h1 : θ.L + θ.c - 1 / 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [eval, ← lt_sub_iff_add_lt, ← lt_div_iff₀' hL, ← Real.sigmoid_logit ⟨ht0, ht1⟩,
    Real.sigmoid_lt_iff, Real.logit, key, ← lt_div_iff₀' hk, sub_lt_iff_lt_add', threshold]

end Sigmoid

/-- The best-fit sigmoid of §4.2. -/
noncomputable def bestFit : Sigmoid := ⟨7 / 10, 6, 7 / 20, 3 / 10⟩

/-- The best-fit degree of the negative sentence at its state, §4.2. -/
noncomputable def bestFitNeg : ℝ := 4 / 5

theorem bestFit_threshold : bestFit.threshold = 7 / 20 - Real.log (5 / 2) / 6 := by
  rw [Sigmoid.threshold, show (1 / 2 - bestFit.c) / (bestFit.L + bestFit.c - 1 / 2) = (5 / 2)⁻¹ by
    norm_num [bestFit], Real.log_inv]
  norm_num [bestFit]
  ring

/-! ### Priors and costs -/

/-- A model is fixed by the prior probability of the positive state, the rationality `α`, and
the costs. -/
structure Setting where
  /-- The prior probability of the positive state. -/
  p : ℝ
  /-- The rationality. -/
  α : ℝ
  /-- The cost of an utterance. -/
  cost : Utterance → ℝ
  /-- The positive state is possible. -/
  p_pos : 0 < p
  /-- The negative state is possible. -/
  p_lt_one : p < 1
  /-- The rationality is positive. -/
  α_pos : 0 < α

/-- In §3.2 silence is free, the positive sentence costs one and its negation two, the marked
form being the costlier. -/
noncomputable def markednessCost : Utterance → ℝ
  | .pos => 1
  | .neg => 2
  | .null => 0

namespace Setting

variable (s : Setting)

/-- The prior probability of a state. -/
def statePrior : State → ℝ
  | .pos => s.p
  | .neg => 1 - s.p

theorem statePrior_pos (st : State) : 0 < s.statePrior st := by
  cases st
  · exact s.p_pos
  · exact sub_pos.2 s.p_lt_one

/-- The measured prior over states. -/
noncomputable def prior : Measure State :=
  ∑ st, ENNReal.ofReal (s.statePrior st) • Measure.dirac st

theorem prior_apply_singleton (st : State) : s.prior {st} = ENNReal.ofReal (s.statePrior st) :=
  Measure.finsetSum_smul_dirac_singleton

theorem prior_real_singleton (st : State) : s.prior.real {st} = s.statePrior st := by
  rw [measureReal_def, prior_apply_singleton, ENNReal.toReal_ofReal (s.statePrior_pos st).le]

theorem prior_ne_zero (st : State) : s.prior {st} ≠ 0 := by
  rw [prior_apply_singleton]
  exact (ENNReal.ofReal_pos.2 (s.statePrior_pos st)).ne'

instance : IsProbabilityMeasure s.prior :=
  ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton, sum_state, prior_apply_singleton,
      prior_apply_singleton, ← ENNReal.ofReal_add (s.statePrior_pos _).le (s.statePrior_pos _).le]
    simp [statePrior]⟩

end Setting

/-! ### The literal listeners and the speaker, (1) to (3) -/

section Listener

variable (P : Measure State) (m : Utterance → State → ℝ)

/-- The literal listener of (1) under a graded meaning reweights the prior by the degree. -/
noncomputable def L0 : Kernel Utterance State :=
  Kernel.ofDensity P fun u st ↦ ENNReal.ofReal (m u st)

instance : IsFiniteKernel (L0 P m) := inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

-- (2) is (11) and (12) at degree one
theorem L0_fuzzy_one_one : L0 P (fuzzy 1 1) = listener P (truthful extension) := by
  rw [listener_truthful_eq_ofDensity, L0]
  congr 1
  funext u st
  cases u <;> cases st <;> simp [fuzzy, extension]

variable [IsFiniteMeasure P]

theorem L0_ne_zero {u : Utterance} {st : State} (h : 0 < m u st) (hst : P {st} ≠ 0) :
    L0 P m u {st} ≠ 0 :=
  (Kernel.ofDensity_apply_singleton_ne_zero_iff P (fun _ ↦ ENNReal.ofReal_ne_top) st).2
    ⟨(ENNReal.ofReal_pos.2 h).ne', hst⟩

variable {m} (hm : ∀ u st, 0 ≤ m u st)
include hm

theorem L0_real (u : Utterance) (st : State) :
    (L0 P m u).real {st} = m u st * P.real {st} / ∑ st', m u st' * P.real {st'} := by
  rw [L0, Kernel.ofDensity_real_singleton _ _ _ fun _ ↦ ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal (hm _ _)]

theorem L0_null_real [IsProbabilityMeasure P] (hnull : ∀ st, m .null st = 1) (st : State) :
    (L0 P m .null).real {st} = P.real {st} := by
  rw [L0_real P hm]
  simp only [hnull, one_mul, sum_measureReal_singleton_eq_one, div_one]

end Listener

namespace Setting

variable (s : Setting)

/-- The speaker of (3) addressing a literal listener is the softmax of its log probability less
the cost, scaled by the rationality. -/
noncomputable def speaker (L : Kernel Utterance State) : Kernel State Utterance :=
  RSA.speaker s.α s.cost L Measure.dirac

instance (L : Kernel Utterance State) : IsFiniteKernel (s.speaker L) :=
  inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

section Boolean

variable (π : Measure State) [IsProbabilityMeasure π] {st : State} (hπ : π {st} ≠ 0)
include hπ

theorem speaker_truthful_real :
    (s.speaker (listener π (truthful extension)) st).real {st.utterance} =
      Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance - Real.log (π.real {st}))) :=
  speaker_listener_truthful_dirac_real_singleton_of_eq_singleton s.α_pos s.cost π extension hπ
    (by cases st <;> decide) (extension_utterance st) rfl fun _ ↦ eq_or_eq_null_of_mem_extension

theorem speaker_truthful_real_null :
    (s.speaker (listener π (truthful extension)) st).real {.null} =
      Real.sigmoid (s.α * (s.cost st.utterance - s.cost .null + Real.log (π.real {st}))) :=
  speaker_listener_truthful_dirac_real_singleton_of_eq_univ s.α_pos s.cost π extension hπ
    (by cases st <;> decide) (extension_utterance st) rfl fun _ ↦ eq_or_eq_null_of_mem_extension

end Boolean

/-- The speaker of the standard model under a prior addresses the Boolean literal listener of
that prior, (1) to (3). -/
noncomputable def standardSpeaker (π : Measure State) : Kernel State Utterance :=
  s.speaker (listener π (truthful extension))

/-- The speaker of the fuzzy model under a prior addresses the fuzzy literal listener of that
prior, the positive degree being the sigmoid of the prior of the positive state, (11) to (13). -/
noncomputable def fuzzySpeaker (θ : Sigmoid) (n : ℝ) (π : Measure State) : Kernel State Utterance :=
  s.speaker (L0 π (fuzzy n (θ.eval (π.real {.pos}))))

instance (π : Measure State) : IsFiniteKernel (s.standardSpeaker π) :=
  inferInstanceAs (IsFiniteKernel (s.speaker _))

instance (θ : Sigmoid) (n : ℝ) (π : Measure State) : IsFiniteKernel (s.fuzzySpeaker θ n π) :=
  inferInstanceAs (IsFiniteKernel (s.speaker _))

end Setting

/-- The utterance likelihood of a polarity is the speaker's use of a state's sentence at that
state. -/
noncomputable def likelihood (S : Kernel State Utterance) (st : State) : ℝ :=
  (S st).real {st.utterance}

/-! ### The standard model (§3.2) -/

namespace Setting

variable (s : Setting)

theorem likelihood_standardSpeaker (st : State) :
    likelihood (s.standardSpeaker s.prior) st =
      Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance - Real.log (s.statePrior st))) := by
  rw [likelihood, standardSpeaker, s.speaker_truthful_real s.prior (s.prior_ne_zero st),
    prior_real_singleton]

-- §3.2
theorem likelihood_standardSpeaker_lt {s' : Setting} (hα : s.α = s'.α) (hc : s.cost = s'.cost)
    {st : State} (h : s.statePrior st < s'.statePrior st) :
    likelihood (s'.standardSpeaker s'.prior) st < likelihood (s.standardSpeaker s.prior) st := by
  rw [likelihood_standardSpeaker, likelihood_standardSpeaker, ← hα, ← hc]
  exact Real.sigmoid_lt (mul_lt_mul_of_pos_left
    (by linarith [Real.log_lt_log (s.statePrior_pos st) h]) s.α_pos)

/-- At equal priors the standard model makes the positive sentence the likelier exactly when it
is the cheaper (§1, §3.2), so it cannot give a low-prior negative such as *The classroom doesn't
have a board* the advantage that speakers give it over *The classroom has a stove* unless the
negation is the cheaper sentence. -/
theorem likelihood_standardSpeaker_neg_lt_pos_iff {s' : Setting} (hα : s.α = s'.α)
    (hc : s.cost = s'.cost) (hp : s'.statePrior .neg = s.statePrior .pos) :
    likelihood (s'.standardSpeaker s'.prior) .neg < likelihood (s.standardSpeaker s.prior) .pos ↔
      s.cost .pos < s.cost .neg := by
  rw [likelihood_standardSpeaker, likelihood_standardSpeaker, ← hα, ← hc, hp,
    Real.sigmoid_lt_iff, mul_lt_mul_iff_of_pos_left s.α_pos]
  simp only [State.utterance]
  constructor <;> intro h <;> linarith

-- §3.2
theorem likelihood_standardSpeaker_neg_eq_pos {s' : Setting} (hα : s.α = s'.α)
    (hc : s.cost = s'.cost) (hp : s'.statePrior .neg = s.statePrior .pos)
    (hcost : s.cost .pos = s.cost .neg) :
    likelihood (s'.standardSpeaker s'.prior) .neg =
      likelihood (s.standardSpeaker s.prior) .pos := by
  rw [likelihood_standardSpeaker, likelihood_standardSpeaker, ← hα, ← hc, hp]
  simp only [State.utterance, hcost]

theorem standardSpeaker_pos_lt_null_iff :
    (s.standardSpeaker s.prior .pos).real {.pos} < (s.standardSpeaker s.prior .pos).real {.null} ↔
      Real.exp (s.cost .null - s.cost .pos) < s.p := by
  have h1 := s.speaker_truthful_real s.prior (st := .pos) (s.prior_ne_zero _)
  simp only [State.utterance] at h1
  rw [standardSpeaker, h1, s.speaker_truthful_real_null s.prior (s.prior_ne_zero _),
    Real.sigmoid_lt_iff,
    mul_lt_mul_iff_of_pos_left s.α_pos, prior_real_singleton, statePrior,
    ← Real.lt_log_iff_exp_lt s.p_pos]
  simp only [State.utterance]
  constructor <;> intro h <;> linarith

/-! ### The fuzzy model (§4) -/

theorem statePrior_lt_L0_real_iff {m : Utterance → State → ℝ} (hm : ∀ u st, 0 ≤ m u st)
    {u : Utterance} (hsum : m u .pos + m u .neg = 1) (st : State) :
    s.statePrior st < (L0 s.prior m u).real {st} ↔ 1 / 2 < m u st := by
  rw [L0_real s.prior hm, sum_state]
  simp only [prior_real_singleton]
  have hp := s.p_pos
  have hp1 := s.p_lt_one
  have ha := hm u .pos
  have hb : m u .neg = 1 - m u .pos := by linarith
  have hpp := mul_pos hp (sub_pos.2 hp1)
  have hden : 0 < m u .pos * s.p + (1 - m u .pos) * (1 - s.p) := by
    nlinarith [mul_nonneg ha (sq_nonneg s.p),
      mul_nonneg (sub_nonneg.2 (show m u .pos ≤ 1 by linarith [hm u .neg])) (sq_nonneg (1 - s.p))]
  rw [hb]
  cases st <;> simp only [statePrior] <;> rw [lt_div_iff₀ hden] <;>
    constructor <;> intro h <;> nlinarith

theorem p_lt_L0_fuzzy_pos_iff {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    s.p < (L0 s.prior (fuzzy n σ) .pos).real {.pos} ↔ 1 / 2 < σ :=
  s.statePrior_lt_L0_real_iff (fuzzy_nonneg hn0 hn1 hσ0 hσ1) (u := .pos) (by simp [fuzzy]) .pos

theorem speaker_fuzzy_pos_lt_null {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 2) (hc : s.cost .null < s.cost .pos) :
    (s.speaker (L0 s.prior (fuzzy n σ)) .pos).real {.pos} <
      (s.speaker (L0 s.prior (fuzzy n σ)) .pos).real {.null} := by
  have hm := fuzzy_nonneg hn0 hn1 hσ0.le (by linarith : σ ≤ 1)
  have hpos := L0_ne_zero s.prior (fuzzy n σ) (u := .pos) (st := .pos) hσ0 (s.prior_ne_zero .pos)
  rw [speaker, speaker_dirac_real_singleton_lt_iff_log s.α_pos hpos
      (L0_ne_zero s.prior (fuzzy n σ) (u := .null) (st := .pos) one_pos (s.prior_ne_zero .pos)),
    ← measureReal_def, ← measureReal_def, L0_null_real s.prior hm (fun _ ↦ rfl),
    prior_real_singleton]
  have hle : (L0 s.prior (fuzzy n σ) .pos).real {.pos} ≤ s.p :=
    not_lt.1 fun h ↦ absurd ((s.p_lt_L0_fuzzy_pos_iff hn0 hn1 hσ0.le (by linarith)).1 h)
      (not_lt.2 hσ)
  have hpos' : 0 < (L0 s.prior (fuzzy n σ) .pos).real {.pos} :=
    ENNReal.toReal_pos hpos (measure_ne_top _ _)
  simp only [statePrior]
  linarith [Real.log_le_log hpos' hle]

/-- Below the sigmoid's threshold, the fuzzy speaker prefers silence to the positive sentence
(§4.1), where the standard speaker prefers the sentence at every prior below the exponential of
the cost it adds. -/
theorem fuzzySpeaker_pos_lt_null (θ : Sigmoid) {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1)
    (hk : 0 < θ.k) (hL : 0 < θ.L) (hc0 : 0 ≤ θ.c) (hc : θ.c < 1 / 2) (hLc : 1 / 2 < θ.L + θ.c)
    (hp : s.p < θ.threshold) (hcost : s.cost .null < s.cost .pos) :
    (s.fuzzySpeaker θ n s.prior .pos).real {.pos} <
      (s.fuzzySpeaker θ n s.prior .pos).real {.null} := by
  rw [fuzzySpeaker, prior_real_singleton]
  exact s.speaker_fuzzy_pos_lt_null hn0 hn1
    (add_pos_of_pos_of_nonneg (mul_pos hL (Real.sigmoid_pos _)) hc0)
    ((θ.eval_lt_half_iff hk hL hc hLc s.p).2 hp).le hcost

/-! ### The wonky-world model (§5) and the funky model (§6)

The world is wonky (`true`) or normal (`false`), and the prior over states in each world is
`Kernel.boolKernel`. Under the speaker `s.standardSpeaker` of each world's prior the listener of
(16) is the wonky listener; under `s.fuzzySpeaker θ n` she is the funky listener of (18) to (22),
whose speaker in the normal world is the fuzzy one. -/

variable (ν : Measure Bool) (S : Measure State → Kernel State Utterance)

/-- The prior over states in each world, (5): the measured prior in the normal world and the
uniform prior in the wonky one. -/
noncomputable def worldPrior : Kernel Bool State := Kernel.boolKernel s.prior (uniformOn Set.univ)

instance : IsMarkovKernel s.worldPrior :=
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set State)) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  inferInstanceAs (IsMarkovKernel (Kernel.boolKernel _ _))

theorem worldPrior_ne_zero (w : Bool) (st : State) : s.worldPrior w {st} ≠ 0 := by
  cases w
  · exact s.prior_ne_zero st
  · exact uniformOn_univ_singleton_ne_zero st

theorem worldPrior_false_real (st : State) : (s.worldPrior false).real {st} = s.statePrior st :=
  s.prior_real_singleton st

theorem worldPrior_true_real (st : State) : (s.worldPrior true).real {st} = 1 / 2 := by
  rw [worldPrior, Kernel.boolKernel_true, uniformOn_univ_real_singleton,
    show Fintype.card State = 2 from rfl]
  norm_num

/-- The wonky listener of (16) infers the state and the world, the states under the measured prior
and the worlds under `ν`, where in each world the speaker addresses that world's prior, (14) and
(15). -/
noncomputable def wonkyListener : Kernel Utterance (State × Bool) :=
  listener (s.prior.prod ν) fun p ↦ S (s.worldPrior p.2) p.1

/-- The wonkiness after a state's sentence is the listener's posterior belief in the wonky
world. -/
noncomputable def wonkiness (st : State) : ℝ := (s.wonkyListener ν S st.utterance).snd.real {true}

/-- The expected typicality of (17) is the probability of the state under the common ground the
sentence leaves, each world's prior weighted by the listener's posterior over the worlds. -/
noncomputable def expectedTypicality (st : State) : ℝ :=
  (s.worldPrior ∘ₘ (s.wonkyListener ν S st.utterance).snd).real {st}

theorem expectedTypicality_eq (st : State)
    [IsProbabilityMeasure (s.wonkyListener ν S st.utterance)] :
    s.expectedTypicality ν S st =
      s.statePrior st + s.wonkiness ν S st * (1 / 2 - s.statePrior st) := by
  have h1 : (s.wonkyListener ν S st.utterance).snd.real {true} +
      (s.wonkyListener ν S st.utterance).snd.real {false} = 1 := by
    rw [← Fintype.sum_bool fun w ↦ (s.wonkyListener ν S st.utterance).snd.real {w},
      sum_measureReal_singleton_eq_one]
  rw [expectedTypicality, Measure.comp_real_singleton, Fintype.sum_bool, worldPrior_true_real,
    worldPrior_false_real, wonkiness]
  linear_combination s.statePrior st * h1

/-- The speaker under a prior averaged over the measured prior on states. -/
private noncomputable def averaged (π : Measure State) : Measure Utterance :=
  ∑ st, s.prior {st} • S π st

variable [∀ π, IsFiniteKernel (S π)]

private instance (π : Measure State) : IsFiniteMeasure (s.averaged S π) :=
  ⟨by
    rw [averaged, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.2 fun _ _ ↦ by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩

private theorem averaged_real (π : Measure State) (u : Utterance) :
    (s.averaged S π).real {u} = ∑ st, s.statePrior st * (S π st).real {u} := by
  rw [averaged, measureReal_def, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum fun _ _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  exact Finset.sum_congr rfl fun st _ ↦ by
    rw [ENNReal.toReal_mul, ← measureReal_def, prior_real_singleton, measureReal_def]

omit [∀ π, IsFiniteKernel (S π)] in
/-- The listener's belief about the world is the listener of the speaker of each world averaged
over the states. -/
private theorem wonkiness_eq_listener (st : State) :
    s.wonkiness ν S st =
      (listener ν (Kernel.boolKernel (s.averaged S s.prior) (s.averaged S (uniformOn Set.univ)))
        st.utterance).real {true} := by
  rw [wonkiness, show (s.wonkyListener ν S st.utterance).snd =
      (s.wonkyListener ν S).snd st.utterance from (Kernel.snd_apply _ _).symm, wonkyListener,
    listener_prod_snd]
  congr 3
  funext w
  cases w <;> rfl

private theorem averaged_standardSpeaker_real (π : Measure State) [IsProbabilityMeasure π]
    (hπ : ∀ st, π {st} ≠ 0) (st : State) :
    (s.averaged s.standardSpeaker π).real {st.utterance} =
      s.statePrior st * Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance -
        Real.log (π.real {st}))) := by
  have h0 (st' : State) (h : st' ≠ st) : (s.standardSpeaker π st').real {st.utterance} = 0 :=
    speaker_listener_truthful_dirac_real_singleton_eq_zero s.α_pos s.cost π extension
      (not_mem_extension_utterance h)
  rw [averaged_real, sum_state]
  cases st
  · rw [h0 .neg (by decide), mul_zero, add_zero, standardSpeaker,
      s.speaker_truthful_real π (hπ _)]
  · rw [h0 .pos (by decide), mul_zero, zero_add, standardSpeaker,
      s.speaker_truthful_real π (hπ _)]

private theorem averaged_standardSpeaker_pos (π : Measure State) [IsProbabilityMeasure π]
    (hπ : ∀ st, π {st} ≠ 0) (st : State) :
    0 < (s.averaged s.standardSpeaker π).real {st.utterance} := by
  rw [averaged_standardSpeaker_real _ _ hπ]
  exact mul_pos (s.statePrior_pos st) (Real.sigmoid_pos _)

private theorem averaged_standardSpeaker_lt_iff (st : State) :
    (s.averaged s.standardSpeaker s.prior).real {st.utterance} <
        (s.averaged s.standardSpeaker (uniformOn Set.univ)).real {st.utterance} ↔
      1 / 2 < s.statePrior st := by
  have hu : (uniformOn Set.univ : Measure State).real {st} = 1 / 2 := s.worldPrior_true_real st
  rw [averaged_standardSpeaker_real _ _ s.prior_ne_zero,
    averaged_standardSpeaker_real _ _ uniformOn_univ_singleton_ne_zero, prior_real_singleton, hu,
    mul_lt_mul_iff_of_pos_left (s.statePrior_pos st), Real.sigmoid_lt_iff,
    mul_lt_mul_iff_of_pos_left s.α_pos, sub_lt_sub_iff_left,
    Real.log_lt_log_iff (by norm_num) (s.statePrior_pos st)]

private theorem averaged_standardSpeaker_gt_iff (st : State) :
    (s.averaged s.standardSpeaker (uniformOn Set.univ)).real {st.utterance} <
        (s.averaged s.standardSpeaker s.prior).real {st.utterance} ↔
      s.statePrior st < 1 / 2 := by
  have hu : (uniformOn Set.univ : Measure State).real {st} = 1 / 2 := s.worldPrior_true_real st
  rw [averaged_standardSpeaker_real _ _ s.prior_ne_zero,
    averaged_standardSpeaker_real _ _ uniformOn_univ_singleton_ne_zero, prior_real_singleton, hu,
    mul_lt_mul_iff_of_pos_left (s.statePrior_pos st), Real.sigmoid_lt_iff,
    mul_lt_mul_iff_of_pos_left s.α_pos, sub_lt_sub_iff_left,
    Real.log_lt_log_iff (s.statePrior_pos st) (by norm_num)]

/-- The channel from the world to the state's sentence: the standard speaker of each world
averaged over the states. -/
private noncomputable abbrev channel : Kernel Bool Utterance :=
  Kernel.boolKernel (s.averaged s.standardSpeaker s.prior)
    (s.averaged s.standardSpeaker (uniformOn Set.univ))

variable [IsProbabilityMeasure ν] (hn : ν {false} ≠ 0) (hw : ν {true} ≠ 0)

omit [IsProbabilityMeasure ν] in
include hw in
private theorem comp_channel_ne_zero (st : State) : (s.channel ∘ₘ ν) {st.utterance} ≠ 0 :=
  Measure.comp_apply_singleton_ne_zero _ _ hw
    (ENNReal.toReal_pos_iff.1
      (s.averaged_standardSpeaker_pos _ uniformOn_univ_singleton_ne_zero st)).1.ne'

include hw in
private theorem wonkiness_eq_posterior (st : State) :
    s.wonkiness ν s.standardSpeaker st = ((s.channel†ν) st.utterance).real {true} := by
  rw [wonkiness_eq_listener, listener_apply_eq_posterior _ _ (s.comp_channel_ne_zero ν hw st)]

include hn hw

/-- The listener revises toward the wonky world after a state's sentence exactly when that state's
prior exceeds one half, whatever the costs (§5.3, Figure 6), as after *The house doesn't have a
ballroom*. -/
theorem lt_wonkiness_iff (st : State) :
    ν.real {true} < s.wonkiness ν s.standardSpeaker st ↔ 1 / 2 < s.statePrior st := by
  rw [s.wonkiness_eq_posterior ν hw, real_lt_posterior_real_singleton_iff_of_pair _ ν
      (by decide : true ≠ false) (fun b _ ↦ by cases b <;> simp) (s.comp_channel_ne_zero ν hw st)
      hw hn, Kernel.boolKernel_false, Kernel.boolKernel_true, averaged_standardSpeaker_lt_iff]

-- §5.3, Figure 6
theorem wonkiness_lt_iff (st : State) :
    s.wonkiness ν s.standardSpeaker st < ν.real {true} ↔ s.statePrior st < 1 / 2 := by
  rw [s.wonkiness_eq_posterior ν hw, posterior_real_singleton_lt_iff_of_pair _ ν
      (by decide : true ≠ false) (fun b _ ↦ by cases b <;> simp) (s.comp_channel_ne_zero ν hw st)
      hw hn, Kernel.boolKernel_false, Kernel.boolKernel_true, averaged_standardSpeaker_gt_iff]

omit hn in
theorem isProbabilityMeasure_wonkyListener (st : State) :
    IsProbabilityMeasure (s.wonkyListener ν s.standardSpeaker st.utterance) :=
  isProbabilityMeasure_listener_of_ne_zero (w := (st, true)) _ _
    (by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      exact mul_ne_zero (s.prior_ne_zero st) hw)
    (by
      rw [standardSpeaker, speaker,
        speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff s.α_pos]
      exact ⟨by rw [extension_utterance]; rfl, s.worldPrior_ne_zero _ st⟩)

omit hn in
theorem wonkiness_pos (st : State) : 0 < s.wonkiness ν s.standardSpeaker st := by
  rw [s.wonkiness_eq_posterior ν hw, posterior_real_singleton _ _ (s.comp_channel_ne_zero ν hw st)]
  exact div_pos (mul_pos (ENNReal.toReal_pos hw (measure_ne_top _ _))
    (s.averaged_standardSpeaker_pos _ uniformOn_univ_singleton_ne_zero st))
    (ENNReal.toReal_pos (s.comp_channel_ne_zero ν hw st) (measure_ne_top _ _))

/-- The typicality the listener infers from a state's sentence rises above the state's prior
exactly when her belief in the wonky world falls (§5.3): a typicality inference where a sentence
describes a state of prior below one half, an atypicality inference where its prior is above. -/
theorem statePrior_lt_expectedTypicality_iff (st : State) :
    s.statePrior st < s.expectedTypicality ν s.standardSpeaker st ↔
      s.wonkiness ν s.standardSpeaker st < ν.real {true} := by
  have := s.isProbabilityMeasure_wonkyListener ν hw st
  rw [expectedTypicality_eq, lt_add_iff_pos_right,
    mul_pos_iff_of_pos_left (s.wonkiness_pos ν hw st), sub_pos, s.wonkiness_lt_iff ν hn hw]

-- §5.3
theorem expectedTypicality_lt_statePrior_iff (st : State) :
    s.expectedTypicality ν s.standardSpeaker st < s.statePrior st ↔
      ν.real {true} < s.wonkiness ν s.standardSpeaker st := by
  have := s.isProbabilityMeasure_wonkyListener ν hw st
  have hW := s.wonkiness_pos ν hw st
  rw [expectedTypicality_eq, add_lt_iff_neg_left,
    show s.wonkiness ν s.standardSpeaker st * (1 / 2 - s.statePrior st) < 0 ↔
      1 / 2 - s.statePrior st < 0 from
      ⟨fun h ↦ neg_of_mul_neg_right h hW.le, mul_neg_of_pos_of_neg hW⟩,
    sub_neg, s.lt_wonkiness_iff ν hn hw]

omit hn hw in
-- §5.3
theorem wonkiness_neg_eq_pos {s' : Setting} (hα : s.α = s'.α) (hc : s.cost = s'.cost)
    (hp : s'.statePrior .neg = s.statePrior .pos) (hcost : s.cost .pos = s.cost .neg) :
    s'.wonkiness ν s'.standardSpeaker .neg = s.wonkiness ν s.standardSpeaker .pos := by
  have hu (t : Setting) (st : State) : (uniformOn Set.univ : Measure State).real {st} = 1 / 2 :=
    t.worldPrior_true_real st
  rw [wonkiness_eq_listener, wonkiness_eq_listener, listener_real_singleton,
    listener_real_singleton, Fintype.sum_bool, Fintype.sum_bool]
  simp only [Kernel.boolKernel_true, Kernel.boolKernel_false]
  rw [s'.averaged_standardSpeaker_real _ s'.prior_ne_zero,
    s'.averaged_standardSpeaker_real _ uniformOn_univ_singleton_ne_zero,
    s.averaged_standardSpeaker_real _ s.prior_ne_zero,
    s.averaged_standardSpeaker_real _ uniformOn_univ_singleton_ne_zero, prior_real_singleton,
    prior_real_singleton, hu s, hu s', ← hα, ← hc, hp]
  simp only [State.utterance, hcost]

end Setting

end HeKaiserIskarous2025
