module

public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.UniformOn
public import Linglib.Data.Examples.HeKaiserIskarous2025
public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# He, Kaiser and Iskarous (2025): Modeling sentence polarity asymmetries

This file formalizes the rational speech act models of He, Kaiser and Iskarous for a speaker who
says of a whole that it has a part, that it lacks it, or nothing. `Setting.speaker` is the standard
speaker of (1)–(4) on the kernel pipeline of `RSA.speaker`, under the Boolean meaning of (2) or the
fuzzy meaning `fuzzy` of (11)–(13), whose positive sentence holds at its state to a sigmoid degree
of that state's prior. `Setting.wonkyListener` is the wonky-world listener of (14)–(16), who infers
the state together with the world, normal at the measured prior or wonky at the uniform one, with
`Setting.wonkiness` its posterior probability
of the wonky world and the expected typicality of (17) the marginal of the state over the worlds;
the funky model of (18)–(22) is the same listener under the fuzzy meaning.

Under the Boolean meaning the likelihood of each polarity is a logistic function of the cost
saved by silence and the log prior of its state (`Setting.likelihood_boolean`): it falls as
the prior rises, and at equal priors the positive polarity is the likelier exactly when it is
the cheaper, the two coinciding at equal costs. The fuzzy positive sentence informs the
literal listener exactly when its degree exceeds one half, which the sigmoid degree does
above a threshold prior; below it the speaker prefers silence to the positive sentence, where
the Boolean speaker prefers the sentence at every prior below the exponential of the cost
saved. The wonky listener's wonkiness rises above its prior exactly when the described
state's prior exceeds one half, whatever the costs, and its expected typicality moves the
state's prior toward one half by the wonkiness.

## Implementation notes

* The sigmoid of (13) in the wonky world takes that world's prior of the positive state, one
  half; the paper does not say which prior it takes there.
* The wonkiness of the Boolean wonky listener depends on the polarity only through the cost
  (`Setting.wonkiness_boolean`), so the polarities coincide at equal costs; the paper's costs
  differ, and its remark that the model does not differentiate the polarities holds of the
  direction of the wonkiness update, not of its size.

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

/-- The speaker says the positive sentence, its negation, or nothing. -/
inductive Utterance where
  | pos
  | neg
  | null
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Utterance := ⊤

/-- A state is described by the sentence of its polarity. -/
def State.utterance : State → Utterance
  | .pos => .pos
  | .neg => .neg

section Sums

variable {β : Type*} [AddCommMonoid β]

theorem sum_state (f : State → β) : ∑ st, f st = f .pos + f .neg := by
  rw [show ∑ st, f st = f .pos + (f .neg + 0) from rfl, add_zero]

end Sums

/-- A graded meaning gives the degree to which an utterance holds at a state. -/
abbrev Meaning := Utterance → State → ℝ

/-- Under the Boolean meaning of (2), each sentence holds at its state alone and silence
everywhere. -/
def boolean : Meaning
  | .pos, .pos => 1
  | .pos, .neg => 0
  | .neg, .neg => 1
  | .neg, .pos => 0
  | .null, _ => 1

/-- Under the fuzzy meaning of (11) and (12), the negative sentence holds at its state to the
degree `n` and the positive sentence to the degree `σ`, each to the complementary degree at the
other state, and silence holds everywhere. -/
def fuzzy (n σ : ℝ) : Meaning
  | .pos, .pos => σ
  | .pos, .neg => 1 - σ
  | .neg, .neg => n
  | .neg, .pos => 1 - n
  | .null, _ => 1

theorem boolean_nonneg (u : Utterance) (st : State) : 0 ≤ boolean u st := by
  cases u <;> cases st <;> simp [boolean]

theorem fuzzy_nonneg {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (u : Utterance) (st : State) : 0 ≤ fuzzy n σ u st := by
  cases u <;> cases st <;> simp [fuzzy] <;> linarith

theorem fuzzy_one_one : fuzzy 1 1 = boolean := by
  funext u st; cases u <;> cases st <;> simp [fuzzy, boolean]

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
  Measure.sum_smul_dirac_apply_singleton _ st

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

/-! ### The literal listener and the speaker, (1) to (3) -/

section Listener

variable (P : Measure State) (m : Meaning)

/-- The literal listener of (1) reweights the prior by the meaning. -/
noncomputable def L0 : Kernel Utterance State :=
  Kernel.ofDensity P fun u st ↦ ENNReal.ofReal (m u st)

instance : IsFiniteKernel (L0 P m) := inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

theorem L0_ne_top (u : Utterance) (st : State) : L0 P m u {st} ≠ ∞ := measure_ne_top _ _

theorem L0_eq_zero {u : Utterance} {st : State} (h : m u st = 0) : L0 P m u {st} = 0 := by
  rw [L0, Kernel.ofDensity_apply_singleton, h, ENNReal.ofReal_zero, zero_mul, ENNReal.zero_div]

variable [IsFiniteMeasure P]

theorem L0_ne_zero {u : Utterance} {st : State} (h : 0 < m u st) (hst : P {st} ≠ 0) :
    L0 P m u {st} ≠ 0 := by
  rw [L0, Kernel.ofDensity_apply_singleton]
  exact (ENNReal.div_pos_iff.2 ⟨mul_ne_zero (ENNReal.ofReal_pos.2 h).ne' hst,
    ENNReal.sum_ne_top.2 fun st' _ ↦
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)⟩).ne'

variable (hm : ∀ u st, 0 ≤ m u st)
include hm

theorem L0_real (u : Utterance) (st : State) :
    (L0 P m u {st}).toReal = m u st * P.real {st} / ∑ st', m u st' * P.real {st'} := by
  rw [L0, Kernel.ofDensity_apply_singleton, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hm u st), ENNReal.toReal_sum fun st' _ ↦
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _), measureReal_def]
  congr 1
  exact Finset.sum_congr rfl fun st' _ ↦ by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hm u st'), measureReal_def]

end Listener

section Speaker

variable (P : Measure State) (m : Meaning) (s : Setting)

/-- The speaker of (3) is the softmax of the literal listener's log probability less the cost,
scaled by the rationality. -/
noncomputable def speaker : Kernel State Utterance := RSA.speaker s.α s.cost (L0 P m) Measure.dirac

instance : IsFiniteKernel (speaker P m s) := inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

theorem speaker_eq_zero {u : Utterance} {st : State} (h : m u st = 0) :
    speaker P m s st {u} = 0 :=
  RSA.speaker_dirac_apply_singleton_eq_zero s.α_pos (L0_eq_zero P m h)

theorem speaker_real_eq_zero {u : Utterance} {st : State} (h : m u st = 0) :
    (speaker P m s st).real {u} = 0 := by
  rw [measureReal_def, speaker_eq_zero P m s h, ENNReal.toReal_zero]

variable [IsFiniteMeasure P]

theorem speaker_ne_zero {u : Utterance} {st : State} (h : 0 < m u st) (hst : P {st} ≠ 0) :
    speaker P m s st {u} ≠ 0 :=
  RSA.speaker_dirac_apply_singleton_ne_zero s.α_pos.le (L0_ne_zero P m h hst)

theorem speaker_real_pos {u : Utterance} {st : State} (h : 0 < m u st) (hst : P {st} ≠ 0) :
    0 < (speaker P m s st).real {u} :=
  ENNReal.toReal_pos (speaker_ne_zero P m s h hst) (measure_ne_top _ _)

theorem speaker_real_lt_iff {u v : Utterance} {st : State} (hu : 0 < m u st) (hv : 0 < m v st)
    (hst : P {st} ≠ 0) :
    (speaker P m s st).real {u} < (speaker P m s st).real {v} ↔
      Real.log (L0 P m u {st}).toReal - s.cost u < Real.log (L0 P m v {st}).toReal - s.cost v :=
  RSA.speaker_dirac_real_singleton_lt_iff_log s.α_pos (L0_ne_zero P m hu hst)
    (L0_ne_zero P m hv hst)

theorem speaker_real_of_pair (hm : ∀ u st, 0 ≤ m u st) {u v : Utterance} {st : State}
    (huv : u ≠ v) (hu : 0 < m u st) (hv : 0 < m v st) (hsupp : ∀ x, 0 < m x st → x = u ∨ x = v)
    (hst : P {st} ≠ 0) :
    (speaker P m s st).real {u} =
      Real.sigmoid (s.α * ((Real.log (L0 P m u {st}).toReal - s.cost u) -
        (Real.log (L0 P m v {st}).toReal - s.cost v))) :=
  RSA.speaker_dirac_real_singleton_of_pair s.α_pos huv (L0_ne_zero P m hu hst)
    (L0_ne_zero P m hv hst) fun x hx ↦
      hsupp x ((hm x st).lt_of_ne fun h ↦ hx (L0_eq_zero P m h.symm))

end Speaker

/-! ### Closed forms under the Boolean meaning -/

section Boolean

variable (P : Measure State) [IsProbabilityMeasure P] (hP : ∀ st, P {st} ≠ 0) (s : Setting)

theorem L0_null_real (m : Meaning) (hm : ∀ u st, 0 ≤ m u st) (hnull : ∀ st, m .null st = 1)
    (st : State) : (L0 P m .null {st}).toReal = P.real {st} := by
  rw [L0_real P m hm]
  simp only [hnull, one_mul, sum_measureReal_singleton_eq_one, div_one]

include hP

theorem L0_boolean_utterance_real (st : State) :
    (L0 P boolean st.utterance {st}).toReal = 1 := by
  rw [L0_real P boolean boolean_nonneg, sum_state]
  cases st <;> simp only [boolean, State.utterance, one_mul, zero_mul, add_zero, zero_add] <;>
    exact div_self (ENNReal.toReal_pos (hP _) (measure_ne_top _ _)).ne'

theorem speaker_boolean_real (st : State) :
    (speaker P boolean s st).real {st.utterance} =
      Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance - Real.log (P.real {st}))) := by
  rw [speaker_real_of_pair P boolean s boolean_nonneg (v := .null) (by cases st <;> decide)
      (by cases st <;> simp [boolean, State.utterance]) (by simp [boolean])
      (fun x hx ↦ by cases st <;> cases x <;> simp_all [boolean, State.utterance]) (hP st),
    L0_boolean_utterance_real P hP st, L0_null_real P boolean boolean_nonneg (fun _ ↦ rfl) st,
    Real.log_one]
  congr 1; ring

end Boolean

/-! ### The standard model (§3.2) and the fuzzy model (§4) -/

namespace Setting

variable (s : Setting)

/-- The speaker under the measured prior. -/
noncomputable abbrev speaker (m : Meaning) : Kernel State Utterance :=
  HeKaiserIskarous2025.speaker s.prior m s

/-- The utterance likelihood of a polarity is the speaker's use of a state's sentence at that
state. -/
noncomputable def likelihood (m : Meaning) (st : State) : ℝ := (s.speaker m st).real {st.utterance}

theorem likelihood_boolean (st : State) :
    s.likelihood boolean st =
      Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance - Real.log (s.statePrior st))) := by
  rw [likelihood, speaker, speaker_boolean_real s.prior s.prior_ne_zero s st, prior_real_singleton]

theorem likelihood_boolean_lt {s' : Setting} (hα : s.α = s'.α) (hc : s.cost = s'.cost)
    {st : State} (h : s.statePrior st < s'.statePrior st) :
    s'.likelihood boolean st < s.likelihood boolean st := by
  rw [likelihood_boolean, likelihood_boolean, ← hα, ← hc]
  exact Real.sigmoid_lt (mul_lt_mul_of_pos_left
    (by linarith [Real.log_lt_log (s.statePrior_pos st) h]) s.α_pos)

theorem likelihood_boolean_neg_lt_pos_iff {s' : Setting} (hα : s.α = s'.α) (hc : s.cost = s'.cost)
    (hp : s'.statePrior .neg = s.statePrior .pos) :
    s'.likelihood boolean .neg < s.likelihood boolean .pos ↔ s.cost .pos < s.cost .neg := by
  rw [likelihood_boolean, likelihood_boolean, ← hα, ← hc, hp, Real.sigmoid_lt_iff,
    mul_lt_mul_iff_of_pos_left s.α_pos]
  simp only [State.utterance]
  constructor <;> intro h <;> linarith

theorem likelihood_boolean_neg_eq_pos {s' : Setting} (hα : s.α = s'.α) (hc : s.cost = s'.cost)
    (hp : s'.statePrior .neg = s.statePrior .pos) (hcost : s.cost .pos = s.cost .neg) :
    s'.likelihood boolean .neg = s.likelihood boolean .pos := by
  rw [likelihood_boolean, likelihood_boolean, ← hα, ← hc, hp]
  simp only [State.utterance, hcost]

theorem speaker_boolean_pos_lt_null_iff :
    (s.speaker boolean .pos).real {.pos} < (s.speaker boolean .pos).real {.null} ↔
      Real.exp (s.cost .null - s.cost .pos) < s.p := by
  have h1 := L0_boolean_utterance_real s.prior s.prior_ne_zero .pos
  simp only [State.utterance] at h1
  rw [speaker, speaker_real_lt_iff s.prior boolean s (by simp [boolean])
      (by simp [boolean]) (s.prior_ne_zero _), h1,
    L0_null_real s.prior boolean boolean_nonneg (fun _ ↦ rfl), Real.log_one, prior_real_singleton,
    statePrior, ← Real.lt_log_iff_exp_lt s.p_pos]
  constructor <;> intro h <;> linarith

theorem statePrior_lt_L0_real_iff {m : Meaning} (hm : ∀ u st, 0 ≤ m u st) {u : Utterance}
    (hsum : m u .pos + m u .neg = 1) (st : State) :
    s.statePrior st < (L0 s.prior m u {st}).toReal ↔ 1 / 2 < m u st := by
  rw [L0_real s.prior m hm, sum_state]
  simp only [prior_real_singleton]
  have hp := s.p_pos
  have hp1 := s.p_lt_one
  have ha := hm u .pos
  have hb : m u .neg = 1 - m u .pos := by linarith
  have hpp := mul_pos hp (sub_pos.2 hp1)
  rw [hb]
  cases st <;> simp only [statePrior]
  · have hden : 0 < m u .pos * s.p + (1 - m u .pos) * (1 - s.p) := by
      nlinarith [mul_nonneg ha (sq_nonneg s.p),
        mul_nonneg (sub_nonneg.2 (show m u .pos ≤ 1 by linarith [hm u .neg])) (sq_nonneg (1 - s.p))]
    rw [lt_div_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  · have hden : 0 < m u .pos * s.p + (1 - m u .pos) * (1 - s.p) := by
      nlinarith [mul_nonneg ha (sq_nonneg s.p),
        mul_nonneg (sub_nonneg.2 (show m u .pos ≤ 1 by linarith [hm u .neg])) (sq_nonneg (1 - s.p))]
    rw [lt_div_iff₀ hden]
    constructor <;> intro h <;> nlinarith

theorem p_lt_L0_fuzzy_pos_iff {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    s.p < (L0 s.prior (fuzzy n σ) .pos {.pos}).toReal ↔ 1 / 2 < σ :=
  s.statePrior_lt_L0_real_iff (fuzzy_nonneg hn0 hn1 hσ0 hσ1) (u := .pos) (by simp [fuzzy]) .pos

theorem one_sub_p_lt_L0_fuzzy_neg_iff {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) :
    1 - s.p < (L0 s.prior (fuzzy n σ) .neg {.neg}).toReal ↔ 1 / 2 < n :=
  s.statePrior_lt_L0_real_iff (fuzzy_nonneg hn0 hn1 hσ0 hσ1) (u := .neg) (by simp [fuzzy]) .neg

theorem speaker_fuzzy_pos_lt_null {n σ : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 2) (hc : s.cost .null < s.cost .pos) :
    (s.speaker (fuzzy n σ) .pos).real {.pos} < (s.speaker (fuzzy n σ) .pos).real {.null} := by
  have hm := fuzzy_nonneg hn0 hn1 hσ0.le (by linarith : σ ≤ 1)
  rw [speaker, speaker_real_lt_iff s.prior (fuzzy n σ) s (u := .pos) (v := .null) (st := .pos)
      hσ0 (by simp [fuzzy]) (s.prior_ne_zero _), L0_null_real s.prior (fuzzy n σ) hm (fun _ ↦ rfl),
    prior_real_singleton]
  have hle : (L0 s.prior (fuzzy n σ) .pos {.pos}).toReal ≤ s.p :=
    not_lt.1 fun h ↦
      absurd ((s.p_lt_L0_fuzzy_pos_iff hn0 hn1 hσ0.le (by linarith)).1 h) (not_lt.2 hσ)
  have hpos : 0 < (L0 s.prior (fuzzy n σ) .pos {.pos}).toReal :=
    ENNReal.toReal_pos (L0_ne_zero s.prior (fuzzy n σ) hσ0 (s.prior_ne_zero _)) (L0_ne_top _ _ _ _)
  simp only [statePrior]
  linarith [Real.log_le_log hpos hle]

/-- The fuzzy meaning of §4.1 gives the negative sentence degree `n` and the positive sentence
the sigmoid degree at the measured prior of the positive state. -/
noncomputable def fuzzyMeaning (θ : Sigmoid) (n : ℝ) : Meaning := fuzzy n (θ.eval s.p)

-- §4.1
theorem speaker_fuzzyMeaning_pos_lt_null (θ : Sigmoid) {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1)
    (hk : 0 < θ.k) (hL : 0 < θ.L) (hc0 : 0 ≤ θ.c) (hc : θ.c < 1 / 2) (hLc : 1 / 2 < θ.L + θ.c)
    (hp : s.p < θ.threshold) (hcost : s.cost .null < s.cost .pos) :
    (s.speaker (s.fuzzyMeaning θ n) .pos).real {.pos} <
      (s.speaker (s.fuzzyMeaning θ n) .pos).real {.null} :=
  s.speaker_fuzzy_pos_lt_null hn0 hn1
    (add_pos_of_pos_of_nonneg (mul_pos hL (Real.sigmoid_pos _)) hc0)
    ((θ.eval_lt_half_iff hk hL hc hLc s.p).2 hp).le hcost

end Setting

/-! ### The wonky-world listener (§5) and the funky listener (§6) -/

/-- The complex prior of (5) has two worlds, the normal world with the measured prior and the
wonky world with the uniform one. -/
inductive World where
  | normal
  | wonky
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

theorem sum_world {β : Type*} [AddCommMonoid β] (f : World → β) :
    ∑ w, f w = f .normal + f .wonky := by
  rw [show ∑ w, f w = f .normal + (f .wonky + 0) from rfl, add_zero]

/-- Under a wonkiness `ω` the wonky world has weight `ω` and the normal world `1 - ω`. -/
def wonkinessWeight (ω : ℝ) : World → ℝ
  | .normal => 1 - ω
  | .wonky => ω

/-- The prior over worlds. -/
noncomputable def wonkinessPrior (ω : ℝ) : Measure World :=
  ∑ w, ENNReal.ofReal (wonkinessWeight ω w) • Measure.dirac w

theorem wonkinessPrior_apply_singleton (ω : ℝ) (w : World) :
    wonkinessPrior ω {w} = ENNReal.ofReal (wonkinessWeight ω w) :=
  Measure.sum_smul_dirac_apply_singleton _ w

instance (ω : ℝ) : IsFiniteMeasure (wonkinessPrior ω) :=
  ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    exact ENNReal.sum_lt_top.2 fun w _ ↦ by
      rw [wonkinessPrior_apply_singleton]; exact ENNReal.ofReal_lt_top⟩

namespace Setting

variable (s : Setting)

/-- The prior over states is the measured one in the normal world and uniform in the wonky
one. -/
noncomputable def worldPrior : World → Measure State
  | .normal => s.prior
  | .wonky => uniformOn Set.univ

instance (w : World) : IsProbabilityMeasure (s.worldPrior w) := by
  cases w
  · exact inferInstanceAs (IsProbabilityMeasure s.prior)
  · exact isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

theorem worldPrior_ne_zero (w : World) (st : State) : s.worldPrior w {st} ≠ 0 := by
  cases w
  · exact s.prior_ne_zero st
  · exact uniformOn_univ_singleton_ne_zero st

theorem worldPrior_real_normal (st : State) : (s.worldPrior .normal).real {st} = s.statePrior st :=
  s.prior_real_singleton st

theorem worldPrior_real_wonky (st : State) : (s.worldPrior .wonky).real {st} = 1 / 2 := by
  rw [worldPrior, uniformOn_univ_real_singleton, show Fintype.card State = 2 from rfl]
  norm_num

/-- In each world, the wonky speaker of (14) and (15) is the speaker under that world's prior
and meaning, the world riding in the state. -/
noncomputable def wonkySpeaker (m : World → Meaning) (p : State × World) : Measure Utterance :=
  HeKaiserIskarous2025.speaker (s.worldPrior p.2) (m p.2) s p.1

theorem wonkySpeaker_apply (m : World → Meaning) (st : State) (w : World) :
    s.wonkySpeaker m (st, w) = HeKaiserIskarous2025.speaker (s.worldPrior w) (m w) s st := rfl

instance (m : World → Meaning) (p : State × World) : IsFiniteMeasure (s.wonkySpeaker m p) :=
  inferInstanceAs (IsFiniteMeasure (RSA.speaker _ _ _ _ _))

/-- The prior of (16) is the measured prior over states, independent of the wonkiness. -/
noncomputable def wonkyJoint (ω : ℝ) : Measure (State × World) := s.prior.prod (wonkinessPrior ω)

instance (ω : ℝ) : IsFiniteMeasure (s.wonkyJoint ω) :=
  inferInstanceAs (IsFiniteMeasure (s.prior.prod (wonkinessPrior ω)))

theorem wonkyJoint_apply_singleton (ω : ℝ) (st : State) (w : World) :
    s.wonkyJoint ω {(st, w)} =
      ENNReal.ofReal (s.statePrior st) * ENNReal.ofReal (wonkinessWeight ω w) := by
  rw [wonkyJoint, ← Set.singleton_prod_singleton, Measure.prod_prod, prior_apply_singleton,
    wonkinessPrior_apply_singleton]

theorem wonkyJoint_real_singleton {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (st : State) (w : World) :
    (s.wonkyJoint ω).real {(st, w)} = s.statePrior st * wonkinessWeight ω w := by
  rw [measureReal_def, wonkyJoint_apply_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (s.statePrior_pos st).le, ENNReal.toReal_ofReal]
  cases w
  · exact sub_nonneg.2 hω1
  · exact hω0

/-- The wonky listener of (16) inverts the wonky speaker over states and worlds against the
prior of (16). -/
noncomputable def wonkyListener (m : World → Meaning) (ω : ℝ) : Kernel Utterance (State × World) :=
  listener (s.wonkyJoint ω) (s.wonkySpeaker m)

theorem isProbabilityMeasure_wonkyListener_boolean {ω : ℝ} (hω0 : 0 < ω) (st : State) :
    IsProbabilityMeasure (s.wonkyListener (fun _ ↦ boolean) ω st.utterance) :=
  isProbabilityMeasure_listener_of_ne_zero (w := (st, World.wonky)) _ _
    (by
      rw [wonkyJoint_apply_singleton]
      exact mul_ne_zero (ENNReal.ofReal_pos.2 (s.statePrior_pos st)).ne'
        (ENNReal.ofReal_pos.2 hω0).ne')
    (speaker_ne_zero _ boolean s (by cases st <;> simp [boolean, State.utterance])
      (s.worldPrior_ne_zero _ st))

/-- The posterior wonkiness after the sentence of a state. -/
noncomputable def wonkiness (m : World → Meaning) (ω : ℝ) (st : State) : ℝ :=
  (s.wonkyListener m ω st.utterance).snd.real {.wonky}

/-- The expected typicality of (17) weighs the prior of a state in each world by the posterior
over worlds after the state's sentence. -/
noncomputable def expectedTypicality (m : World → Meaning) (ω : ℝ) (st : State) : ℝ :=
  ∑ w, (s.wonkyListener m ω st.utterance).snd.real {w} * (s.worldPrior w).real {st}

theorem expectedTypicality_eq (m : World → Meaning) (ω : ℝ) (st : State)
    [IsProbabilityMeasure (s.wonkyListener m ω st.utterance)] :
    s.expectedTypicality m ω st =
      s.statePrior st + s.wonkiness m ω st * (1 / 2 - s.statePrior st) := by
  have h1 : (s.wonkyListener m ω st.utterance).snd.real {.normal} +
      (s.wonkyListener m ω st.utterance).snd.real {.wonky} = 1 := by
    rw [← sum_world (fun w ↦ (s.wonkyListener m ω st.utterance).snd.real {w}),
      sum_measureReal_singleton_eq_one]
  rw [expectedTypicality, sum_world, worldPrior_real_normal, worldPrior_real_wonky, wonkiness]
  linear_combination s.statePrior st * h1

theorem wonkiness_boolean {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (st : State) :
    s.wonkiness (fun _ ↦ boolean) ω st =
      ω * (HeKaiserIskarous2025.speaker (s.worldPrior .wonky) boolean s st).real {st.utterance} /
        (ω * (HeKaiserIskarous2025.speaker (s.worldPrior .wonky) boolean s st).real {st.utterance} +
          (1 - ω) *
            (HeKaiserIskarous2025.speaker (s.worldPrior .normal) boolean s st).real
              {st.utterance}) := by
  have hb : 0 < boolean st.utterance st := by cases st <;> simp [boolean, State.utterance]
  have hpos : ∀ w, 0 < (HeKaiserIskarous2025.speaker (s.worldPrior w) boolean s st).real
      {st.utterance} := fun w ↦
    speaker_real_pos _ boolean s hb (s.worldPrior_ne_zero w st)
  have hx := s.statePrior_pos st
  have h1ω := sub_pos.2 hω1
  rw [wonkiness, wonkyListener, listener_snd_real_singleton, Fintype.sum_prod_type]
  simp only [sum_state, sum_world, wonkySpeaker_apply, s.wonkyJoint_real_singleton hω0.le hω1.le,
    wonkinessWeight]
  cases st
  · simp only [State.utterance] at hpos ⊢
    rw [speaker_real_eq_zero _ boolean s (u := .pos) (st := .neg) rfl,
      speaker_real_eq_zero _ boolean s (u := .pos) (st := .neg) rfl]
    simp only [mul_zero, add_zero]
    have := hpos .wonky
    have := hpos .normal
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · simp only [State.utterance] at hpos ⊢
    rw [speaker_real_eq_zero _ boolean s (u := .neg) (st := .pos) rfl,
      speaker_real_eq_zero _ boolean s (u := .neg) (st := .pos) rfl]
    simp only [mul_zero, add_zero, zero_add]
    have := hpos .wonky
    have := hpos .normal
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring

theorem wonkiness_boolean_pos {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (st : State) :
    0 < s.wonkiness (fun _ ↦ boolean) ω st := by
  have hb : 0 < boolean st.utterance st := by cases st <;> simp [boolean, State.utterance]
  have hpos : ∀ w, 0 < (HeKaiserIskarous2025.speaker (s.worldPrior w) boolean s st).real
      {st.utterance} := fun w ↦
    speaker_real_pos _ boolean s hb (s.worldPrior_ne_zero w st)
  have h1ω := sub_pos.2 hω1
  rw [wonkiness_boolean s hω0 hω1]
  have := hpos .wonky
  have := hpos .normal
  positivity

-- §5.3, Figure 6
theorem lt_wonkiness_iff {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (st : State) :
    ω < s.wonkiness (fun _ ↦ boolean) ω st ↔ 1 / 2 < s.statePrior st := by
  rw [wonkiness_boolean s hω0 hω1,
    speaker_boolean_real (s.worldPrior .wonky) (s.worldPrior_ne_zero .wonky) s st,
    speaker_boolean_real (s.worldPrior .normal) (s.worldPrior_ne_zero .normal) s st,
    worldPrior_real_wonky, worldPrior_real_normal]
  set Sw := Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance - Real.log (1 / 2))) with hSw
  set Sn := Real.sigmoid (s.α * (s.cost .null - s.cost st.utterance - Real.log (s.statePrior st)))
    with hSn
  have hSw0 : 0 < Sw := Real.sigmoid_pos _
  have hSn0 : 0 < Sn := Real.sigmoid_pos _
  have h1ω := sub_pos.2 hω1
  have hden : 0 < ω * Sw + (1 - ω) * Sn := by positivity
  have key : ω * (ω * Sw + (1 - ω) * Sn) < ω * Sw ↔ Sn < Sw := by
    constructor <;> intro h <;> nlinarith [mul_pos hω0 h1ω]
  rw [lt_div_iff₀ hden, key, hSw, hSn, Real.sigmoid_lt_iff, mul_lt_mul_iff_of_pos_left s.α_pos,
    sub_lt_sub_iff_left, Real.log_lt_log_iff (by norm_num) (s.statePrior_pos st)]

-- §5.3, Figure 5
theorem statePrior_lt_expectedTypicality_iff {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (st : State) :
    s.statePrior st < s.expectedTypicality (fun _ ↦ boolean) ω st ↔ s.statePrior st < 1 / 2 := by
  have := s.isProbabilityMeasure_wonkyListener_boolean hω0 st
  rw [expectedTypicality_eq, lt_add_iff_pos_right,
    mul_pos_iff_of_pos_left (s.wonkiness_boolean_pos hω0 hω1 st), sub_pos]

theorem wonkiness_boolean_neg_eq_pos {s' : Setting} {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1)
    (hα : s.α = s'.α) (hc : s.cost = s'.cost) (hp : s'.statePrior .neg = s.statePrior .pos)
    (hcost : s.cost .pos = s.cost .neg) :
    s'.wonkiness (fun _ ↦ boolean) ω .neg = s.wonkiness (fun _ ↦ boolean) ω .pos := by
  rw [wonkiness_boolean s' hω0 hω1, wonkiness_boolean s hω0 hω1,
    speaker_boolean_real (s'.worldPrior .wonky) (s'.worldPrior_ne_zero .wonky) s',
    speaker_boolean_real (s'.worldPrior .normal) (s'.worldPrior_ne_zero .normal) s',
    speaker_boolean_real (s.worldPrior .wonky) (s.worldPrior_ne_zero .wonky) s,
    speaker_boolean_real (s.worldPrior .normal) (s.worldPrior_ne_zero .normal) s,
    worldPrior_real_wonky, worldPrior_real_wonky, worldPrior_real_normal, worldPrior_real_normal,
    ← hα, ← hc, hp]
  simp only [State.utterance, hcost]

/-- In a world, the funky listener of (18) to (20) uses the fuzzy meaning at that world's prior
of the positive state. -/
noncomputable def funkyMeaning (θ : Sigmoid) (n : ℝ) (w : World) : Meaning :=
  fuzzy n (θ.eval ((s.worldPrior w).real {.pos}))

-- §6.2
theorem wonkySpeaker_funkyMeaning_normal (θ : Sigmoid) (n : ℝ) (st : State) :
    s.wonkySpeaker (s.funkyMeaning θ n) (st, .normal) = s.speaker (s.fuzzyMeaning θ n) st := by
  rw [wonkySpeaker_apply, funkyMeaning, worldPrior_real_normal]
  rfl

end Setting

end HeKaiserIskarous2025
