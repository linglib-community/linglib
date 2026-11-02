module

public import Linglib.Core.InformationTheory.Entropy.Surprisal
public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Core.Topology.UnitInterval
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Data.Examples.BergenGoodman2015
public import Linglib.Data.Examples.Readers

/-!
# Bergen and Goodman (2015): The Strategic Use of Noise in Pragmatic Reasoning

This file models rational speech acts over a noisy channel from the utterance a speaker intends to
the one a listener perceives. Each listener inverts the channel composed with a speaker, merely
truthful for the literal listener. The speaker addresses the geometric pool of the listener over the
channel, [which is the listener itself when there is no noise](##geomPool_dirac), and at a belief
[she is the Luce choice of minus the channel-expected divergence of the listener from her
belief](##speaker_geomPool_eq_ofWeights). A sentence fragment has no literal meaning, yet [the
pragmatic listener reads "Bob" as Bob having gone](##Ellipsis.L1_subject) at every deletion rate
strictly between zero and one. Stress lowers the rate at which a name is misheard, so [a speaker who
knows that only Bob went prefers to stress it](##Prosody.S1_bobWent_lt_BOB_went), and [one unsure
whether Alice also went prefers it less](##Prosody.stressOdds_bobAtLeast_lt_onlyBob).

## Implementation notes

* Priors over meanings and intended utterances are uniform, the rationality is `1` and costs are
  `0`.
* The paper's channel inserts, deletes and replaces words independently. Here an intended utterance
  slips to at most one other, so each row of the channel is a Bernoulli measure: the deletion of the
  predicate for ellipsis, the replacement of one name by the other for prosody.
* For ellipsis the speaker chooses among the full sentences, which are indexed by the meanings they
  express, as in the paper's simplification.
* Prosody is perceived without noise, so the stressed and unstressed forms have separate channels.
  Any stressed rate below an unstressed rate of at most a half gives the results, not only the
  paper's half. The conjunction is never misheard and never stressed.
* The paper's listener reasons about the speaker's observation as well as the meaning. At depth one
  the observation enters the literal listener only through a factor the same for every utterance,
  so the speaker addresses the literal listener over meanings. The paper gives no observation model;
  the speaker who knows only that Bob went believes the two states in which he went equally likely.

## TODO

* The speaker's use of fragments needs utterance costs.
* The listener's exhaustive reading of stress needs her inference over the speaker's observations,
  whose distribution the paper does not give.

## References

* [bergen-goodman-2015]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA InformationTheory Finset Real unitInterval
open scoped ENNReal

namespace BergenGoodman2015

/-! ## The speaker over a noisy channel -/

section GeomPool

variable {V U W : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSpace W] [Fintype W]

/-- The geometric pool of the listener `L` over the channel `N` gives each state, at an intended
utterance, the geometric mean over the utterance's perceptions of the listener's mass there. -/
noncomputable def geomPool (N : V → Measure U) (L : U → Measure W) (v : V) : Measure W :=
  Measure.ofWeights fun w ↦ (N v).geomMean fun u ↦ L u {w}

variable [MeasurableSingletonClass W]

@[simp] theorem geomPool_apply_singleton (N : V → Measure U) (L : U → Measure W) (v : V) (w : W) :
    geomPool N L v {w} = (N v).geomMean fun u ↦ L u {w} :=
  Measure.ofWeights_apply_singleton _ w

instance (N : V → Measure U) (L : U → Measure W) [∀ u, IsFiniteMeasure (L u)] (v : V) :
    IsFiniteMeasure (geomPool N L v) :=
  Measure.isFiniteMeasure_ofWeights fun _ ↦ Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _

/-- With no noise the geometric pool of a listener is the listener, so the speaker over the channel
(eq. (7)) is the speaker of eq. (3). -/
theorem geomPool_dirac [MeasurableSingletonClass U] (L : U → Measure W) :
    geomPool Measure.dirac L = L :=
  funext fun u ↦ Measure.ext_of_singleton fun w ↦ by simp

/-- At a belief, the speaker over the channel weighs an utterance by the exponential of minus the
channel-expected divergence of the listener from her belief, to the power `α`, times the cost
weight: she is the Luce choice of the divergence utility of p. 345. -/
theorem speaker_geomPool_eq_ofWeights {O : Type*} [MeasurableSpace O] [Countable O]
    [MeasurableSingletonClass O] [MeasurableSpace V] [Fintype V] [MeasurableSingletonClass V]
    [MeasurableSingletonClass U] {α : ℝ} (hα : 0 ≤ α)
    (C : V → ℝ) (N : V → Measure U) [∀ v, IsProbabilityMeasure (N v)] (L : U → Measure W)
    [∀ u, IsProbabilityMeasure (L u)] (b : O → Measure W) [∀ o, IsProbabilityMeasure (b o)] :
    speaker α C (geomPool N L) b = Kernel.ofWeights fun o v ↦
      EReal.exp (-((∫⁻ u, klDiv (b o) (L u) ∂N v : ℝ≥0∞) : EReal)) ^ α *
        ENNReal.ofReal (exp (-(α * C v))) := by
  have hc0 (x : ℝ≥0∞) (hx : x ≠ ∞) : EReal.exp (-(x : EReal)) ^ α ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 (by simpa using hx))
      (by simp [EReal.coe_ennreal_ne_bot])).ne'
  have hct (x : ℝ≥0∞) : EReal.exp (-(x : EReal)) ^ α ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hα (by simp [EReal.coe_ennreal_ne_bot])
  rw [speaker]
  refine Kernel.ofWeights_eq_of_mul
    (c := fun o ↦ EReal.exp (-(ENNReal.ofReal (Hm[b o]) : EReal)) ^ α)
    (fun o ↦ hc0 _ ENNReal.ofReal_ne_top) (fun o ↦ hct _) fun o v ↦ ?_
  simp_rw [geomPool_apply_singleton]
  rw [Measure.geomMean_comm (b o) (N v) fun w u ↦ L u {w}]
  simp_rw [geomMean_eq_exp_neg_lintegral_surprisal, lintegral_surprisal_eq_ofReal_add_klDiv]
  rw [Measure.geomMean_exp_neg, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one, EReal.coe_ennreal_add, EReal.neg_add
      (.inl (EReal.coe_ennreal_ne_bot _)) (.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg,
    EReal.exp_add,
    ENNReal.mul_rpow_of_nonneg _ _ hα]
  ring

end GeomPool

/-! ## Ellipsis

Three meanings and the full sentences expressing them; deleting the predicate of a sentence leaves
its subject, a fragment with no literal meaning. -/

namespace Ellipsis

/-- Who went to the movies. -/
inductive Meaning
  | aliceWent
  | bobWent
  | nobodyWent
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Meaning := ⊤

/-- A perceived utterance is a full sentence "X went to the movies" or its subject alone. -/
inductive Utterance
  | full (m : Meaning)
  | subject (m : Meaning)
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

/-- The channel deletes the predicate of the intended sentence at rate `δ`. -/
noncomputable def N (δ : I) : Kernel Meaning Utterance :=
  Kernel.ofFunOfCountable fun m ↦ Ber(.subject m, .full m, δ)

instance (δ : I) : IsMarkovKernel (N δ) :=
  ⟨fun m ↦ by rw [N, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- The uniform prior over meanings. -/
noncomputable abbrev μ : Measure Meaning := Measure.count

/-- A full sentence is true exactly at the meaning it expresses. -/
def lit (m : Meaning) : Set Meaning := {m}

/-- The literal listener (eq. (6)) inverts the channel composed with a truthful speaker. -/
noncomputable abbrev L0 (δ : I) : Kernel Utterance Meaning :=
  listener μ fun m ↦ N δ ∘ₘ truthful lit m

/-- The speaker (eq. (7)), choosing among the full sentences. -/
noncomputable abbrev S1 (δ : I) : Kernel Meaning Meaning :=
  speaker 1 0 (geomPool (N δ) (L0 δ)) Measure.dirac

/-- The pragmatic listener (eq. (8)) inverts the channel composed with the speaker. -/
noncomputable abbrev L1 (δ : I) : Kernel Utterance Meaning :=
  listener μ (N δ ∘ₖ S1 δ)

variable {δ : I}

theorem N_apply_singleton (m : Meaning) (u : Utterance) :
    N δ m {u} = if u = .full m then (unitInterval.toNNReal (σ δ) : ℝ≥0∞) else
      if u = .subject m then (unitInterval.toNNReal δ : ℝ≥0∞) else 0 := by
  classical
  rw [N, Kernel.ofFunOfCountable_apply, bernoulliMeasure_apply _ (.singleton u)]
  rcases u with m' | m' <;> by_cases h : m' = m <;> simp [h, eq_comm]

-- Each meaning has one sentence, so the literal listener decodes the channel.
theorem L0_eq_listener : L0 δ = listener μ (N δ) := by
  refine congrArg (listener μ) (funext fun m ↦ ?_)
  rw [truthful, show {m' | m ∈ lit m'} = {m} by ext; simp [lit, eq_comm],
    Measure.restrict_singleton, Measure.count_singleton, one_smul, Measure.dirac_bind
    (Kernel.measurable _)]

private theorem listener_eq_dirac {κ : Kernel Meaning Utterance} {u : Utterance} {m : Meaning}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ w, κ w {u} = if w = m then c else 0) :
    listener μ κ u = Measure.dirac m := by
  have hmarg : (κ ∘ₘ μ) {u} = c := by
    rw [Measure.comp_apply_singleton]
    simp [h]
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [listener_apply_singleton_eq_div, hmarg, h, Measure.dirac_apply' _ (.singleton w)]
  by_cases hw : w = m
  · subst hw
    simp [ENNReal.div_self hc0 hc]
  · simp [hw, Ne.symm hw]

theorem L0_subject (hδ : 0 < δ) (m : Meaning) : L0 δ (.subject m) = Measure.dirac m := by
  rw [L0_eq_listener]
  refine listener_eq_dirac (c := unitInterval.toNNReal δ) ?_ ENNReal.coe_ne_top fun w ↦ ?_
  · simpa [← NNReal.coe_eq_zero] using hδ.ne'
  · by_cases h : w = m
    · simp [N_apply_singleton, h]
    · simp [N_apply_singleton, h, Ne.symm h]

-- Without noise a fragment is never perceived, so the literal listener has no reading for it.
theorem L0_subject_zero (m : Meaning) : L0 0 (.subject m) = 0 :=
  Measure.ext_of_singleton fun w ↦ by
    rw [L0_eq_listener, listener_apply_singleton_eq_zero (by simp [N_apply_singleton]),
      Measure.coe_zero, Pi.zero_apply]

theorem L0_full (hδ : δ < 1) (m : Meaning) : L0 δ (.full m) = Measure.dirac m := by
  rw [L0_eq_listener]
  refine listener_eq_dirac (c := unitInterval.toNNReal (σ δ)) ?_ ENNReal.coe_ne_top fun w ↦ ?_
  · simpa [← NNReal.coe_eq_zero, sub_eq_zero] using fun h ↦ hδ.ne (Subtype.ext h.symm)
  · by_cases h : w = m
    · simp [N_apply_singleton, h]
    · simp [N_apply_singleton, h, Ne.symm h]

section

variable (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
include hδ₀ hδ₁

-- Every perception of a sentence, whole or fragment, recovers its meaning.
theorem geomPool_N_L0 : geomPool (N δ) (L0 δ) = Measure.dirac := by
  funext m
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [geomPool_apply_singleton]
  refine Measure.geomMean_of_forall_eq fun u hu ↦ ?_
  rcases u with m' | m' <;> by_cases h : m' = m <;>
    simp_all [N_apply_singleton, L0_full hδ₁, L0_subject hδ₀]

-- The speaker utters the sentence for her meaning.
theorem S1_eq_id : S1 δ = Kernel.id := by
  ext1 w
  rw [S1, geomPool_N_L0 hδ₀ hδ₁, speaker_dirac_eq_ofWeights, Kernel.id_apply]
  refine Kernel.ofWeights_apply_eq_dirac one_ne_zero ENNReal.one_ne_top fun m ↦ ?_
  by_cases h : m = w
  · simp [h]
  · simp [h, Measure.dirac_apply']

theorem L1_eq_L0 : L1 δ = L0 δ := by
  rw [L1, S1_eq_id hδ₀ hδ₁, Kernel.comp_id, L0_eq_listener]

/-- The pragmatic listener reads a subject fragment as the meaning of the one sentence that deletes
to it, at every deletion rate strictly between zero and one. -/
theorem L1_subject (m : Meaning) : L1 δ (.subject m) = Measure.dirac m := by
  rw [L1_eq_L0 hδ₀ hδ₁, L0_subject hδ₀]

end

/-- `fragmentOf` reads a row's `fragment` feature as a subject fragment. -/
def fragmentOf (row : Datum) : Option Utterance :=
  match row.feature? "fragment" with
  | some "Alice" => some (.subject .aliceWent)
  | some "Bob" => some (.subject .bobWent)
  | some "Nobody" => some (.subject .nobodyWent)
  | _ => none

/-- `propositionOf` reads a row's `proposition` feature as a meaning. -/
def propositionOf (row : Datum) : Option Meaning :=
  match row.feature? "proposition" with
  | some "Alice went to the movies" => some .aliceWent
  | some "Bob went to the movies" => some .bobWent
  | some "Nobody went to the movies" => some .nobodyWent
  | _ => none

theorem model_matches_fragment_row (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ u m, fragmentOf Examples.fragment_answer = some u ∧
      propositionOf Examples.fragment_answer = some m ∧ L1 δ u = Measure.dirac m :=
  ⟨_, _, rfl, rfl, L1_subject hδ₀ hδ₁ _⟩

end Ellipsis

/-! ## Prosody

Stress lowers the rate at which a name is misheard as the other. A speaker who knows that only Bob
went must keep the listener from hearing "Alice went", so stress is worth more to her than to a
speaker who knows only that Bob went. -/

namespace Prosody

/-- Either one of Alice and Bob went alone, or both went. -/
inductive Meaning
  | onlyAlice
  | onlyBob
  | both
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Meaning := ⊤

/-- The subject sentences, stressed (capitals) or not, and the conjunction. -/
inductive Utterance
  | aliceWent
  | ALICE_went
  | bobWent
  | BOB_went
  | aliceAndBobWent
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

/-- Literal meanings are lower-bounded, so "Alice went" is true whenever Alice went. -/
def lit : Utterance → Set Meaning
  | .aliceWent | .ALICE_went => {.onlyAlice, .both}
  | .bobWent | .BOB_went => {.onlyBob, .both}
  | .aliceAndBobWent => {.both}

/-- A name is misheard as the other name, with its prosody. -/
def slip : Utterance → Utterance
  | .aliceWent => .bobWent
  | .bobWent => .aliceWent
  | .ALICE_went => .BOB_went
  | .BOB_went => .ALICE_went
  | .aliceAndBobWent => .aliceAndBobWent

/-- A name is misheard at rate `ε` without stress and `ε'` with it; the conjunction is safe. -/
def rate (ε ε' : I) : Utterance → I
  | .aliceWent | .bobWent => ε
  | .ALICE_went | .BOB_went => ε'
  | .aliceAndBobWent => 0

/-- The channel replaces the intended name by the other at its rate. -/
noncomputable def N (ε ε' : I) : Kernel Utterance Utterance :=
  Kernel.ofFunOfCountable fun u ↦ Ber(slip u, u, rate ε ε' u)

instance (ε ε' : I) : IsMarkovKernel (N ε ε') :=
  ⟨fun u ↦ by rw [N, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- The uniform prior over meanings. -/
noncomputable abbrev μ : Measure Meaning := Measure.count

/-- The literal listener (eq. (6)) inverts the channel composed with a truthful speaker. -/
noncomputable abbrev L0 (ε ε' : I) : Kernel Utterance Meaning :=
  listener μ fun m ↦ N ε ε' ∘ₘ truthful lit m

/-- What the speaker has observed: that only Bob went, or only that Bob went. -/
inductive Observation
  | onlyBob
  | bobAtLeast
  deriving DecidableEq, Fintype

instance : MeasurableSpace Observation := ⊤

/-- A speaker who observed that only Bob went is certain of it; one who observed only that Bob went
believes the two states in which he went equally likely. -/
noncomputable def belief : Observation → Measure Meaning
  | .onlyBob => Measure.dirac .onlyBob
  | .bobAtLeast => uniformOn ({.onlyBob, .both} : Finset Meaning)

/-- The speaker (eq. (7)), at the belief her observation gives her. -/
noncomputable abbrev S1 (ε ε' : I) : Kernel Observation Utterance :=
  speaker 1 0 (geomPool (N ε ε') (L0 ε ε')) belief

/-- The odds with which the speaker stresses "Bob". -/
noncomputable def stressOdds (ε ε' : I) (o : Observation) : ℝ :=
  (S1 ε ε' o).real {.BOB_went} / (S1 ε ε' o).real {.bobWent}

variable {ε ε' : I}

private theorem sum_univ_utt {β : Type*} [AddCommMonoid β] (f : Utterance → β) :
    ∑ u, f u = f .aliceWent + f .ALICE_went + f .bobWent + f .BOB_went + f .aliceAndBobWent := by
  rw [show (univ : Finset Utterance)
      = {.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp only [add_assoc]

@[to_additive]
private theorem prod_univ_mean {β : Type*} [CommMonoid β] (f : Meaning → β) :
    ∏ m, f m = f .onlyAlice * f .onlyBob * f .both := by
  rw [show (univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    prod_insert (by decide), prod_insert (by decide), prod_singleton]
  simp only [mul_assoc]

theorem N_apply_singleton (u v : Utterance) :
    N ε ε' u {v} = (if slip u = v then (unitInterval.toNNReal (rate ε ε' u) : ℝ≥0∞) else 0) +
      if u = v then (unitInterval.toNNReal (σ (rate ε ε' u)) : ℝ≥0∞) else 0 := by
  rw [N, Kernel.ofFunOfCountable_apply, bernoulliMeasure_def]
  simp [Measure.dirac_apply', Set.indicator_apply, eq_comm]

-- On each perception of a sentence about Bob, the literal listener's mass at the state in which
-- only Bob went is half the probability of that perception, and at the state in which both went
-- it is a half.
theorem L0_of_bob {u a : Utterance} (hu : u = .bobWent ∨ u = .BOB_went) (ha : N ε ε' u {a} ≠ 0) :
    L0 ε ε' a {.onlyBob} = 2⁻¹ * N ε ε' u {a} ∧ L0 ε ε' a {.both} = 2⁻¹ := by
  simp only [L0, listener_apply_singleton]
  rcases hu with rfl | rfl <;> cases a <;>
    simp_all [Measure.comp_apply_singleton, truthful_apply_singleton, sum_univ_utt, sum_univ_mean,
      N_apply_singleton, lit, slip, rate, one_add_one_eq_two, ENNReal.div_eq_inv_mul]

-- A speaker who knows that only Bob went weighs a sentence about Bob by half the exponential of
-- minus the entropy of its channel.
theorem geomPool_onlyBob {u : Utterance} (hu : u = .bobWent ∨ u = .BOB_went) :
    geomPool (N ε ε') (L0 ε ε') u {.onlyBob} =
      2⁻¹ * ENNReal.ofReal (exp (-binEntropy (rate ε ε' u))) := by
  have hslip : slip u ≠ u := by rcases hu with rfl | rfl <;> decide
  rw [geomPool_apply_singleton, Measure.geomMean_congr (g := fun a ↦ 2⁻¹ * N ε ε' u {a})
      fun a ha ↦ (L0_of_bob hu ha).1, Measure.geomMean_mul, Measure.geomMean_const,
    geomMean_eq_exp_neg_measureEntropy, N, Kernel.ofFunOfCountable_apply,
    measureEntropy_bernoulliMeasure hslip]

theorem geomPool_both {u : Utterance} (hu : u = .bobWent ∨ u = .BOB_went) :
    geomPool (N ε ε') (L0 ε ε') u {.both} = 2⁻¹ := by
  rw [geomPool_apply_singleton]
  exact Measure.geomMean_of_forall_eq fun a ha ↦ (L0_of_bob hu ha).2

theorem geomMean_belief_onlyBob (u : Utterance) :
    (belief .onlyBob).geomMean (fun w ↦ geomPool (N ε ε') (L0 ε ε') u {w}) =
      geomPool (N ε ε') (L0 ε ε') u {.onlyBob} := by
  rw [belief, Measure.geomMean_dirac]

theorem geomMean_belief_bobAtLeast {u : Utterance} (hu : u = .bobWent ∨ u = .BOB_went) :
    (belief .bobAtLeast).geomMean (fun w ↦ geomPool (N ε ε') (L0 ε ε') u {w}) =
      geomPool (N ε ε') (L0 ε ε') u {.onlyBob} ^ (2⁻¹ : ℝ) * 2⁻¹ ^ (2⁻¹ : ℝ) := by
  rw [belief, Measure.geomMean, prod_univ_mean, uniformOn_finset_real_singleton,
    uniformOn_finset_real_singleton, uniformOn_finset_real_singleton, geomPool_both hu]
  simp

private theorem geomPool_onlyBob_ne_zero {u : Utterance} (hu : u = .bobWent ∨ u = .BOB_went) :
    geomPool (N ε ε') (L0 ε ε') u {.onlyBob} ≠ 0 := by
  rw [geomPool_onlyBob hu]
  exact mul_ne_zero (by simp) (ENNReal.ofReal_pos.mpr (exp_pos _)).ne'

private theorem geomPool_bobWent_ne_zero (o : Observation) (w : Meaning) (hw : belief o {w} ≠ 0) :
    geomPool (N ε ε') (L0 ε ε') .bobWent {w} ≠ 0 := by
  cases w with
  | onlyAlice =>
    cases o with
    | onlyBob => simp [belief, Measure.dirac_apply'] at hw
    | bobAtLeast =>
      rw [belief, uniformOn_finset_apply_singleton] at hw
      simp at hw
  | onlyBob => exact geomPool_onlyBob_ne_zero (.inl rfl)
  | both => simp [geomPool_both (.inl rfl)]

theorem stressOdds_onlyBob :
    stressOdds ε ε' .onlyBob = exp (binEntropy ε - binEntropy ε') := by
  rw [stressOdds, S1, speaker_real_singleton_div zero_le_one (geomPool_bobWent_ne_zero _),
    geomMean_belief_onlyBob, geomMean_belief_onlyBob, geomPool_onlyBob (.inr rfl),
    geomPool_onlyBob (.inl rfl)]
  simp only [rate, rpow_one, Pi.zero_apply, sub_zero, mul_zero, neg_zero, exp_zero, mul_one,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le]
  rw [mul_div_mul_left _ _ (by simp), ← exp_sub]
  ring_nf

-- The odds with which a speaker who knows only that Bob went stresses "Bob" are the square root
-- of the odds of a speaker who knows that only Bob went.
theorem stressOdds_bobAtLeast :
    stressOdds ε ε' .bobAtLeast = √(stressOdds ε ε' .onlyBob) := by
  rw [stressOdds, stressOdds, S1, speaker_real_singleton_div zero_le_one
      (geomPool_bobWent_ne_zero _), speaker_real_singleton_div zero_le_one
      (geomPool_bobWent_ne_zero _), geomMean_belief_bobAtLeast (.inr rfl),
    geomMean_belief_bobAtLeast (.inl rfl), geomMean_belief_onlyBob, geomMean_belief_onlyBob]
  simp only [rpow_one, Pi.zero_apply, sub_zero, mul_zero, neg_zero, exp_zero, mul_one,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  rw [mul_div_mul_right _ _ (by simp), ← div_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    sqrt_eq_rpow, one_div]

private theorem binEntropy_lt (hε' : ε' < ε) (hε : (ε : ℝ) ≤ 2⁻¹) :
    binEntropy ε' < binEntropy ε :=
  binEntropy_strictMonoOn ⟨ε'.2.1, by linarith [Subtype.coe_lt_coe.mpr hε']⟩ ⟨ε.2.1, hε⟩
    (Subtype.coe_lt_coe.mpr hε')

/-- A speaker who knows that only Bob went prefers "BOB went" to "Bob went", at any stressed rate
below an unstressed rate of at most a half. -/
theorem S1_bobWent_lt_BOB_went (hε' : ε' < ε) (hε : (ε : ℝ) ≤ 2⁻¹) :
    (S1 ε ε' .onlyBob).real {.bobWent} < (S1 ε ε' .onlyBob).real {.BOB_went} := by
  have hpos : 0 < (S1 ε ε' .onlyBob).real {.bobWent} :=
    ENNReal.toReal_pos (speaker_apply_singleton_ne_zero zero_le_one (geomPool_bobWent_ne_zero _))
      (measure_ne_top _ _)
  rw [← one_lt_div hpos, ← stressOdds, stressOdds_onlyBob, one_lt_exp_iff, sub_pos]
  exact binEntropy_lt hε' hε

/-- A speaker who knows only that Bob went is less likely to stress "Bob" than one who knows that
only Bob went. -/
theorem stressOdds_bobAtLeast_lt_onlyBob (hε' : ε' < ε) (hε : (ε : ℝ) ≤ 2⁻¹) :
    stressOdds ε ε' .bobAtLeast < stressOdds ε ε' .onlyBob := by
  rw [stressOdds_bobAtLeast, stressOdds_onlyBob, ← exp_half, exp_lt_exp]
  linarith [binEntropy_lt hε' hε]

/-- `uttOf` reads a row's `stress` feature as a sentence about Bob. -/
def uttOf (row : Datum) : Option Utterance :=
  match row.feature? "stress" with
  | some "subject" => some .BOB_went
  | some "none" => some .bobWent
  | _ => none

/-- `observationOf` reads a row's `reading` feature as what the speaker has observed. -/
def observationOf (row : Datum) : Option Observation :=
  match row.feature? "reading" with
  | some "exhaustive" => some .onlyBob
  | some "nonExhaustive" => some .bobAtLeast
  | _ => none

-- At the paper's rate of 1%, halved by stress, the speaker whose knowledge the stressed row's
-- reading attributes prefers the stressed form, and more strongly than the speaker of the
-- unstressed row's reading.
theorem model_matches_stress_rows :
    ∃ u_s u_u o_s o_u, uttOf Examples.stressed_subject = some u_s ∧
      uttOf Examples.unstressed_subject = some u_u ∧
      observationOf Examples.stressed_subject = some o_s ∧
      observationOf Examples.unstressed_subject = some o_u ∧
      let ε : I := ⟨1 / 100, by norm_num, by norm_num⟩
      let ε' : I := ⟨1 / 200, by norm_num, by norm_num⟩
      (S1 ε ε' o_s).real {u_u} < (S1 ε ε' o_s).real {u_s} ∧
        (S1 ε ε' o_u).real {u_s} / (S1 ε ε' o_u).real {u_u} <
          (S1 ε ε' o_s).real {u_s} / (S1 ε ε' o_s).real {u_u} :=
  have hε' : (⟨1 / 200, by norm_num, by norm_num⟩ : I) < ⟨1 / 100, by norm_num, by norm_num⟩ :=
    Subtype.mk_lt_mk.mpr (by norm_num)
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, S1_bobWent_lt_BOB_went hε' (by norm_num),
    stressOdds_bobAtLeast_lt_onlyBob hε' (by norm_num)⟩

end Prosody

end BergenGoodman2015
