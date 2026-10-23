module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Data.Examples.BergenGoodman2015

/-!
# Bergen & Goodman (2015): The strategic use of noise in pragmatic reasoning

This file formalizes Bergen and Goodman's two applications of rational speech acts over a noisy
channel from the speaker's intended utterances to the perceived ones: the literal listener decodes
the intended utterance before interpreting it (eq. 6), the speaker's utility is the channel-expected
log posterior of the intended meaning (eq. 7), and the pragmatic listener inverts the speaker
composed with the channel (eq. 8). The channel misperceives each utterance as at most one other, at
a rate the speaker lowers by stressing a word (`slipChannel`). Sentence fragments have no literal
meaning, yet both listeners read the fragment "Bob" as the point mass on Bob having gone, at every
positive deletion rate (`Ellipsis.L0_subject`, `Ellipsis.L1_subject`), because only "Bob went to the
movies" deletes to it. Stress halves the rate at which a subject is misheard as the other, so the
exponentiated utility of a subject sentence is `exp (-binEntropy rate) / 2`, and a speaker who knows
that only Bob went prefers "BOB went" to "Bob went" (`Prosody.S1_bobWent_lt_BOB_went`), the form the
paper's exhaustive row records (`Prosody.model_matches_stress_rows`).

## Main results

* `Ellipsis.L0_subject`, `Ellipsis.L1_subject` — a subject fragment is the point mass on its
  source, for every positive deletion rate; `Ellipsis.S1_apply` — the speaker utters the full
  sentence.
* `Prosody.channelMix_eq_exp_neg_binEntropy` — a subject sentence's exponentiated utility is
  `exp (-binEntropy rate) / 2`.
* `Prosody.S1_bobWent_lt_BOB_went` — the knowledgeable speaker prefers the stressed form.

## Implementation notes

Priors are unit weights, the rationality parameter is `1`, and costs are zero. The channel runs from
the speaker's intended utterances to the perceived ones: for ellipsis the intended utterances are
the three full sentences (the paper's simplification), for prosody all five forms. Prosody is
perceived, so the stressed and unstressed forms are two copies of the subject-confusion channel at
rates `ε / 2` and `ε`. The prosody speaker is the paper's knowledgeable one, for whom the divergence
utility is eq. 7.

## TODO

* Fragment production (Fig. 1, right) needs utterance costs; the ignorant speaker's lower
  stress rate (Fig. 2, right) needs the divergence utility over observations.
* The listener's exhaustive reading of stress (Fig. 2, left) is the paper's depth-two result
  over knowledge states; at depth one it reduces to the monotonicity in the rate of the
  confusion odds `(r ^ (1 - r) * (1 - r) ^ r) / ((1 - r) ^ (1 - r) * r ^ r)`, not yet proved.

## References

* [bergen-goodman-2015]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Finset Real
open scoped ENNReal

namespace BergenGoodman2015

/-! ### The slip channel -/

section Channel

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]

/-- Under the channel of a slip rate and a slip target, an intended utterance is perceived
intact with probability `1 - rate u` and as `slip u` with probability `rate u`. -/
noncomputable def slipChannel (rate : U → ℝ) (slip : U → U) : Kernel U U :=
  Kernel.ofFunOfCountable fun u =>
    ENNReal.ofReal (1 - rate u) • Measure.dirac u + ENNReal.ofReal (rate u) • Measure.dirac (slip u)

instance (rate : U → ℝ) (slip : U → U) : IsFiniteKernel (slipChannel rate slip) :=
  ⟨⟨∑ u, (ENNReal.ofReal (1 - rate u) + ENNReal.ofReal (rate u)),
    ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.ofReal_lt_top⟩,
    fun u => by
      rw [slipChannel, Kernel.ofFunOfCountable_apply, Measure.add_apply, Measure.smul_apply,
        Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _),
        Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one, mul_one]
      exact single_le_sum (f := fun u => ENNReal.ofReal (1 - rate u) + ENNReal.ofReal (rate u))
        (fun _ _ => zero_le) (mem_univ u)⟩⟩

theorem slipChannel_apply_singleton [DecidableEq U] (rate : U → ℝ) (slip : U → U) (u v : U) :
    slipChannel rate slip u {v} = ENNReal.ofReal (1 - rate u) * (if u = v then 1 else 0) +
      ENNReal.ofReal (rate u) * (if slip u = v then 1 else 0) := by
  rw [slipChannel, Kernel.ofFunOfCountable_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (.singleton v),
    Measure.dirac_apply' _ (.singleton v)]
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]

end Channel

/-! ### Rational speech acts over the channel

The literal listener decodes before interpreting, so the meaning of a perceived utterance is the
meaning of each intended one weighted by the utterance prior and the channel (eq. 6). The
speaker's informativity is the channel-expected log listener, whose exponential is the listener
mass averaged geometrically over perceptions (`channelMix`), and the speaker is the power-weight
best response to that mix (`noisySpeaker`, eqs. 4 and 7). The pragmatic listener inverts the
speaker composed with the channel (eq. 8). At the identity channel each operator is its
noiseless counterpart. -/

section NoisyRSA

variable {W I U : Type*} [MeasurableSpace I] [MeasurableSpace U]

section Meaning

/-- The meaning of a perceived utterance `u_p` is the meaning of each intended utterance,
weighted by the utterance prior and the channel (eq. 6). -/
noncomputable def noisyMeaning (N : Kernel I U) (ρ : Measure I) (m : I → W → ℝ≥0∞) (u_p : U)
    (w : W) : ℝ≥0∞ :=
  ∫⁻ u_i, N u_i {u_p} * m u_i w ∂ρ

variable [Fintype I] [MeasurableSingletonClass I]

theorem noisyMeaning_apply (N : Kernel I U) (ρ : Measure I) (m : I → W → ℝ≥0∞) (u_p : U)
    (w : W) : noisyMeaning N ρ m u_p w = ∑ u_i, N u_i {u_p} * m u_i w * ρ {u_i} :=
  lintegral_fintype _

variable [Fintype U] [MeasurableSingletonClass U]

theorem noisyMeaning_id (ρ : Measure U) (m : U → W → ℝ≥0∞) (u : U) (w : W) :
    noisyMeaning Kernel.id ρ m u w = ρ {u} * m u w := by
  rw [noisyMeaning_apply, sum_eq_single u]
  · rw [Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton u), one_mul, mul_comm]
  · intro v _ hv
    rw [Kernel.id_apply, Measure.dirac_apply' _ (.singleton u),
      Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr hv), zero_mul, zero_mul]
  · exact fun h => absurd (mem_univ u) h

end Meaning

variable [MeasurableSpace W] [Fintype U]

section Speaker

/-- `channelMix N L u_i w` averages the listener mass at `w` geometrically over the
perceptions of `u_i`; it is the exponential of the channel-expected log listener, eq. 7's
informativity. -/
noncomputable def channelMix (N : Kernel I U) (L : Kernel U W) (u_i : I) (w : W) : ℝ≥0∞ :=
  ∏ u_p, L u_p {w} ^ (N u_i {u_p}).toReal

theorem channelMix_eq_prod (N : Kernel I U) (L : Kernel U W) {u_i : I} {s : Finset U}
    (hs : ∀ u_p ∉ s, N u_i {u_p} = 0) (w : W) :
    channelMix N L u_i w = ∏ u_p ∈ s, L u_p {w} ^ (N u_i {u_p}).toReal :=
  (prod_subset (subset_univ s) fun u_p _ hu => by
    rw [hs u_p hu, ENNReal.toReal_zero, ENNReal.rpow_zero]).symm

theorem channelMix_ne_top (N : Kernel I U) (L : Kernel U W) [IsFiniteKernel L] (u_i : I)
    (w : W) : channelMix N L u_i w ≠ ∞ :=
  ENNReal.prod_ne_top fun _ _ => ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (measure_ne_top _ _)

section

variable [Fintype I] [MeasurableSingletonClass I] [Fintype W] [MeasurableSingletonClass W]

/-- The speaker over the channel (eqs. 4 and 7) weights each utterance by the channel-mixed
listener to the power `α`, scaled by the cost weight `exp (-(α * C u))`. -/
noncomputable def noisySpeaker (N : Kernel I U) (α : ℝ) (C : I → ℝ) (L : Kernel U W) :
    Kernel W I :=
  Kernel.ofWeights fun w u => channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))

@[simp] theorem noisySpeaker_apply_singleton (N : Kernel I U) (α : ℝ) (C : I → ℝ)
    (L : Kernel U W) (w : W) (u : I) :
    noisySpeaker N α C L w {u} =
      channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        / ∑ u', channelMix N L u' w ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_apply_singleton _ w u

instance (N : Kernel I U) (α : ℝ) (C : I → ℝ) (L : Kernel U W) :
    IsFiniteKernel (noisySpeaker N α C L) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- Row preference of the speaker reduces to comparing the weighted channel-mixed listener
values; the normalization cancels. -/
theorem noisySpeaker_real_singleton_lt_iff {N : Kernel I U} {α : ℝ} (hα : 0 ≤ α) {C : I → ℝ}
    {L : Kernel U W} [IsFiniteKernel L] {w : W}
    (h0 : ∃ u, channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) ≠ 0) {u u' : I} :
    (noisySpeaker N α C L w).real {u} < (noisySpeaker N α C L w).real {u'} ↔
      channelMix N L u w ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        < channelMix N L u' w ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_real_singleton_lt_iff w
    (fun h => let ⟨u₀, hu₀⟩ := h0; hu₀ (sum_eq_zero_iff.mp h u₀ (mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun u _ => ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hα (channelMix_ne_top N L u w)) ENNReal.ofReal_ne_top)

end

variable [MeasurableSingletonClass U]

theorem ofDensity_noisyMeaning_id (μ : Measure W) (ρ : Measure U) (m : U → W → ℝ≥0∞)
    {u : U} (h0 : ρ {u} ≠ 0) (htop : ρ {u} ≠ ∞) :
    Kernel.ofDensity μ (noisyMeaning Kernel.id ρ m) u = Kernel.ofDensity μ m u :=
  Kernel.ofDensity_apply_eq_of_eq_mul μ h0 htop (noisyMeaning_id ρ m u)

theorem channelMix_id (L : Kernel U W) (u : U) (w : W) : channelMix Kernel.id L u w = L u {w} := by
  rw [channelMix_eq_prod _ _ (s := {u}) fun v hv => by
      rw [Kernel.id_apply, Measure.dirac_apply' _ (.singleton v),
        Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr fun h => hv (by simp [h]))],
    prod_singleton, Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton u),
    ENNReal.toReal_one, ENNReal.rpow_one]

variable [Fintype W] [MeasurableSingletonClass W]

theorem noisySpeaker_id (α : ℝ) (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L] :
    noisySpeaker Kernel.id α C L = speaker α C L Measure.dirac := by
  rw [speaker_dirac_eq_ofWeights]
  unfold noisySpeaker
  congr 1
  funext w u
  rw [channelMix_id]

end Speaker

section Listener

variable [MeasurableSingletonClass U] [Fintype W] [MeasurableSingletonClass W]

theorem listener_id_comp_noisySpeaker (α : ℝ) (C : U → ℝ) (L : Kernel U W)
    [IsFiniteKernel L] (μ : Measure W) :
    listener μ (Kernel.id ∘ₖ noisySpeaker Kernel.id α C L) =
      listener μ (speaker α C L Measure.dirac) := by
  rw [Kernel.id_comp, noisySpeaker_id]

end Listener

end NoisyRSA

/-! ## Ellipsis

Three meanings and the full sentences expressing them; deletion strikes the predicate, leaving a
subject fragment with no literal meaning. -/

namespace Ellipsis

/-- Who went to the movies. -/
inductive Meaning
  | aliceWent
  | bobWent
  | nobodyWent
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Meaning := ⊤

/-- The utterances are the full sentences and the fragments deletion leaves, a subject alone
or the predicate. -/
inductive Utterance
  | full (m : Meaning)
  | subject (m : Meaning)
  | predicate
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

/-- Full sentences mean what they say; fragments have no literal meaning. -/
def lit : Utterance → Set Meaning
  | .full m => {m}
  | _ => ∅

/-- Deletion strikes the predicate of a full sentence at rate `δ`. -/
noncomputable def rate (δ : ℝ) : Utterance → ℝ
  | .full _ => δ
  | _ => 0

/-- Deleting the predicate leaves the subject. -/
def slip : Utterance → Utterance
  | .full m => .subject m
  | u => u

/-- The deletion channel at rate `δ`, from the speaker's full sentences, indexed by the meaning
they express, to the perceived utterances. -/
noncomputable abbrev N (δ : ℝ) : Kernel Meaning Utterance :=
  (slipChannel (rate δ) slip).comap Utterance.full (measurable_of_countable _)

/-- The speaker's full sentences are equally likely. -/
noncomputable abbrev uttPrior : Measure Meaning := Measure.count

/-- The uniform meaning prior. -/
noncomputable abbrev μ : Measure Meaning := Measure.count

/-- The graded literal meaning of a full sentence. -/
noncomputable abbrev lit' : Meaning → Meaning → ℝ≥0∞ := fun m => (lit (.full m)).indicator 1

/-- The literal listener (eq. 6). -/
noncomputable abbrev L0 (δ : ℝ) : Kernel Utterance Meaning :=
  Kernel.ofDensity μ (noisyMeaning (N δ) uttPrior lit')

/-- The speaker (eq. 7), choosing among the full sentences. -/
noncomputable abbrev S1 (δ : ℝ) : Kernel Meaning Meaning := noisySpeaker (N δ) 1 0 (L0 δ)

/-- The pragmatic listener (eq. 8). -/
noncomputable abbrev L1 (δ : ℝ) : Kernel Utterance Meaning :=
  listener μ (N δ ∘ₖ S1 δ)

variable {δ : ℝ} (m : Meaning)

theorem noisyMeaning_subject (w : Meaning) :
    noisyMeaning (N δ) uttPrior lit' (.subject m) w =
      ENNReal.ofReal δ * ({m} : Set Meaning).indicator 1 w := by
  rw [noisyMeaning_apply, sum_eq_single m]
  · simp [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip, lit', lit]
  · intro m' _ h
    simp [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip, lit', lit, h]
  · exact fun h => absurd (mem_univ _) h

theorem noisyMeaning_full (w : Meaning) :
    noisyMeaning (N δ) uttPrior lit' (.full m) w =
      ENNReal.ofReal (1 - δ) * ({m} : Set Meaning).indicator 1 w := by
  rw [noisyMeaning_apply, sum_eq_single m]
  · simp [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip, lit', lit]
  · intro m' _ h
    simp [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip, lit', lit, h]
  · exact fun h => absurd (mem_univ _) h

private theorem L0_of_noisyMeaning {c : ℝ} (hc : 0 < c) {u : Utterance}
    (h : ∀ w, noisyMeaning (N δ) uttPrior lit' u w =
      ENNReal.ofReal c * ({m} : Set Meaning).indicator 1 w) :
    L0 δ u = Measure.dirac m := by
  rw [L0, Kernel.ofDensity_apply_eq_of_eq_mul μ (f := fun _ ↦ ({m} : Set Meaning).indicator 1)
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top h, ← listener_truthful_eq_ofDensity]
  refine Measure.ext_of_singleton fun w => ?_
  simp only [Measure.dirac_apply' _ (.singleton w), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply]
  by_cases hw : m = w
  · subst hw
    rw [listener_truthful_apply_singleton_of_eq_singleton μ (fun _ => {m}) rfl (by simp)]
    simp
  · rw [listener_truthful_apply_singleton_of_notMem μ (fun _ => {m})
      (by simpa using Ne.symm hw)]
    simp [hw]

/-- A subject fragment is the point mass on the meaning whose full sentence deletes to it, at
every positive deletion rate. -/
theorem L0_subject (hδ : 0 < δ) : L0 δ (.subject m) = Measure.dirac m :=
  L0_of_noisyMeaning m hδ (noisyMeaning_subject m)

theorem L0_full (hδ : δ < 1) : L0 δ (.full m) = Measure.dirac m :=
  L0_of_noisyMeaning m (by linarith) (noisyMeaning_full m)

variable (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
include hδ₀ hδ₁

theorem channelMix_full (m' : Meaning) :
    channelMix (N δ) (L0 δ) m' m = if m' = m then 1 else 0 := by
  rw [channelMix_eq_prod _ _ (s := {.full m', .subject m'}) fun u hu => by
      rcases u with m'' | m'' | _ <;>
        simp_all [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip] <;>
        exact fun h => absurd h.symm hu,
    prod_pair (by simp), L0_full m' hδ₁, L0_subject m' hδ₀]
  have h1 : (ENNReal.ofReal (1 - δ)).toReal = 1 - δ := ENNReal.toReal_ofReal (by linarith)
  have h2 : (ENNReal.ofReal δ).toReal = δ := ENNReal.toReal_ofReal hδ₀.le
  simp only [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip, ite_true, mul_one,
    Measure.dirac_apply' _ (.singleton m), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply]
  by_cases h : m' = m
  · simp [h]
  · simp [h, h1, h2, hδ₀, sub_pos.mpr hδ₁]

/-- The speaker utters the full sentence for its meaning. -/
theorem S1_apply : S1 δ m = Measure.dirac m := by
  refine Kernel.ofWeights_apply_eq_dirac one_ne_zero ENNReal.one_ne_top fun m' => ?_
  rw [channelMix_full m hδ₀ hδ₁, ENNReal.rpow_one]
  simp [eq_comm]

theorem comp_apply_subject (w : Meaning) :
    (N δ ∘ₖ S1 δ) w {.subject m} = if w = m then ENNReal.ofReal δ else 0 := by
  rw [Kernel.comp_apply_singleton, sum_eq_single w]
  · rw [S1_apply w hδ₀ hδ₁, Measure.dirac_apply_of_mem (Set.mem_singleton _), one_mul]
    by_cases h : w = m
    · subst h; simp [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip]
    · simp [Kernel.comap_apply, slipChannel_apply_singleton, rate, slip, h]
  · intro u _ hu
    rw [S1_apply w hδ₀ hδ₁, Measure.dirac_apply' _ (.singleton u),
      Set.indicator_of_notMem (by simpa using Ne.symm hu), zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- The pragmatic listener also reads a subject fragment as the point mass on its source. -/
theorem L1_subject : L1 δ (.subject m) = Measure.dirac m := by
  have hmarg : ((N δ ∘ₖ S1 δ) ∘ₘ μ) {.subject m} = ENNReal.ofReal δ := by
    rw [Measure.comp_apply_singleton]
    simp [comp_apply_subject m hδ₀ hδ₁]
  refine Measure.ext_of_singleton fun w => ?_
  rw [listener_apply_singleton_eq_div, hmarg, comp_apply_subject m hδ₀ hδ₁]
  simp only [Measure.dirac_apply' _ (.singleton w), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply]
  by_cases h : w = m
  · subst h
    simp [ENNReal.div_self (ENNReal.ofReal_pos.mpr hδ₀).ne' ENNReal.ofReal_ne_top]
  · simp [h, Ne.symm h]

end Ellipsis

/-! ## Prosody

Stress halves the rate at which a subject is misheard as the other (the paper's `ε / n` at
`n = 2`); the conjunction is never misheard. A speaker who knows that only Bob went must keep
the listener from hearing "Alice went", so stress is worth more to them. -/

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

/-- Subjects are confused at rate `ε`, halved under stress; the conjunction is safe. -/
noncomputable def rate (ε : ℝ) : Utterance → ℝ
  | .aliceWent | .bobWent => ε
  | .ALICE_went | .BOB_went => ε / 2
  | .aliceAndBobWent => 0

/-- A subject is misheard as the other subject, with its prosody. -/
def slip : Utterance → Utterance
  | .aliceWent => .bobWent
  | .bobWent => .aliceWent
  | .ALICE_went => .BOB_went
  | .BOB_went => .ALICE_went
  | .aliceAndBobWent => .aliceAndBobWent

/-- The subject-confusion channel at rate `ε`. -/
noncomputable abbrev N (ε : ℝ) : Kernel Utterance Utterance := slipChannel (rate ε) slip

/-- The uniform utterance prior. -/
noncomputable abbrev uttPrior : Measure Utterance := Measure.count

/-- The uniform meaning prior. -/
noncomputable abbrev μ : Measure Meaning := Measure.count

/-- The graded literal meaning. -/
noncomputable abbrev lit' : Utterance → Meaning → ℝ≥0∞ := fun u => (lit u).indicator 1

/-- The literal listener (eq. 6). -/
noncomputable abbrev L0 (ε : ℝ) : Kernel Utterance Meaning :=
  Kernel.ofDensity μ (noisyMeaning (N ε) uttPrior lit')

/-- The knowledgeable speaker (eq. 7), over all five forms. -/
noncomputable abbrev S1 (ε : ℝ) : Kernel Meaning Utterance :=
  noisySpeaker (N ε) 1 0 (L0 ε)

variable {ε : ℝ}

private theorem sum_univ_utt {β : Type*} [AddCommMonoid β] (f : Utterance → β) :
    ∑ u, f u = f .aliceWent + f .ALICE_went + f .bobWent + f .BOB_went + f .aliceAndBobWent := by
  rw [show (univ : Finset Utterance)
      = {.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp only [add_assoc]

private theorem sum_univ_mean {β : Type*} [AddCommMonoid β] (f : Meaning → β) :
    ∑ m, f m = f .onlyAlice + f .onlyBob + f .both := by
  rw [show (univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [add_assoc]

private theorem L0_onlyBob (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    L0 ε .bobWent {.onlyBob} = ENNReal.ofReal ((1 - ε) / 2) ∧
    L0 ε .aliceWent {.onlyBob} = ENNReal.ofReal (ε / 2) ∧
    L0 ε .BOB_went {.onlyBob} = ENNReal.ofReal ((1 - ε / 2) / 2) ∧
    L0 ε .ALICE_went {.onlyBob} = ENNReal.ofReal (ε / 2 / 2) := by
  have h1 : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hε₀, sub_add_cancel, ENNReal.ofReal_one]
  have h2 : ENNReal.ofReal (1 - ε / 2) + ENNReal.ofReal (ε / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), sub_add_cancel, ENNReal.ofReal_one]
  have h1' := (add_comm _ _).trans h1
  have h2' := (add_comm _ _).trans h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [L0, Kernel.ofDensity_apply_singleton]
      simp only [noisyMeaning_apply, sum_univ_utt, sum_univ_mean, slipChannel_apply_singleton,
        rate, slip, lit', lit, Measure.count_singleton, Pi.one_apply,
        Set.indicator_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
      simp only [reduceCtorEq, ite_true, ite_false, or_false, false_or, mul_one, mul_zero,
        add_zero, zero_add, h1, h1', h2, h2', one_add_one_eq_two]
      simp only [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The exponentiated utility of a subject sentence at slip rate `r` for its unique true meaning is
`exp (-binEntropy r) / 2` (eq. 7). -/
theorem rpow_mul_rpow_eq_exp_neg_binEntropy {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ((1 - r) / 2) ^ (1 - r) * (r / 2) ^ r = exp (-binEntropy r) / 2 := by
  rw [rpow_def_of_pos (div_pos (by linarith) two_pos), rpow_def_of_pos (div_pos hr₀ two_pos),
    ← exp_add, log_div (sub_ne_zero.mpr hr₁.ne') two_ne_zero, log_div hr₀.ne' two_ne_zero,
    show exp (-binEntropy r) / 2 = exp (-binEntropy r - log 2) by
      rw [exp_sub, exp_log two_pos],
    binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
  congr 1; ring

/-- The knowledgeable speaker's channel-mixed listener for the two forms of "Bob went" is the
entropy form of their rates. -/
theorem channelMix_eq_exp_neg_binEntropy (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    channelMix (N ε) (L0 ε) .bobWent .onlyBob = ENNReal.ofReal (exp (-binEntropy ε) / 2) ∧
    channelMix (N ε) (L0 ε) .BOB_went .onlyBob =
      ENNReal.ofReal (exp (-binEntropy (ε / 2)) / 2) := by
  obtain ⟨hb, ha, hB, hA⟩ := L0_onlyBob hε₀.le hε₁.le
  refine ⟨?_, ?_⟩
  · rw [channelMix_eq_prod _ _ (s := {.bobWent, .aliceWent}) fun u hu => by
        rcases u <;> simp_all [slipChannel_apply_singleton, rate, slip],
      prod_pair (by decide), hb, ha]
    simp only [slipChannel_apply_singleton, rate, slip, ite_true, ite_false, mul_one, mul_zero,
      add_zero, zero_add, reduceCtorEq]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε₀.le,
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by linarith) hε₀.le,
      ← ENNReal.ofReal_mul (rpow_nonneg (by linarith) _),
      rpow_mul_rpow_eq_exp_neg_binEntropy hε₀ hε₁]
  · rw [channelMix_eq_prod _ _ (s := {.BOB_went, .ALICE_went}) fun u hu => by
        rcases u <;> simp_all [slipChannel_apply_singleton, rate, slip],
      prod_pair (by decide), hB, hA]
    simp only [slipChannel_apply_singleton, rate, slip, ite_true, ite_false, mul_one, mul_zero,
      add_zero, zero_add, reduceCtorEq]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ← ENNReal.ofReal_mul (rpow_nonneg (by linarith) _),
      rpow_mul_rpow_eq_exp_neg_binEntropy (half_pos hε₀) (by linarith)]

/-- A speaker who knows only Bob went prefers *BOB went* to *Bob went* (Fig. 2). -/
theorem S1_bobWent_lt_BOB_went (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) :
    (S1 ε .onlyBob).real {.bobWent} < (S1 ε .onlyBob).real {.BOB_went} := by
  obtain ⟨hb, hB⟩ := channelMix_eq_exp_neg_binEntropy hε₀ (by linarith)
  rw [S1, noisySpeaker_real_singleton_lt_iff zero_le_one
      ⟨.BOB_went, by simpa [hB] using (ENNReal.ofReal_pos.mpr (by positivity)).ne'⟩]
  simp only [ENNReal.rpow_one, Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one, mul_one]
  rw [hb, hB, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  refine div_lt_div_of_pos_right (exp_lt_exp.2 (neg_lt_neg ?_)) two_pos
  exact binEntropy_strictMonoOn ⟨by linarith, by norm_num; linarith⟩
    ⟨hε₀.le, by norm_num; linarith⟩ (by linarith)

/-- `uttOf` reads a row's `stress` feature as an utterance. -/
def uttOf (row : Datum) : Option Utterance :=
  match row.feature? "stress" with
  | some "subject" => some .BOB_went
  | some "none"    => some .bobWent
  | _              => none

/-- A speaker with the exhaustive meaning prefers the stressed row's form to the unstressed
row's, at the paper's rate. -/
theorem model_matches_stress_rows :
    ∃ u_s u_u, uttOf Examples.stressed_subject = some u_s ∧
      uttOf Examples.unstressed_subject = some u_u ∧
      (S1 (1 / 100) .onlyBob).real {u_u} < (S1 (1 / 100) .onlyBob).real {u_s} :=
  ⟨_, _, rfl, rfl, S1_bobWent_lt_BOB_went (by norm_num) (by norm_num)⟩

end Prosody

end BergenGoodman2015
