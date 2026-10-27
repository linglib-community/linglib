module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Probability.UniformOn

/-!
# Yoon, Tessler, Goodman and Frank (2020): Polite Speech Emerges From Competing Social Goals

This file formalizes [yoon-etal-2020]'s Rational Speech Act model of polite speech, in which a
speaker trades off three goals: to be informative, to be kind, and to appear informative and
kind. In the experimental domain Ann rates Bob's poem on a scale of zero to three hearts and
answers with one of four adjectives, plain or negated. The literal listener updates a uniform
prior over states with the soft lexicon elicited in the norming experiment (`meaning`, `l0`);
the first-order speaker maximizes a mixture of informational and social utility minus cost,
`φ · ln P_L0(s | w) + (1 − φ) · E_L0[V(s)] − C(w)`, (5) (`util`, `speaker`); the pragmatic
listener infers the state and the speaker's goal weight jointly, (4) (`listener`); and the
second-order polite speaker adds presentational utility, the log probability the pragmatic
listener assigns to the projected goal weight, (3), inside the total utility (2)
(`s2Utility`, `s2Speaker`, (1)).

The first-order predictions of Figure 2 are theorems over the free parameters. A speaker with
no weight on informativity prefers "not terrible" to "terrible" exactly when the extra cost of
negation is below its social gain (`social_prefers_indirect_iff`), and prefers "amazing" to
"not amazing" at every cost (`social_prefers_positive`); a speaker with no weight on kindness
prefers the direct form at both ends of the scale (`informative_prefers_direct`,
`informative_prefers_direct_positive`), and never produces an utterance whose literal
probability at the true state is zero (`speaker_apply_eq_zero_of_meaning_eq_zero`).

## Implementation notes

* The lexicon is the acceptance count of each utterance at each state among the 49
  participants in the released norming data (`acceptance`); the paper's Bayesian data analysis
  places a Beta posterior on each acceptance probability instead. An utterance with zero
  acceptance at a state has literal probability zero there, and its score is `⊥` for every
  speaker with some weight on informativity, since the pure-social speaker alone ignores the
  literal probability.
* The listener's prior over the goal weight `φ` is uniform on the unit interval; it is
  discretized to five points (`Phi`) so that the joint prior is `uniformOn`.
* Cost is the paper's cost of negation `c` (Figure 4): a plain utterance costs 1 and a negated
  one `c`, and it sits inside the utility scaled by `α` as in (2); the released model realizes
  it as an utterance prior instead.
* Table 2's maximum a posteriori goal weights for the full model are recorded as data
  (`tableTwo`); the model comparison of Table 1 is outside the scope of the formalization.

## References

* [yoon-etal-2020]
-/

@[expose] public section

namespace YoonEtAl2020

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### States, utterances, goals -/

/-- The rating a poem deserves, in hearts. -/
inductive HeartState
  | h0 | h1 | h2 | h3
  deriving DecidableEq, Repr, Fintype, Inhabited

instance : MeasurableSpace HeartState := ⊤

/-- The subjective value `V(s)` of a state, the number of hearts. -/
def HeartState.value : HeartState → ℚ
  | .h0 => 0
  | .h1 => 1
  | .h2 => 2
  | .h3 => 3

/-- The four adjectives. -/
inductive Adjective
  | terrible | bad | good | amazing
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Adjective := ⊤

/-- An utterance is an adjective, plain or negated, as in *it was X* or *it wasn't X*. -/
abbrev Utterance := Adjective × Bool

/-- The speaker's goal condition in the production experiment. -/
inductive GoalCondition
  | informative | kind | both
  deriving DecidableEq, Repr

/-- The first-order speaker's goal weight `φ`, the weight on informativity against kindness,
discretized to five points. -/
inductive Phi
  | p0 | p25 | p50 | p75 | p100
  deriving DecidableEq, Repr, Fintype, Inhabited

instance : MeasurableSpace Phi := ⊤

/-- The value of each goal weight. -/
def Phi.val : Phi → ℚ
  | .p0 => 0
  | .p25 => 1/4
  | .p50 => 1/2
  | .p75 => 3/4
  | .p100 => 1

/-! ### The soft lexicon -/

/-- The number of the 49 norming participants who accepted the utterance at the state
(Figure 2, top left), from the released norming data. -/
def acceptance : Adjective → Bool → HeartState → ℕ
  | .terrible, false, .h0 => 49
  | .terrible, false, .h1 => 26
  | .terrible, false, .h2 => 0
  | .terrible, false, .h3 => 1
  | .terrible, true, .h0 => 2
  | .terrible, true, .h1 => 22
  | .terrible, true, .h2 => 44
  | .terrible, true, .h3 => 43
  | .bad, false, .h0 => 49
  | .bad, false, .h1 => 45
  | .bad, false, .h2 => 0
  | .bad, false, .h3 => 0
  | .bad, true, .h0 => 3
  | .bad, true, .h1 => 7
  | .bad, true, .h2 => 47
  | .bad, true, .h3 => 44
  | .good, false, .h0 => 1
  | .good, false, .h1 => 2
  | .good, false, .h2 => 47
  | .good, false, .h3 => 49
  | .good, true, .h0 => 48
  | .good, true, .h1 => 46
  | .good, true, .h2 => 2
  | .good, true, .h3 => 1
  | .amazing, false, .h0 => 1
  | .amazing, false, .h1 => 1
  | .amazing, false, .h2 => 7
  | .amazing, false, .h3 => 47
  | .amazing, true, .h0 => 47
  | .amazing, true, .h1 => 47
  | .amazing, true, .h2 => 38
  | .amazing, true, .h3 => 0

/-- The soft literal meaning `𝓛(s)` of an utterance is its acceptance proportion at the state. -/
def meaning (u : Utterance) (s : HeartState) : ℚ := acceptance u.1 u.2 s / 49

theorem meaning_bounded (u : Utterance) (s : HeartState) : 0 ≤ meaning u s ∧ meaning u s ≤ 1 := by
  obtain ⟨a, b⟩ := u
  cases a <;> cases b <;> cases s <;> constructor <;> norm_num [meaning, acceptance]

/-- A plain adjective costs 1, and a negated one the cost of negation `c`. -/
def cost (c : ℝ) (u : Utterance) : ℝ := if u.2 then c else 1

/-! ### The literal listener

With a uniform state prior, `P_L0(s | w) = 𝓛(s) / Σ_s' 𝓛(s')`. -/

private theorem sum_hearts (f : HeartState → ℚ) :
    (∑ s : HeartState, f s) = f .h0 + f .h1 + f .h2 + f .h3 := by
  rw [show (Finset.univ : Finset HeartState) = {.h0, .h1, .h2, .h3} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The lexicon mass of an utterance, the literal listener's normalizer. -/
def semMass (u : Utterance) : ℚ := ∑ s : HeartState, meaning u s

/-- `P_L0(s | u)`, the literal listener's posterior under the uniform prior. -/
def l0 (u : Utterance) (s : HeartState) : ℚ := meaning u s / semMass u

/-- `E_{P_L0(· | u)}[V(s)]`, the social utility of `u`, which does not depend on the true
state. -/
def ev (u : Utterance) : ℚ := ∑ s : HeartState, l0 u s * s.value

private theorem ev_terrible : ev (.terrible, false) = 29/76 := by
  rw [ev, sum_hearts]
  norm_num [l0, semMass, sum_hearts, meaning, acceptance, HeartState.value]

private theorem ev_notTerrible : ev (.terrible, true) = 239/111 := by
  rw [ev, sum_hearts]
  norm_num [l0, semMass, sum_hearts, meaning, acceptance, HeartState.value]

private theorem ev_amazing : ev (.amazing, false) = 39/14 := by
  rw [ev, sum_hearts]
  norm_num [l0, semMass, sum_hearts, meaning, acceptance, HeartState.value]

private theorem ev_notAmazing : ev (.amazing, true) = 41/44 := by
  rw [ev, sum_hearts]
  norm_num [l0, semMass, sum_hearts, meaning, acceptance, HeartState.value]

/-! ### The first-order speaker -/

/-- The first-order utility `U(w; s; φ) = φ · ln P_L0(s | w) + (1 − φ) · E_L0[V(s)] − C(w)`,
scaled by the optimality `α`, as an extended-real score over the situations `(s, φ)`. An
utterance of literal probability zero at `s` scores `⊥` for every `φ ≠ 0`. -/
noncomputable def util (α c : ℝ) (p : HeartState × Phi) (u : Utterance) : EReal :=
  if meaning u p.1 = 0 ∧ p.2 ≠ .p0 then ⊥
  else ((α * ((Phi.val p.2 : ℝ) * Real.log (l0 u p.1 : ℝ)
    + (1 - (Phi.val p.2 : ℝ)) * (ev u : ℝ) - cost c u) : ℝ) : EReal)

private theorem util_ungated {α c : ℝ} {s : HeartState} {φ : Phi} {u : Utterance}
    (h : ¬(meaning u s = 0 ∧ φ ≠ .p0)) :
    util α c (s, φ) u
      = ((α * ((Phi.val φ : ℝ) * Real.log (l0 u s : ℝ)
          + (1 - (Phi.val φ : ℝ)) * (ev u : ℝ) - cost c u) : ℝ) : EReal) := by
  unfold util
  rw [ite_eq_right h]

private theorem util_gated {α c : ℝ} {s : HeartState} {φ : Phi} {u : Utterance}
    (h0 : meaning u s = 0) (hφ : φ ≠ .p0) : util α c (s, φ) u = ⊥ := by
  unfold util
  rw [ite_eq_left ⟨h0, hφ⟩]

theorem util_ne_top (α c : ℝ) (p : HeartState × Phi) (u : Utterance) : util α c p u ≠ ⊤ := by
  unfold util
  split
  · exact bot_ne_top
  · exact EReal.coe_ne_top _

theorem util_exists_ne_bot (α c : ℝ) (p : HeartState × Phi) : ∃ u, util α c p u ≠ ⊥ := by
  obtain ⟨s, φ⟩ := p
  cases s
  · exact ⟨(.terrible, false), by
      rw [util_ungated (by norm_num [meaning, acceptance])]
      exact EReal.coe_ne_bot _⟩
  · exact ⟨(.bad, false), by
      rw [util_ungated (by norm_num [meaning, acceptance])]
      exact EReal.coe_ne_bot _⟩
  · exact ⟨(.good, false), by
      rw [util_ungated (by norm_num [meaning, acceptance])]
      exact EReal.coe_ne_bot _⟩
  · exact ⟨(.amazing, false), by
      rw [util_ungated (by norm_num [meaning, acceptance])]
      exact EReal.coe_ne_bot _⟩

/-- The first-order speaker (5) is the score speaker of `util`. -/
noncomputable def speaker (α c : ℝ) : Kernel (HeartState × Phi) Utterance :=
  Kernel.softmax (util α c)

instance (α c : ℝ) : IsFiniteKernel (speaker α c) :=
  inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

theorem speaker_real_singleton_lt_iff (α c : ℝ) (p : HeartState × Phi) (u u' : Utterance) :
    (speaker α c p).real {u} < (speaker α c p).real {u'} ↔ util α c p u < util α c p u' :=
  Kernel.softmax_real_singleton_lt_iff (util_ne_top α c p) (util_exists_ne_bot α c p)

theorem speaker_apply_eq_zero_of_meaning_eq_zero (α c : ℝ) {s : HeartState} {φ : Phi}
    {u : Utterance} (h0 : meaning u s = 0) (hφ : φ ≠ .p0) : speaker α c (s, φ) {u} = 0 :=
  Kernel.softmax_apply_singleton_eq_zero (util_gated h0 hφ)

/-! ### First-order predictions (Figure 2, top right) -/

theorem social_lt_iff {α : ℝ} (hα : 0 < α) (c : ℝ) (s : HeartState) (u u' : Utterance) :
    (speaker α c (s, .p0)).real {u} < (speaker α c (s, .p0)).real {u'} ↔
      (ev u : ℝ) - cost c u < (ev u' : ℝ) - cost c u' := by
  rw [speaker_real_singleton_lt_iff, util_ungated (by simp), util_ungated (by simp),
    EReal.coe_lt_coe_iff, mul_lt_mul_iff_right₀ hα]
  simp [Phi.val]

/-- The pure-social speaker prefers the indirect "not terrible" to "terrible" exactly when the
extra cost of negation is below the social gain of the negation. -/
theorem social_prefers_indirect_iff {α : ℝ} (hα : 0 < α) (c : ℝ) (s : HeartState) :
    (speaker α c (s, .p0)).real {(.terrible, false)}
        < (speaker α c (s, .p0)).real {(.terrible, true)} ↔
      c - 1 < (ev (.terrible, true) : ℝ) - ev (.terrible, false) := by
  rw [social_lt_iff hα]
  simp only [cost, Bool.false_eq_true, ite_true, ite_false]
  constructor <;> intro h <;> linarith

/-- The pure-social speaker prefers "amazing" to "not amazing", since the direct form is both
kinder and no costlier. -/
theorem social_prefers_positive {α c : ℝ} (hα : 0 < α) (hc : 1 ≤ c) (s : HeartState) :
    (speaker α c (s, .p0)).real {(.amazing, true)}
      < (speaker α c (s, .p0)).real {(.amazing, false)} := by
  rw [social_lt_iff hα, ev_amazing, ev_notAmazing]
  simp only [cost, Bool.false_eq_true, ite_true, ite_false]
  norm_num
  linarith

/-- The pure-informative speaker prefers the direct "terrible" at zero hearts, since the literal
listener puts far more of the mass of "terrible" than of "not terrible" on that state, and the
direct form is no costlier. -/
theorem informative_prefers_direct {α c : ℝ} (hα : 0 < α) (hc : 1 ≤ c) :
    (speaker α c (.h0, .p100)).real {(.terrible, true)}
      < (speaker α c (.h0, .p100)).real {(.terrible, false)} := by
  rw [speaker_real_singleton_lt_iff, util_ungated (by norm_num [meaning, acceptance]),
    util_ungated (by norm_num [meaning, acceptance]), EReal.coe_lt_coe_iff,
    mul_lt_mul_iff_right₀ hα]
  have hlog : Real.log ((l0 (.terrible, true) .h0 : ℚ) : ℝ)
      < Real.log ((l0 (.terrible, false) .h0 : ℚ) : ℝ) := by
    apply Real.log_lt_log
    · norm_num [l0, semMass, sum_hearts, meaning, acceptance]
    · norm_num [l0, semMass, sum_hearts, meaning, acceptance]
  simp only [Phi.val, cost, Bool.false_eq_true, ite_true, ite_false]
  norm_num
  linarith

/-- The pure-informative speaker prefers the direct "amazing" at three hearts, where "not
amazing" is never accepted, so its score is `⊥`. -/
theorem informative_prefers_direct_positive (α c : ℝ) :
    (speaker α c (.h3, .p100)).real {(.amazing, true)}
      < (speaker α c (.h3, .p100)).real {(.amazing, false)} := by
  rw [speaker_real_singleton_lt_iff, util_gated (by norm_num [meaning, acceptance]) (by decide),
    util_ungated (by norm_num [meaning, acceptance])]
  exact EReal.bot_lt_coe _

/-! ### The pragmatic listener, (4) -/

/-- The uniform joint prior over states and goal weights. -/
noncomputable def prior : Measure (HeartState × Phi) := uniformOn Set.univ

instance : IsProbabilityMeasure prior := inferInstanceAs (IsProbabilityMeasure (uniformOn _))

theorem prior_ne_zero (p : HeartState × Phi) : prior {p} ≠ 0 :=
  uniformOn_univ_singleton_ne_zero p

theorem comp_speaker_ne_zero (α c : ℝ) (u : Utterance) : (speaker α c ∘ₘ prior) {u} ≠ 0 := by
  have key : ∀ s : HeartState, meaning u s ≠ 0 → (speaker α c ∘ₘ prior) {u} ≠ 0 := fun s hs =>
    Measure.comp_apply_singleton_ne_zero _ _ (prior_ne_zero (s, .p100))
      (Kernel.softmax_apply_singleton_ne_zero
        (by rw [util_ungated (by simp [hs])]; exact EReal.coe_ne_bot _) (util_ne_top α c _))
  obtain ⟨a, b⟩ := u
  cases a <;> cases b <;> exact key .h0 (by norm_num [meaning, acceptance])

/-- The pragmatic listener (4) infers the state and the goal weight `(s, φ)` from the utterance.
Its first marginal is `P_L1(s | w)` and its second `P_L1(φ | w)`, the probability inside (3). -/
noncomputable def listener (α c : ℝ) : Kernel Utterance (HeartState × Phi) :=
  RSA.listener prior (speaker α c)

/-! ### The second-order polite speaker, (1)–(3) -/

/-- The weights `ω` on the informational, social and presentational utilities. -/
structure S2Weights where
  wInf : ℚ
  wSoc : ℚ
  wPres : ℚ

/-- Table 2 gives the maximum a posteriori goal weights of the full model in each goal
condition. -/
def tableTwo : GoalCondition → S2Weights
  | .both => ⟨36/100, 11/100, 54/100⟩
  | .informative => ⟨36/100, 2/100, 62/100⟩
  | .kind => ⟨25/100, 31/100, 44/100⟩

/-- Table 2 gives the maximum a posteriori projected goal weight `φ` of the full model in each
goal condition. -/
def tableTwoPhi : GoalCondition → ℚ
  | .both => 36/100
  | .informative => 49/100
  | .kind => 37/100

/-- The total utility (2), with the presentational utility (3), is
`ω_inf · ln P_L1(s | w) + ω_soc · E_{P_L1(· | w)}[V] + ω_pres · ln P_L1(phiHat | w) − C(w)`, for the
projected goal weight `phiHat`. -/
noncomputable def s2Utility (α c : ℝ) (W : S2Weights) (phiHat : Phi) (s : HeartState)
    (u : Utterance) : ℝ :=
  (W.wInf : ℝ) * Real.log ((listener α c u).fst.real {s})
    + (W.wSoc : ℝ) * ∑ s' : HeartState, (listener α c u).fst.real {s'} * (s'.value : ℝ)
    + (W.wPres : ℝ) * Real.log ((listener α c u).snd.real {phiHat})
    - cost c u

/-- The second-order speaker (1) is the score speaker of the total utility scaled by `α`. -/
noncomputable def s2Speaker (α c : ℝ) (W : S2Weights) (phiHat : Phi) :
    Kernel HeartState Utterance :=
  Kernel.softmax fun s u => ((α * s2Utility α c W phiHat s u : ℝ) : EReal)

end YoonEtAl2020
