module

public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Pragmatics.RSA.Decision
public import Linglib.Pragmatics.RSA.Uniform
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sumers, Ho, Griffiths, and Hawkins (2024): Reconciling Truthfulness and Relevance as Epistemic and Decision-Theoretic Utility

On the speaker model of Sumers, Ho, Griffiths and Hawkins, Grice's maxims of quality and
relation are two independent objectives a speaker trades off. Truthfulness is an epistemic
utility, `1` for a true utterance and `-1` for a false one (5), `truthfulness`; relevance is a
decision-theoretic utility after van Rooy and Benz, the reward the listener earns by acting on
the utterance in a decision problem (6)–(8), `RSA.actionUtility` of `RSA.policy`; and the speaker
of a Rational Speech Act model, after Frank and Goodman, soft-maximizes their convex combination
at a weight `λ` plus a cost term (9), `combinedUtility`, `speaker`. The endpoints are the purely
truthful speaker, who is insensitive to the decision problem and uniform over the true utterances,
`speaker_zero_eq_of_mem`, and the purely relevant speaker, who exaggerates whenever
exaggeration earns the listener more, `speaker_one_real_lt_iff`.

Signaling bandits decouple the two objectives. A world assigns a value to each feature, an
action carries a set of features, and its reward is the sum of their values (10)–(11),
`reward`; an utterance names a feature and its value, true at a world regardless of the
decision context, `sem`; the listener conditions a uniform prior on the utterance and acts on
the expected rewards of the actions in the context. Under the uniform prior the posterior
mean of the named feature is the named value and every other feature keeps its prior mean,
`expectedReward_listener_filter`, which is how the paper reads Figure 6C: in the
context of a red spotted, a red solid, and a blue striped mushroom, naming the value of green
or the zero value of red is true but leaves the listener's policy where the prior had it,
`green_two_true_irrelevant`, `red_zero_true_irrelevant`; naming a positive value of spots is
relevant, and the more so the higher the value, so the exaggeration is false but more relevant
than the truth, `spots_relevant_iff`, `exaggeration_relevant`; and the combined speaker prefers
the true utterance exactly when the relevance gained by exaggerating is worth less than the
truthfulness lost, `prefers_truth_iff`. Relevance is context-dependent where truth is not: in
a context of three spotted mushrooms naming the value of spots is irrelevant and naming the
value of green is relevant (footnote 12), `spots_irrelevant_allSpotted`,
`green_relevant_allSpotted`.

Appendix A relates decision problems to Roberts's questions under discussion. For the
two-action decision problem in which one action earns `r` in a cell of the partition
containing the true world and `s` outside it, and the other the reverse, relevance is a
logistic function of the listener's posterior mass on the cell, `actionUtility_cellReward`,
so for `s < r` it ranks utterances exactly as the question's epistemic utility, the log of
that mass, does, `actionUtility_lt_iff_qudUtility_lt`; the identity decision problem of
Theorem 1 is the case of the singleton cell, `actionUtility_lt_iff_log_lt`.

The paper's two experiments put participants in the speaker's role in the mushroom domain.
In the free-choice experiment participants instructed to be truthful, given no instruction,
or instructed to make the tourist pick well were fit by increasing weights on relevance, the
uninstructed participants strictly between the endpoints; in the endorsement experiment the
separation widened and the uninstructed participants still balanced the two; and the combined
model was favored over either objective alone. The worked examples, on which a pragmatic
listener embedding the combined speaker infers that a mentioned garage is open, loosens a
stated start time, and rounds the time when asked casually, after Van der Henst and colleagues, are
simulations at chosen parameters and are not formalized.

## Implementation notes

The listener's decision context is the action type, so a context of the bandit is a type of
actions with their feature sets, and an utterance's relevance in two contexts is its utility
against two action types. The cost term enters with the sign of (9). Lewis signaling games,
where the world state is the correct action and the objectives coincide, are described and
not formalized.

## TODO

* Theorem 1's exact identity: the reward `s` at which relevance under the identity decision
  problem equals the log of the posterior mass, defined through the Lambert W function.

## References

* [sumers-etal-2024]
* [frank-goodman-2012]
* [grice-1975]
* [van-rooy-2003]
* [benz-2006]
* [roberts-2012]
* [van-der-henst-etal-2002]
* [qing-franke-2015]
-/

@[expose] public section

namespace SumersEtAl2024

open MeasureTheory ProbabilityTheory RSA Finset
open scoped ENNReal

/-! ### The speaker objectives -/

section Objectives

variable {W U A : Type*} [DecidableEq W] [MeasurableSpace U] [Fintype A] [MeasurableSpace A]

/-- Truthfulness as epistemic utility (5) is `1` for a true utterance and `-1` for a false one. -/
def truthfulness (sem : U → Finset W) (u : U) (w : W) : ℝ := if w ∈ sem u then 1 else -1

/-- The combined utility (9) mixes relevance and truthfulness at weight `lam` on relevance and
adds the cost term. -/
noncomputable def combinedUtility (lam : ℝ) (cost : U → ℝ) (sem : U → Finset W)
    (π : Kernel U A) (R : A → W → ℝ) (u : U) (w : W) : ℝ :=
  lam * actionUtility π R u w + (1 - lam) * truthfulness sem u w + cost u

variable (cost : U → ℝ) (sem : U → Finset W) (π : Kernel U A) (R : A → W → ℝ) {u : U}
  {w : W}

theorem combinedUtility_zero :
    combinedUtility 0 cost sem π R u w = truthfulness sem u w + cost u := by
  simp [combinedUtility]

theorem combinedUtility_one :
    combinedUtility 1 cost sem π R u w = actionUtility π R u w + cost u := by
  simp [combinedUtility]

end Objectives

section Speaker

variable {W U A : Type*} [Fintype W] [DecidableEq W] [MeasurableSpace W]
  [DiscreteMeasurableSpace W] [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
  [Fintype A] [MeasurableSpace A]

/-- The speaker (1) is the softmax of combined utility at rationality `βS`. -/
noncomputable def speaker (βS lam : ℝ) (cost : U → ℝ) (sem : U → Finset W)
    (π : Kernel U A) (R : A → W → ℝ) : Kernel W U :=
  Kernel.softmax fun w u ↦ ((βS * combinedUtility lam cost sem π R u w : ℝ) : EReal)

variable (lam : ℝ) (cost : U → ℝ) (sem : U → Finset W) (π : Kernel U A)
  (R : A → W → ℝ) {βS : ℝ} {u u' : U} {w : W}

instance : IsFiniteKernel (speaker βS lam cost sem π R) :=
  inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty U] : IsMarkovKernel (speaker βS lam cost sem π R) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary U, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

/-- Row preference of the speaker is comparison of combined utility. -/
theorem speaker_real_lt_iff (hβ : 0 < βS) :
    (speaker βS lam cost sem π R w).real {u} < (speaker βS lam cost sem π R w).real {u'} ↔
      combinedUtility lam cost sem π R u w < combinedUtility lam cost sem π R u' w := by
  rw [speaker, Kernel.softmax_real_singleton_lt_iff (w := w) (fun _ ↦ EReal.coe_ne_top _)
    ⟨u, EReal.coe_ne_bot _⟩, EReal.coe_lt_coe_iff]
  exact mul_lt_mul_iff_right₀ hβ

theorem speaker_zero_eq_of_mem (c : ℝ) (hu : w ∈ sem u) (hu' : w ∈ sem u') :
    speaker βS 0 (fun _ ↦ c) sem π R w {u} = speaker βS 0 (fun _ ↦ c) sem π R w {u'} := by
  simp only [speaker, Kernel.softmax_apply_singleton, combinedUtility_zero, truthfulness, hu, hu',
    ite_true]

/-- The purely relevant speaker prefers the utterance that earns the listener more, true or
not. -/
theorem speaker_one_real_lt_iff (hβ : 0 < βS) (c : ℝ) :
    (speaker βS 1 (fun _ ↦ c) sem π R w).real {u} <
        (speaker βS 1 (fun _ ↦ c) sem π R w).real {u'} ↔
      actionUtility π R u w < actionUtility π R u' w := by
  rw [speaker_real_lt_iff _ _ _ _ _ hβ, combinedUtility_one, combinedUtility_one]
  exact add_lt_add_iff_right c

end Speaker

/-! ### Appendix A: decision problems and questions under discussion -/

section Cell

variable {W U : Type*} [Fintype W] [DecidableEq W] [MeasurableSpace W]
  [DiscreteMeasurableSpace W] [MeasurableSpace U]

/-- In the decision problem of a cell the first action earns `r` in the cell and `s` outside it,
and the second the reverse. -/
def cellReward (r s : ℝ) (c : Finset W) : Fin 2 → W → ℝ :=
  fun a w ↦ if (w ∈ c ↔ a = 0) then r else s

/-- The listener's posterior mass on the cell (A3). -/
noncomputable def cellMass (L : Kernel U W) (c : Finset W) (u : U) : ℝ :=
  ∑ w ∈ c, (L u).real {w}

/-- The epistemic utility of an utterance relative to a question (A2) is the log of the
posterior mass on the cell of the true world. -/
noncomputable def qudUtility (L : Kernel U W) (c : Finset W) (u : U) : ℝ :=
  Real.log (cellMass L c u)

variable (L : Kernel U W) [IsMarkovKernel L] {r s : ℝ} (c : Finset W) {u u' : U} {w : W}
  {β : ℝ}

theorem expectedReward_cellReward (u : U) :
    expectedReward L (cellReward r s c) u 0 = s + (r - s) * cellMass L c u ∧
      expectedReward L (cellReward r s c) u 1 = r + (s - r) * cellMass L c u := by
  have htot := sum_filter_add_sum_filter_not univ (· ∈ c) fun w ↦ (L u).real {w}
  have h1 : ∑ w, (L u).real {w} = 1 := sum_measureReal_singleton_eq_one (L u)
  rw [filter_mem_eq_inter, univ_inter, h1] at htot
  have hB : ∑ w with w ∉ c, (L u).real {w} = 1 - cellMass L c u := by
    rw [cellMass]; linarith
  simp only [expectedReward, cellReward, Fin.isValue, iff_true, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, iff_false, mul_ite, sum_ite, not_not, filter_mem_eq_inter, univ_inter,
    ← sum_mul, hB, cellMass]
  constructor <;> ring

variable [Fintype U] [DiscreteMeasurableSpace U]

/-- Relevance under the cell decision problem is a logistic function of the posterior mass on
the cell, the calculation of Appendix A. -/
theorem actionUtility_cellReward (hw : w ∈ c) :
    actionUtility (policy β L (cellReward r s c)) (cellReward r s c) u w =
      s + (r - s) * Real.sigmoid (β * (r - s) * (2 * cellMass L c u - 1)) := by
  obtain ⟨h0, h1⟩ := expectedReward_cellReward L c (r := r) (s := s) u
  rw [actionUtility_of_pair (cellReward r s c) (policy β L (cellReward r s c)) (a := 0) (a' := 1)
      (by decide) (fun a ↦ by fin_cases a <;> simp),
    policy_real_of_pair L (cellReward r s c) (a := 0) (a' := 1) (by decide)
      (fun a ↦ by fin_cases a <;> simp), h0, h1]
  simp only [cellReward, hw, Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, iff_false,
    not_true_eq_false, ite_true, ite_false]
  ring_nf

/-- If `s < r`, the cell decision problem ranks utterances as the question's epistemic utility does
(Theorem 2). -/
theorem actionUtility_lt_iff_qudUtility_lt (hw : w ∈ c) (hrs : s < r) (hβ : 0 < β)
    (hu : 0 < cellMass L c u) (hu' : 0 < cellMass L c u') :
    actionUtility (policy β L (cellReward r s c)) (cellReward r s c) u w <
        actionUtility (policy β L (cellReward r s c)) (cellReward r s c) u' w ↔
      qudUtility L c u < qudUtility L c u' := by
  rw [actionUtility_cellReward L c hw, actionUtility_cellReward L c hw, qudUtility, qudUtility,
    Real.log_lt_log_iff hu hu', add_lt_add_iff_left,
    mul_lt_mul_iff_right₀ (sub_pos.2 hrs), Real.sigmoid_lt_iff,
    mul_lt_mul_iff_right₀ (mul_pos hβ (sub_pos.2 hrs))]
  constructor <;> intro h <;> linarith

/-- The identity decision problem ranks utterances by the listener's log posterior of the true world
(Theorem 1). -/
theorem actionUtility_lt_iff_log_lt (hrs : s < r) (hβ : 0 < β) (hu : 0 < (L u).real {w})
    (hu' : 0 < (L u').real {w}) :
    actionUtility (policy β L (cellReward r s {w})) (cellReward r s {w}) u w <
        actionUtility (policy β L (cellReward r s {w})) (cellReward r s {w}) u' w ↔
      Real.log ((L u).real {w}) < Real.log ((L u').real {w}) := by
  rw [actionUtility_lt_iff_qudUtility_lt L {w} (mem_singleton_self w) hrs hβ
    (by rwa [cellMass, sum_singleton]) (by rwa [cellMass, sum_singleton]), qudUtility, qudUtility,
    cellMass, cellMass, sum_singleton, sum_singleton]

end Cell

/-! ### Signaling bandits -/

section Bandit

variable {K V A U : Type*} [Fintype K] [DecidableEq K] [Fintype V]

/-- The reward of an action carrying the features `feat a` at a world is the sum of their
values (10)–(11). -/
def reward (val : V → ℝ) (feat : A → Finset K) (a : A) (w : K → V) : ℝ :=
  ∑ k ∈ feat a, val (w k)

theorem sum_ite_div_sum_ite (p : V → Prop) [DecidablePred p] (hp : ∃ x, p x) (f k : K)
    (g : V → ℝ) :
    (∑ w : K → V, if p (w f) then g (w k) else 0) /
        (∑ w : K → V, if p (w f) then (1 : ℝ) else 0) =
      if k = f then (∑ x with p x, g x) / (univ.filter p).card
        else (∑ x, g x) / Fintype.card V := by
  have key : ∀ g : V → ℝ, (∑ w : K → V, if p (w f) then g (w k) else 0) =
      ∏ i, ∑ x, (if i = f then (if p x then 1 else 0) else 1) * (if i = k then g x else 1) := by
    intro g
    rw [prod_univ_sum, Fintype.piFinset_univ]
    refine sum_congr rfl fun w _ ↦ ?_
    rw [prod_mul_distrib, prod_ite_eq', prod_ite_eq', ite_eq_left (mem_univ _),
      ite_eq_left (mem_univ _), boole_mul]
  have key₁ : (∑ w : K → V, if p (w f) then (1 : ℝ) else 0) =
      ∏ i, ∑ x, (if i = f then (if p x then 1 else 0) else 1) * (if i = k then (1 : ℝ) else 1) :=
    key fun _ ↦ 1
  obtain ⟨x₀, hx₀⟩ := hp
  have hcard : ((univ.filter p).card : ℝ) ≠ 0 := by
    exact_mod_cast (card_pos.2 ⟨x₀, mem_filter.2 ⟨mem_univ _, hx₀⟩⟩).ne'
  have hV : (Fintype.card V : ℝ) ≠ 0 := by
    have : Nonempty V := ⟨x₀⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [key, key₁, ← prod_div_distrib]
  rw [show (∏ i, (∑ x, (if i = f then (if p x then 1 else 0) else 1) * (if i = k then g x else 1))
      / (∑ x, (if i = f then (if p x then 1 else 0) else 1) * (if i = k then (1 : ℝ) else 1))) =
      ∏ i, if i = k then (if k = f then (∑ x with p x, g x) / (univ.filter p).card
        else (∑ x, g x) / Fintype.card V) else 1 from
    prod_congr rfl fun i _ ↦ by
      by_cases hif : i = f
      · subst hif
        by_cases hik : i = k
        · subst hik; simp [sum_boole, sum_filter]
        · simp [hik, sum_boole, hcard]
      · by_cases hik : i = k
        · subst hik; simp [hif]
        · simp [hif, hik, hV]]
  rw [prod_ite_eq', ite_eq_left (mem_univ _)]

variable [DecidableEq V]

/-- The utterance naming a feature and a value is true at the worlds where the feature has that
value. -/
def sem (u : K × V) : Finset (K → V) := univ.filter fun w ↦ w u.1 = u.2

theorem mem_sem_iff (u : K × V) (w : K → V) : w ∈ sem u ↔ w u.1 = u.2 := by simp [sem]

variable [MeasurableSpace (K → V)] [DiscreteMeasurableSpace (K → V)] [Fintype U]
  [MeasurableSpace U] [DiscreteMeasurableSpace U]

theorem expectedReward_listener_filter {S : U → Finset (K → V)} {u : U} (p : V → Prop)
    [DecidablePred p] (hp : ∃ x, p x) (f : K) (hS : S u = univ.filter fun w ↦ p (w f))
    (val : V → ℝ) (feat : A → Finset K) (a : A) :
    expectedReward (RSA.listener (uniformOn Set.univ) (truthful fun u ↦ (S u : Set (K → V))))
        (reward val feat) u a =
      ∑ k ∈ feat a, if k = f then (∑ x with p x, val x) / (univ.filter p).card
        else (∑ x, val x) / Fintype.card V := by
  simp only [expectedReward, listener_uniformOn_truthful_real_singleton, hS, mem_filter, mem_univ,
    true_and,
    reward, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← sum_ite_div_sum_ite p hp f k val, sum_div]
  refine sum_congr rfl fun w _ ↦ ?_
  rw [card_filter]
  push_cast
  split_ifs <;> simp [div_eq_inv_mul]

end Bandit

/-! ### The mushroom domain of Figure 6 -/

section Mushrooms

/-- The features are three colors and three textures. -/
inductive Feature
  | green | red | blue | spots | solid | stripes
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Feature := ⊤

/-- Feature values `-2` to `+2`, as `0` to `4`. -/
abbrev Value := Fin 5

/-- The reward value of a feature value. -/
def val (v : Value) : ℝ := (v : ℝ) - 2

theorem sum_val : ∑ x : Value, val x = 0 := by
  simp [Fin.sum_univ_five, val]; norm_num

/-- The world of Figure 6A has green `+2`, red `0`, blue `-2`, spots `+1`, solid `0` and stripes
`-1`. -/
def world : Feature → Value
  | .green => 4 | .red => 2 | .blue => 0 | .spots => 3 | .solid => 2 | .stripes => 1

/-- The context of Figure 6B has a red spotted, a red solid, and a blue striped mushroom. -/
def feat : Fin 3 → Finset Feature
  | 0 => {.red, .spots}
  | 1 => {.red, .solid}
  | 2 => {.blue, .stripes}

/-- The context of footnote 12 has a green, a red, and a blue spotted mushroom. -/
def featSpotted : Fin 3 → Finset Feature
  | 0 => {.green, .spots}
  | 1 => {.red, .spots}
  | 2 => {.blue, .spots}

/-- The literal listener (3) at the uniform prior over worlds. -/
noncomputable abbrev listener : Kernel (Feature × Value) (Feature → Value) :=
  RSA.listener (uniformOn Set.univ) (truthful fun u ↦ (sem u : Set (Feature → Value)))

/-- The prior as a listener who has heard nothing. -/
noncomputable abbrev prior : Kernel (Feature × Value) (Feature → Value) :=
  RSA.listener (uniformOn Set.univ) (truthful fun _ ↦ ((univ : Finset (Feature → Value)) : Set _))

variable (fs : Fin 3 → Finset Feature) (u : Feature × Value) (a : Fin 3) {β βS : ℝ}

theorem expectedReward_listener :
    expectedReward listener (reward val fs) u a = ∑ k ∈ fs a, if k = u.1 then val u.2 else 0 := by
  rw [expectedReward_listener_filter (S := sem) (u := u) (· = u.2) ⟨u.2, rfl⟩ u.1 rfl,
    sum_val]
  simp [filter_eq']

theorem expectedReward_prior : expectedReward prior (reward val fs) u a = 0 := by
  rw [expectedReward_listener_filter (S := fun _ ↦ univ) (u := u) (fun _ ↦ True)
    ⟨u.2, trivial⟩ u.1 (filter_true_of_mem fun _ _ ↦ trivial).symm, sum_val]
  simp
  exact fun _ ↦ sum_val

/-- Two utterances after which every action's expected reward agrees up to a shift are
equally useful in the context. -/
theorem actionUtility_eq_prior_of_expectedReward {c : ℝ}
    (h : ∀ a, expectedReward listener (reward val fs) u a = c) :
    actionUtility (policy β listener (reward val fs)) (reward val fs) u world =
      actionUtility (policy β prior (reward val fs)) (reward val fs) u world :=
  actionUtility_policy_eq_of_expectedReward_eq_add listener (reward val fs) fun a ↦ by
    rw [h a, expectedReward_prior, zero_add]

/-- The three mushrooms of Figure 6B earn `1`, `0` and `-3` at the world. -/
theorem reward_world :
    reward val feat 0 world = 1 ∧ reward val feat 1 world = 0 ∧ reward val feat 2 world = -3 := by
  simp [reward, feat, world, val]; norm_num

theorem actionUtility_prior :
    actionUtility (policy β prior (reward val feat)) (reward val feat) u world = -2 / 3 := by
  obtain ⟨h0, h1, h2⟩ := reward_world
  simp only [actionUtility, policy_real_singleton, expectedReward_prior, mul_zero,
    Fin.sum_univ_three, h0, h1, h2]
  rw [show (fun _ : Fin 3 ↦ (0 : ℝ)) = 0 from rfl, Real.softmax_zero]
  norm_num

theorem green_two_true_irrelevant :
    world ∈ sem (.green, 4) ∧
      actionUtility (policy β listener (reward val feat)) (reward val feat) (.green, 4) world =
        actionUtility (policy β prior (reward val feat)) (reward val feat) (.green, 4) world :=
  ⟨by simp [sem, world], actionUtility_eq_prior_of_expectedReward feat _ (c := 0) fun a ↦ by
    fin_cases a <;> simp [expectedReward_listener, feat]⟩

theorem red_zero_true_irrelevant :
    world ∈ sem (.red, 2) ∧
      actionUtility (policy β listener (reward val feat)) (reward val feat) (.red, 2) world =
        actionUtility (policy β prior (reward val feat)) (reward val feat) (.red, 2) world :=
  ⟨by simp [sem, world], actionUtility_eq_prior_of_expectedReward feat _ (c := 0) fun a ↦ by
    fin_cases a <;> simp [expectedReward_listener, feat, val]⟩

theorem expectedReward_spots (v : Value) :
    expectedReward listener (reward val feat) (.spots, v) a = if a = 0 then val v else 0 := by
  fin_cases a <;> simp [expectedReward_listener, feat]

theorem actionUtility_spots (v : Value) :
    actionUtility (policy β listener (reward val feat)) (reward val feat) (.spots, v) world =
      (Real.exp (β * val v) - 3) / (Real.exp (β * val v) + 2) := by
  obtain ⟨h0, h1, h2⟩ := reward_world
  simp only [actionUtility, policy_real_singleton, expectedReward_spots, Real.softmax_apply,
    Fin.sum_univ_three, h0, h1, h2]
  simp only [Fin.isValue, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false,
    Fin.reduceEq, mul_zero, Real.exp_zero]
  have := Real.exp_pos (β * val v)
  field_simp
  ring

theorem spots_relevant_iff (hβ : 0 < β) (v : Value) :
    actionUtility (policy β prior (reward val feat)) (reward val feat) (.spots, v) world <
        actionUtility (policy β listener (reward val feat)) (reward val feat) (.spots, v) world ↔
      0 < val v := by
  have key : 1 < Real.exp (β * val v) ↔ 0 < val v := by
    rw [Real.one_lt_exp_iff]; exact mul_pos_iff_of_pos_left hβ
  have := Real.exp_pos (β * val v)
  rw [actionUtility_prior, actionUtility_spots, ← key, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

theorem exaggeration_relevant (hβ : 0 < β) :
    world ∈ sem (.spots, 3) ∧ world ∉ sem (.spots, 4) ∧
      actionUtility (policy β listener (reward val feat)) (reward val feat) (.spots, 3) world <
        actionUtility (policy β listener (reward val feat)) (reward val feat) (.spots, 4)
          world := by
  refine ⟨by simp [sem, world], by simp [sem, world], ?_⟩
  rw [actionUtility_spots, actionUtility_spots, ← sub_pos]
  have h1 := Real.exp_pos (β * val 3)
  have h2 : Real.exp (β * val 3) < Real.exp (β * val 4) := by
    rw [Real.exp_lt_exp]; simp only [val]; norm_num; linarith
  have h3 : (Real.exp (β * val 4) - 3) / (Real.exp (β * val 4) + 2) -
      (Real.exp (β * val 3) - 3) / (Real.exp (β * val 3) + 2) =
      5 * (Real.exp (β * val 4) - Real.exp (β * val 3)) /
        ((Real.exp (β * val 4) + 2) * (Real.exp (β * val 3) + 2)) := by
    field_simp
    ring
  rw [h3]
  exact div_pos (by linarith) (by positivity)

/-- The combined speaker prefers the truth to the exaggeration exactly when the relevance
gained by exaggerating, weighted by `lam`, is worth less than the truthfulness lost. -/
theorem prefers_truth_iff (hβS : 0 < βS) (lam c : ℝ) :
    (speaker βS lam (fun _ ↦ c) sem (policy β listener (reward val feat)) (reward val feat)
        world).real {(.spots, 4)} <
      (speaker βS lam (fun _ ↦ c) sem (policy β listener (reward val feat)) (reward val feat)
        world).real {(.spots, 3)} ↔
      lam * (actionUtility (policy β listener (reward val feat)) (reward val feat) (.spots, 4) world
        - actionUtility (policy β listener (reward val feat)) (reward val feat) (.spots, 3) world)
        < 2 * (1 - lam) := by
  rw [speaker_real_lt_iff _ _ _ _ _ hβS]
  simp only [combinedUtility, truthfulness, sem, mem_filter, mem_univ, true_and, world,
    Fin.reduceEq, ite_true, ite_false]
  constructor <;> intro h <;> linarith

theorem spots_irrelevant_allSpotted (v : Value) :
    actionUtility (policy β listener (reward val featSpotted)) (reward val featSpotted)
        (.spots, v) world =
      actionUtility (policy β prior (reward val featSpotted)) (reward val featSpotted)
        (.spots, v) world :=
  actionUtility_eq_prior_of_expectedReward featSpotted _ (c := val v) fun a ↦ by
    fin_cases a <;> simp [expectedReward_listener, featSpotted]

theorem green_relevant_allSpotted (hβ : 0 < β) :
    actionUtility (policy β prior (reward val featSpotted)) (reward val featSpotted)
        (.green, 4) world <
      actionUtility (policy β listener (reward val featSpotted)) (reward val featSpotted)
        (.green, 4) world := by
  have hR : reward val featSpotted 0 world = 3 ∧ reward val featSpotted 1 world = 1 ∧
      reward val featSpotted 2 world = -1 := by
    simp [reward, featSpotted, world, val]; norm_num
  have hE : ∀ a, expectedReward listener (reward val featSpotted) (.green, 4) a =
      if a = 0 then 2 else 0 := by
    intro a; fin_cases a <;> simp [expectedReward_listener, featSpotted, val]; norm_num
  obtain ⟨h0, h1, h2⟩ := hR
  simp only [actionUtility, policy_real_singleton, expectedReward_prior, hE, mul_zero,
    Fin.sum_univ_three, h0, h1, h2, Real.softmax_apply]
  simp only [Fin.isValue, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false,
    Fin.reduceEq, mul_zero, Real.exp_zero]
  have he : 1 < Real.exp (β * 2) := Real.one_lt_exp_iff.2 (by positivity)
  have := Real.exp_pos (β * 2)
  rw [← sub_pos]
  have h3 : Real.exp (β * 2) / (Real.exp (β * 2) + 1 + 1) * 3 +
        1 / (Real.exp (β * 2) + 1 + 1) * 1 + 1 / (Real.exp (β * 2) + 1 + 1) * -1 -
      (1 / (1 + 1 + 1) * 3 + 1 / (1 + 1 + 1) * 1 + 1 / (1 + 1 + 1) * -1) =
      2 * (Real.exp (β * 2) - 1) / (Real.exp (β * 2) + 2) := by
    field_simp
    ring
  rw [h3]
  exact div_pos (by linarith) (by positivity)

end Mushrooms

end SumersEtAl2024
