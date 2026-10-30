module

public import Linglib.Logic.Aristotelian.Square
public import Linglib.Pragmatics.RSA.Decision
public import Studies.KirbyDowmanGriffiths2007

/-!
# Brochhagen, Franke and van Rooij (2018): Coevolution of Lexical Meaning and Pragmatic Use

A population of language users, each pairing a lexicon with a level of pragmatic reasoning,
evolves by the replicator mutator dynamic: types reproduce in proportion to their expected
communicative success and pass to the next generation by iterated Bayesian learning. The speakers
[send false messages](##speaker_eq_zero_and_agents_fst_ne_zero), so any type can be mistaken for
any other. Over the two states of *some*, a lexicon with the upper bound of *some*
[communicates better](##selfSuccess_lt) than one without, and the claim that every other type
beats literal use of the unbounded lexicon [fails at low rationality](##selfSuccess_Llack_zero_lt).
Learners who sample from the posterior [keep the prior](##invariant_biasedPrior); learners who
adopt the likeliest type
[favour the type others are mistaken for](##invariant_mapLearner_comp_lh_iff).

## Implementation notes

* The pragmatic speakers of eq. (6) maximize the chance that the hearer guesses the state, so they
  are `RSA.actionSpeaker` at the utility of a correct guess, not `RSA.speaker`, whose logarithmic
  utility [frank-goodman-2012] never sends a false message (note 2).
* A type's data (`produce`) draw each state from the state prior, so they have total mass one; the
  posterior over types is the same as under the printed likelihood (see Errata).
* The factor `1.05` of Fig. 2 is the prior's parameter, from the caption. `invariant_biasedPrior`
  shows for every factor that the stationary ratio of `L_lack` to `L_bound` users is the factor,
  which is the "exactly 1.05" of p. 2770.
* Appendix B's learners at `l = 10` are replaced by learners who adopt the likeliest type, the
  limit `l → ∞` and [griffiths-kalish-2007]'s `mapLearner`; the printed `Q` at `l = 10` is `LH`
  to the printed precision.
* The complexities of Table 2 are taken as printed; the lexicon prior is left unnormalized.
* Swapping *none* and *all* reverses the scale and preserves the flat prior, so the model is
  symmetric under it ([success_image](##success_image)). It takes the lexicon {*none*, *some*,
  *all*} to {*all*, *not all*, *none*}, which therefore communicates exactly as well with every
  type; only the prior separates them, by `7 : 6`, since *not all* costs one unit more than
  *some* ([success_lexMirror](##success_lexMirror)). The paper does not state this. Its six lexica
  "of the third kind" (p. 2770) are the permutations of the first; the permutations of the second
  leave the lower bound of *not all* to pragmatics instead.
* [brochhagen-franke-van-rooij-2016] is the precursor, over two states and two messages, with a
  speaker that weighs the literal hearer by an exponent and a prior that penalizes upper-bounded
  messages; it is not formalized separately. Its update (p. 2083) weights the mutation into type
  `i` by the share of `i` in the previous generation, which loses mass: with no mutation, equal
  fitness and the uniform population over its twelve types in both generations, the next
  population has total mass `1/12`. Its prose (p. 2082) says that `L_a` gives `m₁` an upper
  bound, but by its matrix the bounded message, true only at the first state, is `m₂`.

## Errata

* §3.1 (p. 2768) says that every type has a sizable advantage over literal `L_lack`. Pragmatic
  `L_bound` has one only when `λ > log(5/3)`, and pragmatic `L_lack` does worse than literal
  `L_lack` whenever `λ ≤ 2 log(5/2)`, as at the `λ = 1` of §2.4.1
  ([selfSuccess_Llack_zero_lt](##selfSuccess_Llack_zero_lt)).
* Appendix A (p. 2788) prints the replicator mutator step as
  `(0.9x² - 0.2x + 0.2) / (3x² - 4x + 2)` with rest points `.121`, `.609` and `.903`. These are
  the step and rest points when the negatives produced by mutation number `0.1 · 2(1 - x)`
  instead of `0.1 · (1 - x)(2 - 2x)`. The step is `(1.1x² - 0.4x + 0.2) / (3x² - 4x + 2)`
  ([rmd_real_negative](##rmd_real_negative)), whose rest points are numerically near `.106`,
  `.735` and `.859`.
* The likelihood of data in §2.4.3 (p. 2767) is the product of the speaker's chances of the
  messages, without the chances of the states, so it sums to `|S|^k` over the data of length
  `k` and the rows of `Q` do not sum to one.
* Table 2 (p. 2773) gives `A ∩ B ≠ ∅ ∧ A ≠ ∅` as the least complex formula for *some but not
  all*, but it expresses *some*, since its second conjunct follows from the first; the formula for
  *none or all*, its negation, expresses *none* given that `A` is nonempty. The formula
  `A ∩ B ≠ ∅ ∧ ¬(A ⊆ B)` for *some but not all* costs `11` by Table 1, more than the printed
  `8`; a higher cost only lowers the prior of `L_bound`, so `lexiconWeight_lt` still holds.
* In Appendix B (p. 2789) the third row of `LH` and of both matrices `Q` is labelled `t₂`; it is
  `t₃`.

## TODO

* The simulations of §3.3 are not formalized.
* That the costs of Table 2 are the least derivation costs in the grammar of Table 1.
* Convergence, not just invariance, of the chains of Fig. 2(b) and Appendix B.
* The type-level fitness of §2.4.2, the mean of a type's success as speaker and as hearer, over
  the 432 types of §3.2.

## References

* [brochhagen-franke-van-rooij-2018]
* [brochhagen-franke-van-rooij-2016]
* [griffiths-kalish-2007]
* [kirby-dowman-griffiths-2007]
* [frank-goodman-2012]
-/

@[expose] public section

namespace BrochhagenFrankeVanRooij2018

open MeasureTheory ProbabilityTheory Finset RSA
open Aristotelian (Triangle)
open KirbyDowmanGriffiths2007 (exponentiatedPosterior invariant_exponentiatedPosterior_one)
open GriffithsKalish2007 (mapLearner mapLearner_apply)
open scoped ENNReal NNReal

/-! ### Language users -/

section Agents

variable {S M : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S]
  [Fintype M] [MeasurableSpace M] [DiscreteMeasurableSpace M]

/-- Eqs. (3)–(6): the speaker and the hearer of reasoning level `n` with lexicon `L` at state
prior `pr` and rationality `lam`. The literal speaker is the softmax of the truth of a message,
the literal hearer conditions the prior on its truth, a pragmatic speaker is the softmax of the
chance that the hearer of the level below guesses the state, and a pragmatic hearer inverts the
speaker of the level below by Bayes' rule. -/
noncomputable def agents (pr : Measure S) (lam : ℝ) (L : M → Set S) : ℕ → Kernel S M × Kernel M S
  | 0 => (Kernel.softmax fun s m ↦ ((lam * (L m).indicator 1 s : ℝ) : EReal),
      listener pr (truthful L))
  | n + 1 => (actionSpeaker lam 0 (agents pr lam L n).2 fun a ↦ Pi.single a 1,
      listener pr fun s ↦ (agents pr lam L n).1 s)

/-- §2.4.2: the expected success of a speaker addressing a hearer, the chance that the hearer
guesses the speaker's state. -/
noncomputable def success (pr : Measure S) (σ : Kernel S M) (η : Kernel M S) : ℝ :=
  ∑ s, pr.real {s} * ∑ m, (σ s).real {m} * (η m).real {s}

variable (pr : Measure S) (lam : ℝ) (L : M → Set S)

theorem agents_zero_fst :
    (agents pr lam L 0).1 = Kernel.softmax fun s m ↦ ((lam * (L m).indicator 1 s : ℝ) : EReal) :=
  rfl

theorem agents_zero_snd : (agents pr lam L 0).2 = listener pr (truthful L) := rfl

theorem agents_succ_fst (n : ℕ) :
    (agents pr lam L (n + 1)).1 = actionSpeaker lam 0 (agents pr lam L n).2 fun a ↦ Pi.single a 1 :=
  rfl

theorem agents_succ_snd (n : ℕ) :
    (agents pr lam L (n + 1)).2 = listener pr fun s ↦ (agents pr lam L n).1 s := rfl

instance [Nonempty M] (n : ℕ) : IsMarkovKernel (agents pr lam L n).1 := by
  cases n
  · exact Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary M, EReal.coe_ne_bot _⟩)
      fun _ _ ↦ EReal.coe_ne_top _
  · exact inferInstanceAs (IsMarkovKernel (actionSpeaker _ _ _ _))

-- Note 2: every speaker sends every message, false ones included, with positive probability.
theorem agents_fst_apply_ne_zero (n : ℕ) (s : S) (m : M) : (agents pr lam L n).1 s {m} ≠ 0 := by
  cases n
  · exact Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _
  · exact actionSpeaker_apply_singleton_ne_zero _ _ _

-- With two messages, a pragmatic speaker's share of one is the logistic function of the scaled
-- difference in the chance that the hearer below guesses the state after each.
theorem agents_succ_fst_real_of_pair (n : ℕ) (s : S) {m m' : M} (hmm' : m ≠ m')
    (hall : ∀ c, c = m ∨ c = m') :
    ((agents pr lam L (n + 1)).1 s).real {m} = Real.sigmoid (lam *
      (((agents pr lam L n).2 m).real {s} - ((agents pr lam L n).2 m').real {s})) := by
  rw [agents_succ_fst, actionSpeaker_real_of_pair (fun a ↦ Pi.single a 1) 0 _ hmm' hall,
    actionUtility_single, actionUtility_single]
  simp

-- With two messages, the literal speaker's share of one is the logistic function of the scaled
-- difference in their truth.
theorem agents_zero_fst_real_of_pair (s : S) {m m' : M} (hmm' : m ≠ m')
    (hall : ∀ c, c = m ∨ c = m') :
    ((agents pr lam L 0).1 s).real {m} =
      Real.sigmoid (lam * (L m).indicator 1 s - lam * (L m').indicator 1 s) := by
  rw [agents_zero_fst, Kernel.softmax_real_singleton_of_pair hmm' (EReal.coe_ne_bot _)
    (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe,
    EReal.toReal_coe]

-- The literal hearer conditions the prior on the truth of the message.
theorem agents_zero_snd_real (m : M) (s : S) [Decidable (s ∈ L m)] :
    ((agents pr lam L 0).2 m).real {s} = if s ∈ L m then pr.real {s} / pr.real (L m) else 0 := by
  rw [agents_zero_snd]
  split_ifs with h
  · exact listener_truthful_real_singleton pr L h
  · rw [measureReal_def, listener_truthful_apply_singleton_of_notMem pr L h, ENNReal.toReal_zero]

private theorem softmax_apply_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable α]
    [MeasurableSingletonClass α] [Fintype β] {score score' : α → β → EReal} {a a' : α}
    (h : ∀ b, score' a' b = score a b) : Kernel.softmax score' a' = Kernel.softmax score a := by
  simp only [Kernel.softmax, Kernel.ofWeights, Kernel.ofFunOfCountable_apply, h]

-- The agents of a lexicon moved by a permutation of the states that preserves the prior are the
-- agents of the original lexicon, moved by that permutation.
theorem agents_image (e : S ≃ S) (he : ∀ s, pr {e s} = pr {s}) (n : ℕ) :
    (∀ s, (agents pr lam (fun m ↦ e '' L m) n).1 (e s) = (agents pr lam L n).1 s) ∧
      ∀ m s, (agents pr lam (fun m ↦ e '' L m) n).2 m {e s} = (agents pr lam L n).2 m {s} := by
  induction n with
  | zero =>
    refine ⟨fun s ↦ softmax_apply_eq fun m ↦ ?_, fun m s ↦ ?_⟩
    · rw [Set.indicator_image e.injective]
      rfl
    · refine listener_apply_singleton_of_equiv pr _ e he (fun t ↦ ?_) s
      rw [truthful_apply_singleton, truthful_apply_singleton, Set.indicator_image e.injective]
      rfl
  | succ n ih =>
    refine ⟨fun s ↦ softmax_apply_eq fun m ↦ ?_, fun m s ↦ ?_⟩
    · simp only [actionSpeakerScore, actionUtility_single, measureReal_def, ih.2]
    · exact listener_apply_singleton_of_equiv pr _ e he (fun t ↦ by rw [ih.1]) s

-- §2.4.2: so the expected success of any speaker of the moved lexicon with any hearer of a moved
-- lexicon is that of the original pair.
theorem success_image (L' : M → Set S) (e : S ≃ S) (he : ∀ s, pr {e s} = pr {s}) (n n' : ℕ) :
    success pr (agents pr lam (fun m ↦ e '' L m) n).1 (agents pr lam (fun m ↦ e '' L' m) n').2 =
      success pr (agents pr lam L n).1 (agents pr lam L' n').2 := by
  rw [success, ← e.sum_comp]
  refine sum_congr rfl fun s _ ↦ ?_
  simp only [measureReal_def, he, (agents_image pr lam L e he n).1,
    (agents_image pr lam L' e he n').2]

/-- Note 2: a speaker who maximizes the log of the literal hearer's credence in the state, as in
[frank-goodman-2012], never sends a false message, whereas every speaker of the paper, maximizing
the hearer's chance of guessing the state, sends every message with positive probability. -/
theorem speaker_eq_zero_and_agents_fst_ne_zero {α : ℝ} (hα : 0 < α) {s : S} {m : M}
    (h : s ∉ L m) :
    speaker α 0 (listener pr (truthful L)) Measure.dirac s {m} = 0 ∧
      ∀ n, (agents pr lam L n).1 s {m} ≠ 0 :=
  ⟨speaker_dirac_apply_singleton_eq_zero hα (listener_truthful_apply_singleton_of_notMem pr L h),
    fun n ↦ agents_fst_apply_ne_zero pr lam L n s m⟩

end Agents

/-! ### Some and all: the restricted type space of §3.1

The states are the two vertices of the I corner of the square of opposition, *some but not all*
(`Triangle.IO`) and *all* (`Triangle.A`), equally likely. -/

section TwoStates

scoped instance : MeasurableSpace Triangle := ⊤

scoped instance : DiscreteMeasurableSpace Triangle := ⟨fun _ ↦ trivial⟩

/-- The messages *some* and *all*. -/
inductive Msg
  | some
  | all
  deriving DecidableEq, Fintype

instance : MeasurableSpace Msg := ⊤

instance : DiscreteMeasurableSpace Msg := ⟨fun _ ↦ trivial⟩

instance : Nonempty Msg := ⟨.some⟩

/-- §3.1: the two states, *some but not all* and *all*, are equally likely. -/
noncomputable def pr : Measure Triangle := uniformOn ↑Triangle.corners.I

/-- §2.4.1: `L_bound` lexicalizes an upper bound for *some*. -/
def Lbound : Msg → Set Triangle
  | .some => {.IO}
  | .all => {.A}

/-- §2.4.1: `L_lack` gives *some* only a lower bound, so *some* is true at *all*. -/
def Llack : Msg → Set Triangle
  | .some => ↑Triangle.corners.I
  | .all => {.A}

/-- The success of a type communicating with itself, its fitness in a population of its own kind. -/
noncomputable def selfSuccess (lam : ℝ) (L : Msg → Set Triangle) (n : ℕ) : ℝ :=
  success pr (agents pr lam L n).1 (agents pr lam L n).2

instance : IsProbabilityMeasure pr :=
  isProbabilityMeasure_uniformOn (finite_toSet _) ⟨.IO, by decide⟩

private theorem triangle_univ : (univ : Finset Triangle) = {.E, .IO, .A} := by decide

private theorem msg_univ : (univ : Finset Msg) = {.some, .all} := by decide

private theorem pr_real (t : Triangle) :
    pr.real {t} = if t = .E then 0 else 1 / 2 := by
  rw [pr, uniformOn_finset_real_singleton]
  cases t <;> simp [Triangle.corners]

private theorem success_eq {σ : Kernel Triangle Msg} {η : Kernel Msg Triangle} :
    success pr σ η = ((σ .IO).real {.some} * (η .some).real {.IO} +
      (σ .IO).real {.all} * (η .all).real {.IO} + (σ .A).real {.some} * (η .some).real {.A} +
      (σ .A).real {.all} * (η .all).real {.A}) / 2 := by
  simp only [success, triangle_univ, msg_univ, sum_insert, mem_insert, mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, sum_singleton, pr_real, ↓reduceIte]
  ring

variable {lam : ℝ}

private theorem pragmatic_hearer_real (L : Msg → Set Triangle) (m : Msg) (s : Triangle) :
    ((agents pr lam L 1).2 m).real {s} = pr.real {s} * ((agents pr lam L 0).1 s).real {m} /
      (((agents pr lam L 0).1 .IO).real {m} / 2 + ((agents pr lam L 0).1 .A).real {m} / 2) := by
  rw [agents_succ_snd, listener_real_singleton]
  congr 1
  simp only [triangle_univ, sum_insert, mem_insert, mem_singleton, reduceCtorEq, or_self,
    not_false_eq_true, sum_singleton, pr_real, ↓reduceIte]
  ring

private theorem pr_real_I : pr.real {.IO, .A} = 1 := by
  rw [show ({.IO, .A} : Set Triangle) = ↑Triangle.corners.I by ext t; cases t <;> decide, pr,
    measureReal_def, uniformOn_self (finite_toSet _) ⟨.IO, by decide⟩, ENNReal.toReal_one]

private theorem pr_real_IO : pr.real {.IO} = 1 / 2 := by rw [pr_real]; rfl

private theorem pr_real_A : pr.real {.A} = 1 / 2 := by rw [pr_real]; rfl

private theorem S0_some (L : Msg → Set Triangle) (s : Triangle) :
    ((agents pr lam L 0).1 s).real {.some} =
      Real.sigmoid (lam * (L .some).indicator 1 s - lam * (L .all).indicator 1 s) :=
  agents_zero_fst_real_of_pair pr lam L s (by decide) fun c ↦ by cases c <;> simp

private theorem S0_all (L : Msg → Set Triangle) (s : Triangle) :
    ((agents pr lam L 0).1 s).real {.all} =
      Real.sigmoid (lam * (L .all).indicator 1 s - lam * (L .some).indicator 1 s) :=
  agents_zero_fst_real_of_pair pr lam L s (by decide) fun c ↦ by cases c <;> simp

private theorem S1_some (L : Msg → Set Triangle) (s : Triangle) :
    ((agents pr lam L 1).1 s).real {.some} = Real.sigmoid (lam *
      (((agents pr lam L 0).2 .some).real {s} - ((agents pr lam L 0).2 .all).real {s})) :=
  agents_succ_fst_real_of_pair pr lam L 0 s (by decide) fun c ↦ by cases c <;> simp

private theorem S1_all (L : Msg → Set Triangle) (s : Triangle) :
    ((agents pr lam L 1).1 s).real {.all} = Real.sigmoid (lam *
      (((agents pr lam L 0).2 .all).real {s} - ((agents pr lam L 0).2 .some).real {s})) :=
  agents_succ_fst_real_of_pair pr lam L 0 s (by decide) fun c ↦ by cases c <;> simp

open Classical in
private theorem H0_real (L : Msg → Set Triangle) (m : Msg) (s : Triangle) :
    ((agents pr lam L 0).2 m).real {s} = if s ∈ L m then pr.real {s} / pr.real (L m) else 0 :=
  agents_zero_snd_real pr lam L m s

-- §2.4.1: the literal user of `L_bound` sends the true message with chance `σ(λ)`.
theorem selfSuccess_Lbound_zero : selfSuccess lam Lbound 0 = Real.sigmoid lam := by
  rw [selfSuccess, success_eq, S0_some, S0_all, S0_some, S0_all, H0_real, H0_real, H0_real,
    H0_real]
  simp [Lbound, pr_real_IO, pr_real_A, Real.sigmoid_neg]

-- §2.4.1: the pragmatic user of `L_bound` reasons over the literal one's noise.
theorem selfSuccess_Lbound_one :
    selfSuccess lam Lbound 1 = Real.sigmoid lam ^ 2 + (1 - Real.sigmoid lam) ^ 2 := by
  rw [selfSuccess, success_eq, S1_some, S1_all, S1_some, S1_all, pragmatic_hearer_real,
    pragmatic_hearer_real, pragmatic_hearer_real, pragmatic_hearer_real]
  simp only [S0_some, S0_all, H0_real]
  simp [Lbound, pr_real_IO, pr_real_A, Real.sigmoid_neg]
  ring

-- §2.4.1: the literal user of `L_lack` cannot tell the states apart after *some*.
theorem selfSuccess_Llack_zero : selfSuccess lam Llack 0 = Real.sigmoid lam / 4 + 3 / 8 := by
  rw [selfSuccess, success_eq, S0_some, S0_all, S0_some, S0_all, H0_real, H0_real, H0_real,
    H0_real]
  simp [Llack, pr_real_IO, pr_real_A, pr_real_I, Real.sigmoid_neg, Triangle.corners]
  ring

-- §2.4.1: the pragmatic user of `L_lack`, with `σ(λ)` and `σ(λ/2)`.
theorem selfSuccess_Llack_one :
    selfSuccess lam Llack 1 =
      (Real.sigmoid (lam / 2) * Real.sigmoid lam / (Real.sigmoid lam + 1 / 2) +
        (1 - Real.sigmoid (lam / 2)) * (1 - Real.sigmoid lam) / (3 / 2 - Real.sigmoid lam) +
        (1 - Real.sigmoid (lam / 2)) * (1 / 2) / (Real.sigmoid lam + 1 / 2) +
        Real.sigmoid (lam / 2) * (1 / 2) / (3 / 2 - Real.sigmoid lam)) / 2 := by
  have hH0 (m : Msg) (t : Triangle) : ((agents pr lam Llack 0).2 m).real {t} =
      if t = .E then 0 else if m = .some then 1 / 2 else if t = .A then 1 else 0 := by
    rw [H0_real]
    cases m <;> cases t <;> simp [Llack, Triangle.corners, pr_real_IO, pr_real_A, pr_real_I]
  have hS0 (m : Msg) (t : Triangle) (ht : t ≠ .E) : ((agents pr lam Llack 0).1 t).real {m} =
      if t = .A then 1 / 2 else if m = .some then Real.sigmoid lam else 1 - Real.sigmoid lam := by
    cases m <;> cases t <;>
      simp_all [S0_some, S0_all, Llack, Triangle.corners, Real.sigmoid_neg, Real.sigmoid_zero]
  have hS1 (m : Msg) (t : Triangle) (ht : t ≠ .E) : ((agents pr lam Llack 1).1 t).real {m} =
      if (m = .some) = (t = .IO) then Real.sigmoid (lam / 2) else 1 - Real.sigmoid (lam / 2) := by
    rw [← Real.sigmoid_neg]
    cases m <;> cases t <;> simp_all [S1_some, S1_all] <;> congr 1 <;> ring
  have h₀ := Real.sigmoid_pos lam
  have h₁ := Real.sigmoid_lt_one lam
  have h₂ : Real.sigmoid lam + 1 / 2 ≠ 0 := by linarith
  have h₃ : 3 / 2 - Real.sigmoid lam ≠ 0 := by linarith
  have h₄ : 2 * Real.sigmoid lam + 1 ≠ 0 := by linarith
  have h₅ : 3 - 2 * Real.sigmoid lam ≠ 0 := by linarith
  have h₆ : 3 - Real.sigmoid lam * 2 ≠ 0 := by linarith
  have h₇ : Real.sigmoid lam * 2 + 1 ≠ 0 := by linarith
  rw [selfSuccess, success_eq, pragmatic_hearer_real, pragmatic_hearer_real,
    pragmatic_hearer_real, pragmatic_hearer_real]
  simp only [hS1 _ _ (by decide : Triangle.IO ≠ .E), hS1 _ _ (by decide : Triangle.A ≠ .E),
    hS0 _ _ (by decide : Triangle.IO ≠ .E), hS0 _ _ (by decide : Triangle.A ≠ .E), pr_real_IO,
    pr_real_A]
  simp only [reduceCtorEq, ↓reduceIte, eq_iff_iff, iff_true, iff_false, not_true_eq_false]
  field_simp
  ring

private theorem sigmoid_eq_exp_half (lam : ℝ) :
    Real.sigmoid lam = Real.exp (lam / 2) ^ 2 / (Real.exp (lam / 2) ^ 2 + 1) ∧
      Real.sigmoid (lam / 2) = Real.exp (lam / 2) / (Real.exp (lam / 2) + 1) := by
  have h : Real.exp (lam / 2) ^ 2 = Real.exp lam := by rw [← Real.exp_nat_mul]; ring_nf
  have hpos := Real.exp_pos (lam / 2)
  refine ⟨?_, ?_⟩ <;> rw [Real.sigmoid_def, Real.exp_neg] <;> field_simp
  rw [h]
  field_simp

private theorem half_add_sq_div (u : ℝ) :
    u ^ 2 / (u ^ 2 + 1) + 1 / 2 = (3 * u ^ 2 + 1) / (2 * (u ^ 2 + 1)) := by
  have : u ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem three_halves_sub_sq_div (u : ℝ) :
    3 / 2 - u ^ 2 / (u ^ 2 + 1) = (u ^ 2 + 3) / (2 * (u ^ 2 + 1)) := by
  have : u ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem one_sub_div_self {u : ℝ} (h : u + 1 ≠ 0) : 1 - u / (u + 1) = 1 / (u + 1) := by
  field_simp
  ring

private theorem half_lt_sigmoid {lam : ℝ} (h : 0 < lam) : 1 / 2 < Real.sigmoid lam := by
  simpa [Real.sigmoid_zero] using Real.sigmoid_lt h

private theorem sigmoid_log_five_thirds : Real.sigmoid (Real.log (5 / 3)) = 5 / 8 := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

-- The pragmatic user of `L_lack` against the pragmatic user of `L_bound`, through `u = e^(λ/2)`.
private theorem selfSuccess_Lbound_one_sub_Llack_one (lam : ℝ) :
    selfSuccess lam Lbound 1 - selfSuccess lam Llack 1 =
      (Real.exp (lam / 2) - 1) ^ 2 * (Real.exp (lam / 2) ^ 6 + 6 * Real.exp (lam / 2) ^ 5 +
        7 * Real.exp (lam / 2) ^ 4 + 20 * Real.exp (lam / 2) ^ 3 + 7 * Real.exp (lam / 2) ^ 2 +
        6 * Real.exp (lam / 2) + 1) / (2 * (Real.exp (lam / 2) ^ 2 + 1) ^ 2 *
        (Real.exp (lam / 2) ^ 2 + 3) * (3 * Real.exp (lam / 2) ^ 2 + 1)) := by
  obtain ⟨h₁, h₂⟩ := sigmoid_eq_exp_half lam
  rw [selfSuccess_Lbound_one, selfSuccess_Llack_one, h₁, h₂]
  have hu := Real.exp_pos (lam / 2)
  generalize Real.exp (lam / 2) = u at hu ⊢
  rw [half_add_sq_div, three_halves_sub_sq_div, one_sub_div_self (u := u ^ 2) (by positivity),
    one_sub_div_self (u := u) (by positivity)]
  have : u + 1 ≠ 0 := by positivity
  have : 3 * u ^ 2 + 1 ≠ 0 := by positivity
  have : u ^ 2 + 3 ≠ 0 := by positivity
  field_simp
  ring

-- The literal user of `L_lack` against the pragmatic one, through `u = e^(λ/2)`.
private theorem selfSuccess_Llack_zero_sub_Llack_one (lam : ℝ) :
    selfSuccess lam Llack 0 - selfSuccess lam Llack 1 =
      -(Real.exp (lam / 2) - 1) * (5 * Real.exp (lam / 2) ^ 5 - 11 * Real.exp (lam / 2) ^ 4 +
        6 * Real.exp (lam / 2) ^ 3 - 26 * Real.exp (lam / 2) ^ 2 + 5 * Real.exp (lam / 2) - 11) /
        (8 * (Real.exp (lam / 2) ^ 2 + 1) * (Real.exp (lam / 2) ^ 2 + 3) *
        (3 * Real.exp (lam / 2) ^ 2 + 1)) := by
  obtain ⟨h₁, h₂⟩ := sigmoid_eq_exp_half lam
  rw [selfSuccess_Llack_zero, selfSuccess_Llack_one, h₁, h₂]
  have hu := Real.exp_pos (lam / 2)
  generalize Real.exp (lam / 2) = u at hu ⊢
  rw [half_add_sq_div, three_halves_sub_sq_div, one_sub_div_self (u := u ^ 2) (by positivity),
    one_sub_div_self (u := u) (by positivity)]
  have : u + 1 ≠ 0 := by positivity
  have : 3 * u ^ 2 + 1 ≠ 0 := by positivity
  have : u ^ 2 + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- §3.1 (p. 2768): literal `L_bound` communicates better with its own kind than pragmatic
`L_bound` does, which gains nothing from reasoning over a lexicon with an upper bound, and better
than literal `L_lack`, whose *some* is ambiguous; and pragmatic `L_bound` communicates better than
pragmatic `L_lack`. These hold at every rationality. -/
theorem selfSuccess_lt (hlam : 0 < lam) :
    selfSuccess lam Lbound 1 < selfSuccess lam Lbound 0 ∧
      selfSuccess lam Llack 0 < selfSuccess lam Lbound 0 ∧
      selfSuccess lam Llack 1 < selfSuccess lam Lbound 1 := by
  have h₁ := half_lt_sigmoid hlam
  have h₂ := Real.sigmoid_lt_one lam
  refine ⟨?_, ?_, ?_⟩
  · rw [selfSuccess_Lbound_one, selfSuccess_Lbound_zero]
    nlinarith
  · rw [selfSuccess_Llack_zero, selfSuccess_Lbound_zero]
    linarith
  · rw [← sub_pos, selfSuccess_Lbound_one_sub_Llack_one]
    have hu := Real.one_lt_exp_iff.2 (half_pos hlam)
    have hu' := hu.trans' one_pos
    refine div_pos (mul_pos (pow_pos (sub_pos.2 hu) 2) (by positivity)) (by positivity)

/-- §3.1 (p. 2768) claims that every other type communicates better than literal `L_lack`. With
pragmatic `L_bound` this holds exactly when `λ > log(5/3)`, and pragmatic `L_lack` does worse than
literal `L_lack` whenever `λ ≤ 2 log(5/2)`, as at the paper's `λ = 1`. -/
theorem selfSuccess_Llack_zero_lt (hlam : 0 < lam) :
    (selfSuccess lam Llack 0 < selfSuccess lam Lbound 1 ↔ Real.log (5 / 3) < lam) ∧
      (lam ≤ 2 * Real.log (5 / 2) → selfSuccess lam Llack 1 < selfSuccess lam Llack 0) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · have key : Real.log (5 / 3) < lam ↔ 5 / 8 < Real.sigmoid lam := by
      rw [← sigmoid_log_five_thirds, Real.sigmoid_lt_iff]
    rw [selfSuccess_Llack_zero, selfSuccess_Lbound_one, key]
    have h₁ := half_lt_sigmoid hlam
    constructor <;> intro h <;> nlinarith
  · rw [← sub_pos, selfSuccess_Llack_zero_sub_Llack_one]
    have hu := Real.one_lt_exp_iff.2 (half_pos hlam)
    have hu' : Real.exp (lam / 2) ≤ 5 / 2 := by
      calc Real.exp (lam / 2) ≤ Real.exp (Real.log (5 / 2)) := Real.exp_le_exp.2 (by linarith)
        _ = 5 / 2 := Real.exp_log (by norm_num)
    set u := Real.exp (lam / 2)
    have hP : 5 * u ^ 5 - 11 * u ^ 4 + 6 * u ^ 3 - 26 * u ^ 2 + 5 * u - 11 < 0 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hu.le) (sub_nonneg.2 hu'),
        mul_nonneg (mul_nonneg (sub_nonneg.2 hu.le) (sub_nonneg.2 hu')) (sub_nonneg.2 hu.le),
        sq_nonneg (u - 2), mul_nonneg (sub_nonneg.2 hu.le) (sq_nonneg (u - 2))]
    refine div_pos ?_ (by positivity)
    nlinarith [sub_pos.2 hu]

-- At high rationality the order reverses: at the `λ = 20` of §2.4.1, pragmatic `L_lack`
-- communicates better than literal `L_lack`.
example : selfSuccess 20 Llack 0 < selfSuccess 20 Llack 1 := by
  rw [← sub_neg, selfSuccess_Llack_zero_sub_Llack_one]
  have hu : (3 : ℝ) ≤ Real.exp (20 / 2) := by
    linarith [Real.add_one_le_exp (20 / 2 : ℝ)]
  set u := Real.exp (20 / 2)
  have hP : 0 < 5 * u ^ 5 - 11 * u ^ 4 + 6 * u ^ 3 - 26 * u ^ 2 + 5 * u - 11 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu), pow_le_pow_left₀ (by norm_num) hu 4]
  refine div_neg_of_neg_of_pos ?_ (by positivity)
  nlinarith

/-! ### Mutation alone on the four types of §3.1

A type pairs one of the two lexica with a reasoning level, `0` for literal and `1` for pragmatic
use. A type's data are `k` states drawn from the prior, each with the message the type sends
there. -/

/-- The two lexica of §3.1. -/
inductive Lex
  | bound
  | lack
  deriving DecidableEq, Fintype

namespace Lex

instance : MeasurableSpace Lex := ⊤

instance : DiscreteMeasurableSpace Lex := ⟨fun _ ↦ trivial⟩

instance : Nonempty Lex := ⟨.lack⟩

/-- The lexicon a name stands for. -/
def denote : Lex → Msg → Set Triangle
  | bound => Lbound
  | lack => Llack

end Lex

/-- §2.4.3: the chance that a type produces a sequence of `k` state-message pairs. -/
noncomputable def produce (lam : ℝ) (k : ℕ) : Kernel (Lex × Fin 2) (Fin k → Triangle × Msg) :=
  Kernel.ofFunOfCountable fun t ↦ Measure.pi fun _ ↦ pr ⊗ₘ (agents pr lam t.1.denote t.2).1

instance (k : ℕ) : IsMarkovKernel (produce lam k) :=
  ⟨fun t ↦ by rw [produce, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- Fig. 2: the prior over types favouring those with `L_lack` by a factor `c`. -/
noncomputable def biasedPrior (c : ℝ≥0) : Measure (Lex × Fin 2) :=
  Measure.ofRealWeights fun t ↦ (if t.1 = .lack then (c : ℝ) else 1) / (2 * (c + 1))

private theorem lex_univ : (univ : Finset Lex) = {.bound, .lack} := by decide

private theorem biasedPrior_real_singleton (c : ℝ≥0) (t : Lex × Fin 2) :
    (biasedPrior c).real {t} = (if t.1 = .lack then (c : ℝ) else 1) / (2 * (c + 1)) :=
  Measure.ofRealWeights_real_singleton (fun t ↦ by positivity) t

instance (c : ℝ≥0) : IsProbabilityMeasure (biasedPrior c) := by
  refine Measure.isProbabilityMeasure_ofRealWeights (fun t ↦ by positivity) ?_
  rw [Fintype.sum_prod_type, lex_univ, sum_pair (by decide)]
  simp only [Fin.sum_univ_two, ↓reduceIte, reduceCtorEq]
  field_simp
  ring

private theorem biasedPrior_real_lex (c : ℝ≥0) (x : Lex) :
    (biasedPrior c).real {t | t.1 = x} = (if x = .lack then (c : ℝ) else 1) / (c + 1) := by
  have : {t : Lex × Fin 2 | t.1 = x} = ↑({(x, 0), (x, 1)} : Finset (Lex × Fin 2)) := by
    ext t; obtain ⟨y, i⟩ := t; fin_cases i <;> simp [eq_comm]
  rw [this, ← sum_measureReal_singleton, sum_pair (by simp), biasedPrior_real_singleton,
    biasedPrior_real_singleton]
  field_simp
  ring

/-- §3.1 (p. 2770), Fig. 2(b): learners who sample from the posterior (`l = 1`) keep the prior
[griffiths-kalish-2007], so a population under mutation alone settles where users of `L_lack`
outnumber users of `L_bound` by the factor by which the prior favours them, `1.05` in Fig. 2. -/
theorem invariant_biasedPrior (k : ℕ) (c : ℝ≥0) :
    (exponentiatedPosterior (produce lam k) (biasedPrior c) 1 ∘ₖ produce lam k).Invariant
      (biasedPrior c) ∧
      (biasedPrior c).real {t | t.1 = .lack} / (biasedPrior c).real {t | t.1 = .bound} = c := by
  refine ⟨invariant_exponentiatedPosterior_one _ _, ?_⟩
  rw [biasedPrior_real_lex, biasedPrior_real_lex]
  simp only [↓reduceIte, reduceCtorEq]
  field_simp

example : (biasedPrior 1.05).real {t | t.1 = .lack} / (biasedPrior 1.05).real {t | t.1 = .bound} =
    1.05 := by
  rw [(invariant_biasedPrior (lam := 0) 0 1.05).2]
  norm_num

end TwoStates

/-! ### Three states: the lexica of §3.2

The states are the three vertices of the triangle of opposition, *none* (`Triangle.E`), *some but
not all* (`Triangle.IO`) and *all* (`Triangle.A`), equally likely, and a lexicon sends each of
three messages to a set of states. -/

section ThreeStates

open Aristotelian.Triangle (corners)

/-- §3.2.1: a lexical representation, a set of states other than the empty and the full one. -/
abbrev Representation := {r : Finset Triangle // r ≠ ∅ ∧ r ≠ univ}

-- §3.2.1: six representations, `6³ = 216` lexica and `432` types.
theorem card_types : Fintype.card Representation = 6 ∧ Fintype.card (Fin 3 → Representation) = 216 ∧
    Fintype.card ((Fin 3 → Representation) × Fin 2) = 432 := by
  have h : Fintype.card Representation = 6 := by decide
  simp [Fintype.card_prod, h]

/-- Table 2: the least cost of a formula of the grammar of Table 1 that expresses each
representation, as printed. -/
def complexity (r : Finset Triangle) : ℕ :=
  if r = corners.A then 3 else if r = corners.I ⊓ corners.O then 8 else if r = corners.I then 4
  else if r = corners.E then 4 else if r = corners.E ⊔ corners.A then 10
  else if r = corners.O then 5 else 0

/-- §3.2.2: the greatest complexity of a representation. -/
def maxComplexity : ℕ := univ.sup fun r : Representation ↦ complexity r

/-- §3.2.2: a representation's prior, proportional to one more than the amount by which its
complexity falls short of the greatest. -/
noncomputable def reprPrior (r : Representation) : ℝ :=
  (maxComplexity + 1 - complexity r : ℕ) /
    ∑ r' : Representation, ((maxComplexity + 1 - complexity r' : ℕ) : ℝ)

/-- §3.2.2: the prior of a lexicon, up to normalization, the product of the priors of the
representations it uses. -/
noncomputable def lexiconWeight (L : Fin 3 → Representation) : ℝ :=
  ∏ r ∈ univ.image L, reprPrior r

/-- *None*. -/
def none : Representation := ⟨corners.E, by decide⟩
/-- *Some*. -/
def some : Representation := ⟨corners.I, by decide⟩
/-- *All*. -/
def all : Representation := ⟨corners.A, by decide⟩
/-- *Not all*. -/
def notAll : Representation := ⟨corners.O, by decide⟩
/-- *Some but not all*. -/
def someNotAll : Representation := ⟨corners.I ⊓ corners.O, by decide⟩

private theorem complexity_eq :
    complexity none = 4 ∧ complexity some = 4 ∧ complexity all = 3 ∧ complexity notAll = 5 ∧
      complexity someNotAll = 8 := by
  decide

private theorem reprPrior_eq (r : Representation) :
    reprPrior r = (11 - complexity r : ℕ) / 32 := by
  have h₁ : maxComplexity = 10 := by decide
  have h₂ : ∑ r' : Representation, (maxComplexity + 1 - complexity r' : ℕ) = 32 := by decide
  rw [reprPrior, ← Nat.cast_sum, h₂, h₁]
  norm_num

/-- §3.2.1: a lexicon that leaves the upper bound of *some* to pragmatics. -/
def lexLack : Fin 3 → Representation := ![none, some, all]

/-- §3.2.1: a lexicon that lexicalizes the upper bound of *some*. -/
def lexBound : Fin 3 → Representation := ![none, someNotAll, all]

/-- §3.2.1: a lexicon that uses *all* for every message. -/
def lexAll : Fin 3 → Representation := fun _ ↦ all

/-- The mirror image of `lexLack`, which leaves the lower bound of *not all* to pragmatics. -/
def lexMirror : Fin 3 → Representation := ![all, notAll, none]

-- §3.2.2 (p. 2773): the prior favours `lexAll` over `lexLack` over `lexBound`.
theorem lexiconWeight_lt : lexiconWeight lexBound < lexiconWeight lexLack ∧
    lexiconWeight lexLack < lexiconWeight lexAll := by
  have hB : univ.image lexBound = {none, someNotAll, all} := by decide
  have hL : univ.image lexLack = {none, some, all} := by decide
  have hA : univ.image lexAll = {all} := by decide
  simp only [lexiconWeight, hB, hL, hA,
    prod_insert (by decide : none ∉ ({someNotAll, all} : Finset _)),
    prod_insert (by decide : none ∉ ({some, all} : Finset _)),
    prod_insert (by decide : someNotAll ∉ ({all} : Finset _)),
    prod_insert (by decide : some ∉ ({all} : Finset _)), prod_singleton, reprPrior_eq]
  obtain ⟨h₁, h₂, h₃, -, h₅⟩ := complexity_eq
  rw [h₁, h₂, h₃, h₅]
  norm_num

-- §3.2.2 (p. 2773): no lexicon is likelier a priori than `lexAll`.
theorem lexiconWeight_le_lexAll (L : Fin 3 → Representation) :
    lexiconWeight L ≤ lexiconWeight lexAll := by
  have hA : lexiconWeight lexAll = 1 / 4 := by
    rw [lexiconWeight, show univ.image lexAll = {all} by decide, prod_singleton, reprPrior_eq,
      complexity_eq.2.2.1]
    norm_num
  have h₃ : ∀ r : Representation, 3 ≤ complexity r := by decide
  have h₀ : ∀ r, 0 ≤ reprPrior r := fun r ↦ by rw [reprPrior_eq]; positivity
  have h₄ : ∀ r, reprPrior r ≤ 1 / 4 := fun r ↦ by
    rw [reprPrior_eq, div_le_iff₀ (by norm_num)]
    have := h₃ r
    have : ((11 - complexity r : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (by omega)
    linarith
  obtain ⟨r, hr⟩ : (univ.image L).Nonempty := univ_nonempty.image L
  rw [hA, lexiconWeight, ← mul_prod_erase _ _ hr]
  calc reprPrior r * ∏ r' ∈ (univ.image L).erase r, reprPrior r' ≤ reprPrior r * 1 :=
        mul_le_mul_of_nonneg_left
          (prod_le_one₀ (fun r' _ ↦ h₀ r') fun r' _ ↦ (h₄ r').trans (by norm_num)) (h₀ r)
    _ ≤ 1 / 4 := by linarith [h₄ r]

-- Table 2 (p. 2773), erratum: the formula printed for *some but not all* expresses *some*.
example {α : Type*} (A B : Set α) : (A ∩ B).Nonempty ∧ A.Nonempty ↔ (A ∩ B).Nonempty :=
  ⟨And.left, fun h ↦ ⟨h, h.mono Set.inter_subset_left⟩⟩

/-- The flat prior over the three states. -/
noncomputable def flat : Measure Triangle := uniformOn Set.univ

/-- A lexicon's denotations. -/
def denote (L : Fin 3 → Representation) (m : Fin 3) : Set Triangle := ↑(L m).1

-- The order-reversing permutation of the states, which swaps *none* and *all*, takes `lexLack`
-- to `lexMirror`. The flat prior is symmetric under it, so `lexMirror` communicates with every
-- type as `lexLack` does at every level and rationality; only the prior separates them, 7 : 6.
theorem success_lexMirror (lam : ℝ) (L : Fin 3 → Set Triangle) (n n' : ℕ) :
    success flat (agents flat lam (denote lexMirror) n).1
        (agents flat lam (fun m ↦ Equiv.swap .E .A '' L m) n').2 =
      success flat (agents flat lam (denote lexLack) n).1 (agents flat lam L n').2 ∧
      lexiconWeight lexLack = 7 / 6 * lexiconWeight lexMirror := by
  have he : denote lexMirror = fun m ↦ Equiv.swap .E .A '' denote lexLack m := by
    funext m
    rw [denote, denote, ← Equiv.coe_toEmbedding, ← Finset.coe_map, Finset.coe_inj]
    fin_cases m <;> decide
  refine ⟨he ▸ success_image flat lam _ L _ (fun s ↦ uniformOn_univ_singleton_eq _ _) n n', ?_⟩
  have hM : univ.image lexMirror = {all, notAll, none} := by decide
  have hL : univ.image lexLack = {none, some, all} := by decide
  simp only [lexiconWeight, hM, hL, prod_insert (by decide : none ∉ ({some, all} : Finset _)),
    prod_insert (by decide : all ∉ ({notAll, none} : Finset _)),
    prod_insert (by decide : some ∉ ({all} : Finset _)),
    prod_insert (by decide : notAll ∉ ({none} : Finset _)), prod_singleton, reprPrior_eq]
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := complexity_eq
  rw [h₁, h₂, h₃, h₄]
  norm_num

end ThreeStates

/-! ### The replicator mutator dynamic

A population is a probability measure over types. The replicator step reweights each type by its
fitness, and the mutator step passes the result through the kernel `Q` that sends a teacher's type
to the type its learners acquire. -/

section Replicator

variable {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

/-- §2.4.2: the fitness of a type, its expected payoff `U` against a member of the population. -/
noncomputable def fitness (U : T → T → ℝ) (x : Measure T) (i : T) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ j, x.real {j} * U i j)

/-- Eq. (2): the replicator step, which reweights each type by its fitness. -/
noncomputable def replicator (f : T → ℝ≥0∞) (x : Measure T) : Measure T :=
  (x.withDensity f)[|Set.univ]

/-- Eqs. (1)–(2): the replicator mutator step. -/
noncomputable def rmd (Q : Kernel T T) (f : T → ℝ≥0∞) (x : Measure T) : Measure T :=
  Q ∘ₘ replicator f x

instance (f : T → ℝ≥0∞) (x : Measure T) : IsFiniteMeasure (replicator f x) :=
  inferInstanceAs (IsFiniteMeasure ((x.withDensity f)[|Set.univ]))

theorem replicator_apply_singleton (f : T → ℝ≥0∞) (x : Measure T) (i : T) :
    replicator f x {i} = (∑ k, f k * x {k})⁻¹ * (f i * x {i}) := by
  rw [replicator, cond_apply .univ, Set.univ_inter, withDensity_apply _ .univ,
    withDensity_apply _ (measurableSet_singleton i), Measure.restrict_univ, lintegral_fintype,
    lintegral_singleton]

theorem replicator_real_singleton (f : T → ℝ≥0∞) (hf : ∀ i, f i ≠ ⊤) (x : Measure T)
    [IsFiniteMeasure x] (i : T) :
    (replicator f x).real {i} = (f i).toReal * x.real {i} / ∑ k, (f k).toReal * x.real {k} := by
  rw [measureReal_def, replicator_apply_singleton, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sum fun k _ ↦ ENNReal.mul_ne_top (hf k) (measure_ne_top _ _),
    ENNReal.toReal_mul, inv_mul_eq_div]
  simp only [ENNReal.toReal_mul, measureReal_def]

omit [Fintype T] [MeasurableSingletonClass T] in
-- p. 2761: without mutation the dynamic is the replicator dynamic.
theorem rmd_id (f : T → ℝ≥0∞) (x : Measure T) : rmd Kernel.id f x = replicator f x :=
  Measure.id_comp

-- p. 2761: under equal fitness the dynamic is iterated mutation.
theorem rmd_const (Q : Kernel T T) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) (x : Measure T)
    [IsProbabilityMeasure x] : rmd Q (fun _ ↦ c) x = Q ∘ₘ x := by
  have : replicator (fun _ ↦ c) x = x := Measure.ext_of_singleton fun i ↦ by
    rw [replicator_apply_singleton, ← mul_sum, sum_measure_singleton, coe_univ, measure_univ,
      mul_one, ← mul_assoc, ENNReal.inv_mul_cancel hc hc', one_mul]
  rw [rmd, this]

end Replicator

/-! #### Appendix A: a coordination game

Two types of agent, negative and positive, earn `1` when two negatives meet, `2` when two
positives meet, and `0` otherwise. A tenth of the learners of each type acquire the other. -/

section AppendixA

/-- App. A: the two types of the coordination game. -/
inductive Sign
  | negative
  | positive
  deriving DecidableEq, Fintype

namespace Sign

instance : MeasurableSpace Sign := ⊤

instance : DiscreteMeasurableSpace Sign := ⟨fun _ ↦ trivial⟩

/-- App. A: the payoffs of the coordination game. -/
def payoff : Sign → Sign → ℝ
  | negative, negative => 1
  | positive, positive => 2
  | _, _ => 0

/-- App. A: the mutation that keeps a type with chance `0.9`. -/
noncomputable def mutation : Kernel Sign Sign :=
  Kernel.ofFunOfCountable fun j ↦ Measure.ofRealWeights fun i ↦ if i = j then 0.9 else 0.1

theorem univ_eq : (univ : Finset Sign) = {negative, positive} := by decide

end Sign

open Sign

private theorem mutation_real_negative (j : Sign) :
    (mutation j).real {negative} = if negative = j then 0.9 else 0.1 := by
  rw [mutation, Kernel.ofFunOfCountable_apply,
    Measure.ofRealWeights_real_singleton (fun i ↦ by split_ifs <;> norm_num)]

instance : IsMarkovKernel mutation :=
  ⟨fun j ↦ by
    rw [mutation, Kernel.ofFunOfCountable_apply]
    refine Measure.isProbabilityMeasure_ofRealWeights (fun i ↦ by split_ifs <;> norm_num) ?_
    cases j <;> simp [univ_eq] <;> norm_num⟩

private theorem real_positive (x : Measure Sign) [IsProbabilityMeasure x] :
    x.real {positive} = 1 - x.real {negative} := by
  have : x.real {negative} + x.real {positive} = 1 :=
    measureReal_singleton_add_singleton_of_pair x (by decide) fun i _ ↦ by cases i <;> simp
  linarith

private theorem replicator_real (x : Measure Sign) [IsProbabilityMeasure x] (i : Sign) :
    (replicator (fitness payoff x) x).real {i} =
      (if i = negative then x.real {negative} ^ 2 else 2 * (1 - x.real {negative}) ^ 2) /
        (3 * x.real {negative} ^ 2 - 4 * x.real {negative} + 2) := by
  have h₀ := measureReal_nonneg (μ := x) (s := {negative})
  have h₁ : x.real {negative} ≤ 1 := measureReal_le_one
  have hp := real_positive x
  rw [replicator_real_singleton (fitness payoff x) (fun _ ↦ ENNReal.ofReal_ne_top), univ_eq,
    sum_pair (by decide)]
  cases i <;>
    simp only [fitness, univ_eq, sum_pair (by decide : negative ≠ positive), payoff, hp,
      ↓reduceIte, reduceCtorEq] <;>
    rw [ENNReal.toReal_ofReal (by nlinarith), ENNReal.toReal_ofReal (by nlinarith)] <;>
    congr 1 <;> ring

-- App. A (p. 2788): the replicator step alone rests at the shares `0`, `2/3` and `1` of
-- negatives.
theorem replicator_real_negative_eq_iff (x : Measure Sign) [IsProbabilityMeasure x] :
    (replicator (fitness payoff x) x).real {negative} = x.real {negative} ↔
      x.real {negative} = 0 ∨ x.real {negative} = 2 / 3 ∨ x.real {negative} = 1 := by
  rw [replicator_real]
  simp only [↓reduceIte]
  set a := x.real {negative}
  have hΦ : 3 * a ^ 2 - 4 * a + 2 ≠ 0 := by nlinarith [sq_nonneg (a - 2 / 3)]
  rw [div_eq_iff hΦ]
  constructor
  · intro h
    have : a * (a - 1) * (3 * a - 2) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact .inl h
      · exact .inr (.inr (by linarith))
    · exact .inr (.inl (by linarith))
  · rintro (h | h | h) <;> rw [h] <;> ring

-- App. A (p. 2788), erratum: the replicator mutator step sends the share `x` of negatives to
-- `(1.1x² - 0.4x + 0.2) / (3x² - 4x + 2)`, not to the printed `(0.9x² - 0.2x + 0.2) / ⋯`.
theorem rmd_real_negative (x : Measure Sign) [IsProbabilityMeasure x] :
    (rmd mutation (fitness payoff x) x).real {negative} =
      (1.1 * x.real {negative} ^ 2 - 0.4 * x.real {negative} + 0.2) /
        (3 * x.real {negative} ^ 2 - 4 * x.real {negative} + 2) := by
  rw [rmd, Measure.comp_real_singleton, univ_eq, sum_pair (by decide), mutation_real_negative,
    mutation_real_negative, replicator_real, replicator_real]
  set a := x.real {negative}
  have hΦ : 3 * a ^ 2 - 4 * a + 2 ≠ 0 := by nlinarith [sq_nonneg (a - 2 / 3)]
  simp only [↓reduceIte, reduceCtorEq]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  congr 1
  ring

end AppendixA

/-! ### Appendix B: mutation that favours the type the others are mistaken for

Three equally likely types produce three data. Type `t₁` produces its own datum `d₁` with chance
`1 - 2ε`; types `t₂` and `t₃` produce theirs with chance `1 - (ε + δ)` and `d₁` with chance `δ`. -/

section AppendixB

variable {ε δ : ℝ}

/-- App. B: the chance `LH i j` that type `tᵢ` produces datum `dⱼ`. -/
def lhWeight (ε δ : ℝ) (i j : Fin 3) : ℝ :=
  if i = j then (if i = 0 then 1 - 2 * ε else 1 - (ε + δ)) else if j = 0 then δ else ε

/-- App. B: the production likelihood `LH`. -/
noncomputable def lh (ε δ : ℝ) : Kernel (Fin 3) (Fin 3) :=
  Kernel.ofFunOfCountable fun i ↦ Measure.ofRealWeights (lhWeight ε δ i)

/-- App. B: the population `(δ, ε, ε) / (δ + 2ε)` over the three types. -/
noncomputable def lhStationary (ε δ : ℝ) : Measure (Fin 3) :=
  Measure.ofRealWeights fun i ↦ (if i = 0 then δ else ε) / (δ + 2 * ε)

private theorem lhWeight_nonneg (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) (i j : Fin 3) :
    0 ≤ lhWeight ε δ i j := by
  unfold lhWeight
  split_ifs <;> linarith

private theorem lh_apply_singleton (i j : Fin 3) :
    lh ε δ i {j} = ENNReal.ofReal (lhWeight ε δ i j) := by
  rw [lh, Kernel.ofFunOfCountable_apply, Measure.ofRealWeights, Measure.ofWeights_apply_singleton]

theorem isMarkovKernel_lh (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) :
    IsMarkovKernel (lh ε δ) := by
  refine ⟨fun i ↦ ?_⟩
  rw [lh, Kernel.ofFunOfCountable_apply]
  refine Measure.isProbabilityMeasure_ofRealWeights (lhWeight_nonneg hε hδ h i) ?_
  fin_cases i <;> simp [Fin.sum_univ_three, lhWeight] <;> ring

private theorem lh_real_singleton (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) (i j : Fin 3) :
    (lh ε δ i).real {j} = lhWeight ε δ i j := by
  rw [measureReal_def, lh_apply_singleton, ENNReal.toReal_ofReal (lhWeight_nonneg hε hδ h i j)]

-- App. B: when `δ + 2ε < 1`, every datum is likeliest under its own type, so the MAP learner
-- adopts the type whose datum it saw.
theorem mapLearner_lh (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) :
    mapLearner (lh ε δ) (uniformOn Set.univ) = Kernel.id := by
  refine Kernel.ext fun d ↦ ?_
  have : (univ.argmax fun i ↦ uniformOn Set.univ {i} * lh ε δ i {d}) = {d} := by
    refine argmax_eq_singleton_iff.2 ⟨mem_univ _, fun i _ hi ↦ ?_⟩
    simp only [uniformOn_univ_apply_singleton, lh_apply_singleton]
    refine ENNReal.mul_lt_mul_right (by simp) (by simp) <| (ENNReal.ofReal_lt_ofReal_iff ?_).2 ?_
    · fin_cases d <;> simp [lhWeight] <;> linarith
    · fin_cases i <;> fin_cases d <;> simp_all [lhWeight] <;> linarith
  rw [mapLearner_apply, this, Kernel.id_apply, coe_singleton]
  refine Measure.ext_of_singleton fun i ↦ ?_
  simp [uniformOn_singleton, Pi.single_apply]

theorem isProbabilityMeasure_lhStationary (hε : 0 < ε) (hδ : 0 ≤ δ) :
    IsProbabilityMeasure (lhStationary ε δ) := by
  refine Measure.isProbabilityMeasure_ofRealWeights (fun i ↦ by positivity) ?_
  simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  field_simp
  ring

private theorem lhStationary_real_singleton (hε : 0 < ε) (hδ : 0 ≤ δ) (i : Fin 3) :
    (lhStationary ε δ).real {i} = (if i = 0 then δ else ε) / (δ + 2 * ε) :=
  Measure.ofRealWeights_real_singleton (fun i ↦ by positivity) i

private theorem real_add_three (ν : Measure (Fin 3)) [IsProbabilityMeasure ν] :
    ν.real {0} + ν.real {1} + ν.real {2} = 1 := by
  have := sum_measureReal_singleton (μ := ν) (univ : Finset (Fin 3))
  rwa [Fin.sum_univ_three, coe_univ, probReal_univ] at this

private theorem ext_of_real {μ ν : Measure (Fin 3)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ i, μ.real {i} = ν.real {i}) : μ = ν :=
  Measure.ext_of_singleton fun i ↦
    (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1 (h i)

-- App. B: the chain `LH` keeps exactly the population `(δ, ε, ε) / (δ + 2ε)`.
theorem invariant_lh_iff (hε : 0 < ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) (ν : Measure (Fin 3))
    [IsProbabilityMeasure ν] : (lh ε δ).Invariant ν ↔ ν = lhStationary ε δ := by
  have := isMarkovKernel_lh hε.le hδ h
  have := isProbabilityMeasure_lhStationary hε hδ
  have hcomp (ν : Measure (Fin 3)) [IsProbabilityMeasure ν] (j : Fin 3) :
      (lh ε δ ∘ₘ ν).real {j} = ν.real {0} * lhWeight ε δ 0 j + ν.real {1} * lhWeight ε δ 1 j +
        ν.real {2} * lhWeight ε δ 2 j := by
    rw [Measure.comp_real_singleton, Fin.sum_univ_three, lh_real_singleton hε.le hδ h,
      lh_real_singleton hε.le hδ h, lh_real_singleton hε.le hδ h]
  have hpos : δ + 2 * ε ≠ 0 := by linarith
  refine ⟨fun hν ↦ ext_of_real fun i ↦ ?_, ?_⟩
  · have hsum := real_add_three ν
    have h₀ := hcomp ν 0
    have h₁ := hcomp ν 1
    have h₂ := hcomp ν 2
    rw [hν.def] at h₀ h₁ h₂
    simp only [lhWeight, Fin.isValue, ↓reduceIte, Fin.reduceEq] at h₀ h₁ h₂
    rw [lhStationary_real_singleton hε hδ, eq_div_iff hpos]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      linear_combination δ * hsum + h₀
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      linear_combination ε * hsum + h₁
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      linear_combination ε * hsum + h₂
  · rintro rfl
    refine ext_of_real fun j ↦ ?_
    rw [hcomp, lhStationary_real_singleton hε hδ, lhStationary_real_singleton hε hδ,
      lhStationary_real_singleton hε hδ, lhStationary_real_singleton hε hδ]
    fin_cases j <;> simp [lhWeight] <;> field_simp <;> ring

/-- App. B (p. 2789): learners who sample from the posterior (`l = 1`) keep the flat prior, while
learners who adopt the likeliest type learn `LH` itself, whose only stationary population is
`(δ, ε, ε) / (δ + 2ε)`. This population favours `t₁` exactly when `δ > ε`. -/
theorem invariant_mapLearner_comp_lh_iff (hε : 0 < ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1)
    (ν : Measure (Fin 3)) [IsProbabilityMeasure ν] :
    letI := isMarkovKernel_lh hε.le hδ h
    (exponentiatedPosterior (lh ε δ) (uniformOn Set.univ) 1 ∘ₖ lh ε δ).Invariant
      (uniformOn Set.univ) ∧
      ((mapLearner (lh ε δ) (uniformOn Set.univ) ∘ₖ lh ε δ).Invariant ν ↔
        ν = lhStationary ε δ) ∧
      ((lhStationary ε δ).real {1} < (lhStationary ε δ).real {0} ↔ ε < δ) := by
  have := isMarkovKernel_lh hε.le hδ h
  refine ⟨invariant_exponentiatedPosterior_one _ _, ?_, ?_⟩
  · rw [mapLearner_lh hε.le hδ h, Kernel.id_comp]
    exact invariant_lh_iff hε hδ h ν
  · rw [lhStationary_real_singleton hε hδ, lhStationary_real_singleton hε hδ]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
    exact div_lt_div_iff_of_pos_right (by linarith)

-- App. B: at `ε = 0.1`, `δ = 0.2` the population is `⟨0.5, 0.25, 0.25⟩`.
example : (lhStationary 0.1 0.2).real {0} = 1 / 2 ∧ (lhStationary 0.1 0.2).real {1} = 1 / 4 ∧
    (lhStationary 0.1 0.2).real {2} = 1 / 4 := by
  simp only [lhStationary_real_singleton (by norm_num : (0 : ℝ) < 0.1)
    (by norm_num : (0 : ℝ) ≤ 0.2)]
  norm_num

end AppendixB

end BrochhagenFrankeVanRooij2018
