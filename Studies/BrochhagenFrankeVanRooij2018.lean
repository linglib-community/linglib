module

public import Linglib.Logic.Aristotelian.Triangle
public import Linglib.Pragmatics.Probabilistic.Decision
public import Studies.KirbyDowmanGriffiths2007

/-!
# Brochhagen, Franke and van Rooij (2018): Coevolution of Lexical Meaning and Pragmatic Use

A type of language user pairs a lexicon, which sends each message to the set of states it is true
at, with a level of pragmatic reasoning. The literal hearer conditions the state prior on the truth
of a message, and the literal speaker is the softmax, at rationality `λ`, of its truth. The hearer
of level `n + 1` inverts the speaker of level `n` by Bayes' rule, and the speaker of level `n + 1`
is the softmax of the chance that the hearer of level `n` guesses the state. The expected success
of a speaker `σ` with a hearer `η` is the probability, under the joint law `pr ⊗ₘ (η ∘ₖ σ)` of a
state and the hearer's guess, that the guess is the state.

Every speaker sends every message with positive probability, false ones included, unlike the
speaker whose utility is the logarithm of the literal hearer's credence
(`rsaSpeaker_eq_zero_and_speaker_ne_zero`). Relabelling the states by a permutation that preserves
the prior, and the messages by any permutation, leaves expected success unchanged
(`success_image`). Over the two states of *some*, the lexicon that bounds *some* above
communicates better with its own kind than the lexicon that does not, at each level of reasoning
(`selfSuccess_lt`); `selfSuccess_Llack_zero_lt` gives the rationalities at which literal use of
the unbounded lexicon is outdone by pragmatic use of either lexicon.

A population is a probability measure on types. The replicator step reweights it by fitness and
normalizes, and the mutator step passes the result through the kernel that sends a teacher's type
to the type its learner acquires. Learners who sample from the posterior keep the prior
(`invariant_biasedPrior`), while learners who adopt the likeliest type favour the type that the
others are mistaken for (`invariant_mapLearner_comp_lh_iff`).

## Implementation notes

* The pragmatic speaker maximizes the chance that the hearer guesses the state, so it is
  `RSA.actionSpeaker` at the reward of a correct guess, not `RSA.speaker`.
* A type's datum draws the state from the state prior and the message from the type's speaker, so
  a type's data have total mass one. The state prior does not depend on the type, so it does not
  change the learner's posterior.
* The replicator step is Bayes' rule with fitness as likelihood: `replicator f x` is the row of
  `Kernel.ofDensity x` at the density `f`, and is evaluated through that API.
* The prior favouring the unbounded lexicon takes its factor as a parameter, `1.05` in the paper.
* Learners who raise the posterior to a large power are replaced by learners who adopt the
  likeliest type, the limit of large powers and `GriffithsKalish2007.mapLearner`. In the
  three-type example the paper's mutation matrix at power `10` is, to the printed precision, the
  production likelihood itself.
* The complexities of the six lexical representations are taken as printed, and the prior of a
  lexicon is left unnormalized.
* The composite step of the coordination game is formalized from its replicator and mutation
  steps, as $x \mapsto (1.1x^2 - 0.4x + 0.2)/(3x^2 - 4x + 2)$, whose rest points are the roots of
  $30x^3 - 51x^2 + 24x - 2$.
* Swapping *none* and *all* preserves the flat prior over three states and takes the lexicon
  {*none*, *some*, *all*} to {*all*, *not all*, *none*}, which therefore communicates as well with
  every type; only the simplicity prior separates the two, by `7 : 6` (`success_lexMirror`).

## TODO

* The simulations over the 432 types are not formalized.
* Convergence, not just invariance, of the iterated-learning chains.
* The fitness of a type in a mixed population, the mean of its success as speaker and as hearer
  against each type, and the replicator steps it drives on the four types of the restricted space.

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

mutual

/-- Eqs. (4) and (6): the speaker of reasoning level `n` with lexicon `L` at state prior `pr` and
rationality `lam`. The literal speaker is the softmax of the truth of a message, and a pragmatic
speaker the softmax of the chance that the hearer of the level below guesses the state. -/
noncomputable def speaker (pr : Measure S) (lam : ℝ) (L : M → Set S) : ℕ → Kernel S M
  | 0 => Kernel.softmax fun s m ↦ ((lam * (L m).indicator 1 s : ℝ) : EReal)
  | n + 1 => actionSpeaker lam 0 (hearer pr lam L n) fun a ↦ Pi.single a 1

/-- Eqs. (3) and (5): the hearer of reasoning level `n`. The literal hearer conditions the prior
on the truth of the message, and a pragmatic hearer inverts the speaker of the level below by
Bayes' rule. -/
noncomputable def hearer (pr : Measure S) (lam : ℝ) (L : M → Set S) : ℕ → Kernel M S
  | 0 => literalListener pr L
  | n + 1 => listener pr fun s ↦ speaker pr lam L n s

end

/-- §2.4.2: the expected success of a speaker with a hearer, the probability that the hearer's
guess is the state. -/
noncomputable def success (pr : Measure S) (σ : Kernel S M) (η : Kernel M S) : ℝ :=
  (pr ⊗ₘ (η ∘ₖ σ)).real (Set.diagonal S)

variable (pr : Measure S) (lam : ℝ) (L : M → Set S)

theorem speaker_zero :
    speaker pr lam L 0 = Kernel.softmax fun s m ↦ ((lam * (L m).indicator 1 s : ℝ) : EReal) :=
  rfl

theorem speaker_succ (n : ℕ) :
    speaker pr lam L (n + 1) = actionSpeaker lam 0 (hearer pr lam L n) fun a ↦ Pi.single a 1 :=
  rfl

theorem hearer_zero : hearer pr lam L 0 = literalListener pr L := rfl

theorem hearer_succ (n : ℕ) : hearer pr lam L (n + 1) = listener pr fun s ↦ speaker pr lam L n s :=
  rfl

instance (n : ℕ) : IsFiniteKernel (speaker pr lam L n) := by
  cases n <;> exact inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty M] (n : ℕ) : IsMarkovKernel (speaker pr lam L n) := by
  cases n
  · exact Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary M, EReal.coe_ne_bot _⟩)
      fun _ _ ↦ EReal.coe_ne_top _
  · exact inferInstanceAs (IsMarkovKernel (actionSpeaker _ _ _ _))

instance (n : ℕ) : IsFiniteKernel (hearer pr lam L n) := by
  cases n <;> exact inferInstanceAs (IsFiniteKernel (listener _ _))

-- Note 2: every speaker sends every message, false ones included, with positive probability.
theorem speaker_apply_singleton_ne_zero (n : ℕ) (s : S) (m : M) : speaker pr lam L n s {m} ≠ 0 := by
  cases n
  · exact Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _
  · exact actionSpeaker_apply_singleton_ne_zero _ _ _

-- With two messages, the literal speaker's share of one is the logistic function of the scaled
-- difference in their truth.
theorem speaker_zero_real_of_pair (s : S) {m m' : M} (hmm' : m ≠ m') (hall : ∀ c, c = m ∨ c = m') :
    (speaker pr lam L 0 s).real {m} =
      Real.sigmoid (lam * (L m).indicator 1 s - lam * (L m').indicator 1 s) := by
  rw [speaker_zero, Kernel.softmax_real_singleton_of_pair hmm' (EReal.coe_ne_bot _)
    (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe,
    EReal.toReal_coe]

-- With two messages, a pragmatic speaker's share of one is the logistic function of the scaled
-- difference in the chance that the hearer below guesses the state after each.
theorem speaker_succ_real_of_pair (n : ℕ) (s : S) {m m' : M} (hmm' : m ≠ m')
    (hall : ∀ c, c = m ∨ c = m') :
    (speaker pr lam L (n + 1) s).real {m} =
      Real.sigmoid (lam * ((hearer pr lam L n m).real {s} - (hearer pr lam L n m').real {s})) := by
  rw [speaker_succ, actionSpeaker_real_of_pair (fun a ↦ Pi.single a 1) 0 _ hmm' hall]
  simp [integral_pi_single]

-- The literal hearer conditions the prior on the truth of the message.
theorem hearer_zero_real (m : M) (s : S) :
    (hearer pr lam L 0 m).real {s} = (L m).indicator (fun s ↦ pr.real {s} / pr.real (L m)) s := by
  by_cases h : s ∈ L m
  · rw [Set.indicator_of_mem h, hearer_zero, literalListener_real_singleton pr L h]
  · rw [Set.indicator_of_notMem h, measureReal_def, hearer_zero,
      literalListener_apply_singleton_of_notMem pr L h, ENNReal.toReal_zero]

private theorem compProd_real_diagonal [SFinite pr] (κ : Kernel S S) [IsSFiniteKernel κ] :
    (pr ⊗ₘ κ).real (Set.diagonal S) = (∫⁻ s, κ s {s} ∂pr).toReal := by
  rw [measureReal_def, Measure.compProd_apply .of_discrete]
  congr 2 with s
  congr 1
  ext t
  simp [eq_comm]

-- Expected success is the chance, averaged over the prior, that the round trip from a state
-- through a message returns it.
theorem success_eq_lintegral [SFinite pr] (σ : Kernel S M) [IsSFiniteKernel σ] (η : Kernel M S)
    [IsSFiniteKernel η] : success pr σ η = (∫⁻ s, (η ∘ₖ σ) s {s} ∂pr).toReal :=
  compProd_real_diagonal pr _

theorem success_eq_sum [IsFiniteMeasure pr] (σ : Kernel S M) [IsFiniteKernel σ] (η : Kernel M S)
    [IsFiniteKernel η] :
    success pr σ η = ∑ s, pr.real {s} * ∑ m, (σ s).real {m} * (η m).real {s} := by
  rw [success_eq_lintegral, lintegral_fintype, ENNReal.toReal_sum fun s _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [Kernel.comp_apply' _ _ _ (.singleton s), lintegral_fintype, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun m _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
    mul_comm, measureReal_def]
  simp only [ENNReal.toReal_mul, measureReal_def, mul_comm]

/-- Note 2: a speaker who maximizes the logarithm of the literal hearer's credence in the state
never sends a false message, whereas every speaker of the paper does with positive probability. -/
theorem rsaSpeaker_eq_zero_and_speaker_ne_zero {α : ℝ} (hα : 0 < α) {s : S} {m : M}
    (h : s ∉ L m) :
    RSA.speaker α 0 (literalListener pr L) Measure.dirac s {m} = 0 ∧
      ∀ n, speaker pr lam L n s {m} ≠ 0 :=
  ⟨speaker_dirac_apply_singleton_eq_zero hα (literalListener_apply_singleton_of_notMem pr L h),
    fun n ↦ speaker_apply_singleton_ne_zero pr lam L n s m⟩

/-! #### Relabelling states and messages -/

private theorem preimage_singleton_equiv {X : Type*} (e : X ≃ X) (x : X) :
    e ⁻¹' {x} = {e.symm x} := by
  ext y
  simp [Equiv.eq_symm_apply]

private theorem indicator_image {β : Type*} [Zero β] [One β] (e : S ≃ S) (A : Set S) (s : S) :
    (e '' A).indicator (1 : S → β) s = A.indicator 1 (e.symm s) := by
  rw [e.image_eq_preimage_symm]
  rfl

private theorem softmax_image (e : S ≃ S) (π : M ≃ M) {score score' : S → M → EReal}
    (h : ∀ s m, score' s m = score (e.symm s) (π.symm m)) :
    Kernel.softmax score' = ((Kernel.softmax score).comap e.symm .of_discrete).map π := by
  ext s : 1
  refine Measure.ext_of_singleton fun m ↦ ?_
  rw [Kernel.map_apply' _ .of_discrete _ (.singleton m), Kernel.comap_apply,
    preimage_singleton_equiv, Kernel.softmax_apply_singleton, Kernel.softmax_apply_singleton]
  simp only [h]
  rw [π.symm.sum_comp fun u ↦ (score (e.symm s) u).exp]

private theorem listener_image {e : S ≃ S} (he : MeasurePreserving e pr pr) (π : M ≃ M)
    {C C' : S → Measure M} (h : ∀ s m, C' s {m} = C (e.symm s) {π.symm m}) :
    listener pr C' = ((listener pr C).comap π.symm .of_discrete).map e := by
  ext m : 1
  have hf : (fun m s ↦ C s {m}) = fun m ↦ (fun s ↦ C (e.symm s) {m}) ∘ e := by
    funext m s
    simp
  rw [Kernel.map_apply _ .of_discrete, Kernel.comap_apply, listener, listener, hf,
    Kernel.ofDensity_map pr Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable, he.map_eq]
  simp only [Kernel.ofDensity_apply, h]

private theorem speaker_image_and_hearer_image {e : S ≃ S} (he : MeasurePreserving e pr pr)
    (π : M ≃ M) (n : ℕ) :
    speaker pr lam (fun m ↦ e '' L (π.symm m)) n =
        ((speaker pr lam L n).comap e.symm .of_discrete).map π ∧
      hearer pr lam (fun m ↦ e '' L (π.symm m)) n =
        ((hearer pr lam L n).comap π.symm .of_discrete).map e := by
  induction n with
  | zero =>
    refine ⟨softmax_image e π fun s m ↦ by rw [indicator_image], listener_image pr he π
      fun s m ↦ ?_⟩
    rw [truthful_apply_singleton, truthful_apply_singleton, indicator_image]
  | succ n ih =>
    refine ⟨softmax_image e π fun s m ↦ ?_, listener_image pr he π fun s m ↦ ?_⟩
    · simp only [ih.2, integral_pi_single, measureReal_def, Pi.zero_apply,
        Kernel.map_apply' _ .of_discrete _ (.singleton s), Kernel.comap_apply,
        preimage_singleton_equiv]
    · rw [ih.1, Kernel.map_apply' _ .of_discrete _ (.singleton m), Kernel.comap_apply,
        preimage_singleton_equiv]

variable {pr} {e : S ≃ S}

-- Relabelling the states of a lexicon by a permutation that preserves the prior, and its messages
-- by any permutation, relabels its speakers' states and messages alike.
theorem speaker_image (he : MeasurePreserving e pr pr) (π : M ≃ M) (n : ℕ) :
    speaker pr lam (fun m ↦ e '' L (π.symm m)) n =
      ((speaker pr lam L n).comap e.symm .of_discrete).map π :=
  (speaker_image_and_hearer_image pr lam L he π n).1

theorem hearer_image (he : MeasurePreserving e pr pr) (π : M ≃ M) (n : ℕ) :
    hearer pr lam (fun m ↦ e '' L (π.symm m)) n =
      ((hearer pr lam L n).comap π.symm .of_discrete).map e :=
  (speaker_image_and_hearer_image pr lam L he π n).2

-- §2.4.2: so the expected success of any speaker with any hearer is unchanged when both lexica are
-- relabelled alike.
theorem success_image (L' : M → Set S) (he : MeasurePreserving e pr pr) (π : M ≃ M) (n n' : ℕ) :
    success pr (speaker pr lam (fun m ↦ e '' L (π.symm m)) n)
        (hearer pr lam (fun m ↦ e '' L' (π.symm m)) n') =
      success pr (speaker pr lam L n) (hearer pr lam L' n') := by
  have hπ : ((hearer pr lam L' n').comap π.symm .of_discrete).comap π .of_discrete =
      hearer pr lam L' n' := by
    ext m : 1
    rw [Kernel.comap_apply, Kernel.comap_apply, π.symm_apply_apply]
  rw [speaker_image lam L he π n, hearer_image lam L' he π n', success, ← Kernel.map_comp,
    Kernel.comp_map _ _ .of_discrete, hπ, success, compProd_real_diagonal,
    compProd_real_diagonal, ← he.lintegral_comp .of_discrete]
  refine congrArg _ (lintegral_congr fun s ↦ ?_)
  rw [Kernel.map_apply' _ .of_discrete _ (.singleton _), preimage_singleton_equiv,
    Kernel.comp_apply, Kernel.comp_apply, Kernel.comap_apply, e.symm_apply_apply]

end Agents

/-! ### Some and all: the restricted type space of §3.1

The states are the two vertices of the I corner of the square of opposition, *some but not all*
(`Triangle.someNotAll`) and *all* (`Triangle.all`), equally likely. -/

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
  | .some => {.someNotAll}
  | .all => {.all}

/-- §2.4.1: `L_lack` gives *some* only a lower bound, so *some* is true at *all*. -/
def Llack : Msg → Set Triangle
  | .some => ↑Triangle.corners.I
  | .all => {.all}

/-- The success of a type with its own kind, its fitness in a population of that type. -/
noncomputable def selfSuccess (lam : ℝ) (L : Msg → Set Triangle) (n : ℕ) : ℝ :=
  success pr (speaker pr lam L n) (hearer pr lam L n)

instance : IsProbabilityMeasure pr :=
  isProbabilityMeasure_uniformOn (finite_toSet _) ⟨.someNotAll, by decide⟩

private theorem msg_univ : (univ : Finset Msg) = {.some, .all} := by decide

private theorem pr_real (t : Triangle) :
    pr.real {t} = if t = .none then 0 else 1 / 2 := by
  rw [pr, uniformOn_finset_real_singleton]
  cases t <;> simp [Triangle.corners]

private theorem success_eq {σ : Kernel Triangle Msg} [IsFiniteKernel σ] {η : Kernel Msg Triangle}
    [IsFiniteKernel η] :
    success pr σ η = ((σ .someNotAll).real {.some} * (η .some).real {.someNotAll} +
      (σ .someNotAll).real {.all} * (η .all).real {.someNotAll} +
      (σ .all).real {.some} * (η .some).real {.all} +
      (σ .all).real {.all} * (η .all).real {.all}) / 2 := by
  simp only [success_eq_sum, Triangle.univ_eq, msg_univ, sum_insert, mem_insert, mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, sum_singleton, pr_real, ↓reduceIte]
  ring

variable {lam : ℝ}

private theorem pragmatic_hearer_real (L : Msg → Set Triangle) (m : Msg) (s : Triangle) :
    (hearer pr lam L 1 m).real {s} = pr.real {s} * (speaker pr lam L 0 s).real {m} /
      ((speaker pr lam L 0 .someNotAll).real {m} / 2 +
        (speaker pr lam L 0 .all).real {m} / 2) := by
  rw [hearer_succ, listener_real_singleton]
  congr 1
  simp only [Triangle.univ_eq, sum_insert, mem_insert, mem_singleton, reduceCtorEq, or_self,
    not_false_eq_true, sum_singleton, pr_real, ↓reduceIte]
  ring

private theorem pr_real_I : pr.real {.someNotAll, .all} = 1 := by
  rw [show ({.someNotAll, .all} : Set Triangle) = ↑Triangle.corners.I by ext t; cases t <;> decide,
    pr, measureReal_def, uniformOn_self (finite_toSet _) ⟨.someNotAll, by decide⟩,
    ENNReal.toReal_one]

private theorem pr_real_someNotAll : pr.real {.someNotAll} = 1 / 2 := by rw [pr_real]; rfl

private theorem pr_real_all : pr.real {.all} = 1 / 2 := by rw [pr_real]; rfl

private theorem S0_some (L : Msg → Set Triangle) (s : Triangle) :
    (speaker pr lam L 0 s).real {.some} =
      Real.sigmoid (lam * (L .some).indicator 1 s - lam * (L .all).indicator 1 s) :=
  speaker_zero_real_of_pair pr lam L s (by decide) fun c ↦ by cases c <;> simp

private theorem S0_all (L : Msg → Set Triangle) (s : Triangle) :
    (speaker pr lam L 0 s).real {.all} =
      Real.sigmoid (lam * (L .all).indicator 1 s - lam * (L .some).indicator 1 s) :=
  speaker_zero_real_of_pair pr lam L s (by decide) fun c ↦ by cases c <;> simp

private theorem S1_some (L : Msg → Set Triangle) (s : Triangle) :
    (speaker pr lam L 1 s).real {.some} = Real.sigmoid (lam *
      ((hearer pr lam L 0 .some).real {s} - (hearer pr lam L 0 .all).real {s})) :=
  speaker_succ_real_of_pair pr lam L 0 s (by decide) fun c ↦ by cases c <;> simp

private theorem S1_all (L : Msg → Set Triangle) (s : Triangle) :
    (speaker pr lam L 1 s).real {.all} = Real.sigmoid (lam *
      ((hearer pr lam L 0 .all).real {s} - (hearer pr lam L 0 .some).real {s})) :=
  speaker_succ_real_of_pair pr lam L 0 s (by decide) fun c ↦ by cases c <;> simp

-- §2.4.1: the literal user of `L_bound` sends the true message with chance `σ(λ)`.
theorem selfSuccess_Lbound_zero : selfSuccess lam Lbound 0 = Real.sigmoid lam := by
  rw [selfSuccess, success_eq, S0_some, S0_all, S0_some, S0_all]
  simp [hearer_zero_real, Lbound, pr_real_someNotAll, pr_real_all, Real.sigmoid_neg]

-- §2.4.1: the pragmatic user of `L_bound` reasons over the literal one's noise.
theorem selfSuccess_Lbound_one :
    selfSuccess lam Lbound 1 = Real.sigmoid lam ^ 2 + (1 - Real.sigmoid lam) ^ 2 := by
  rw [selfSuccess, success_eq, S1_some, S1_all, S1_some, S1_all, pragmatic_hearer_real,
    pragmatic_hearer_real, pragmatic_hearer_real, pragmatic_hearer_real]
  simp only [S0_some, S0_all, hearer_zero_real]
  simp [Lbound, pr_real_someNotAll, pr_real_all, Real.sigmoid_neg]
  ring

-- §2.4.1: the literal user of `L_lack` cannot tell the states apart after *some*.
theorem selfSuccess_Llack_zero : selfSuccess lam Llack 0 = Real.sigmoid lam / 4 + 3 / 8 := by
  rw [selfSuccess, success_eq, S0_some, S0_all, S0_some, S0_all]
  simp [hearer_zero_real, Llack, pr_real_someNotAll, pr_real_all, pr_real_I, Real.sigmoid_neg,
    Triangle.corners]
  ring

-- §2.4.1: the pragmatic user of `L_lack`, with `σ(λ)` and `σ(λ/2)`.
theorem selfSuccess_Llack_one :
    selfSuccess lam Llack 1 =
      (Real.sigmoid (lam / 2) * Real.sigmoid lam / (Real.sigmoid lam + 1 / 2) +
        (1 - Real.sigmoid (lam / 2)) * (1 - Real.sigmoid lam) / (3 / 2 - Real.sigmoid lam) +
        (1 - Real.sigmoid (lam / 2)) * (1 / 2) / (Real.sigmoid lam + 1 / 2) +
        Real.sigmoid (lam / 2) * (1 / 2) / (3 / 2 - Real.sigmoid lam)) / 2 := by
  have hH0 (m : Msg) (t : Triangle) : (hearer pr lam Llack 0 m).real {t} =
      if t = .none then 0 else if m = .some then 1 / 2 else if t = .all then 1 else 0 := by
    rw [hearer_zero_real]
    cases m <;> cases t <;>
      simp [Llack, Triangle.corners, pr_real_someNotAll, pr_real_all, pr_real_I]
  have hS0 (m : Msg) (t : Triangle) (ht : t ≠ .none) : (speaker pr lam Llack 0 t).real {m} =
      if t = .all then 1 / 2 else if m = .some then Real.sigmoid lam else 1 - Real.sigmoid lam := by
    cases m <;> cases t <;>
      simp_all [S0_some, S0_all, Llack, Triangle.corners, Real.sigmoid_neg, Real.sigmoid_zero]
  have hS1 (m : Msg) (t : Triangle) (ht : t ≠ .none) : (speaker pr lam Llack 1 t).real {m} =
      if (m = .some) = (t = .someNotAll) then Real.sigmoid (lam / 2)
      else 1 - Real.sigmoid (lam / 2) := by
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
  simp only [hS1 _ _ (by decide : Triangle.someNotAll ≠ .none),
    hS1 _ _ (by decide : Triangle.all ≠ .none), hS0 _ _ (by decide : Triangle.someNotAll ≠ .none),
    hS0 _ _ (by decide : Triangle.all ≠ .none), pr_real_someNotAll, pr_real_all]
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

/-- §3.1: at every positive rationality, literal `L_bound` communicates better with its own kind
than pragmatic `L_bound` and than literal `L_lack`, and pragmatic `L_bound` better than pragmatic
`L_lack`. -/
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

/-- §3.1: pragmatic `L_bound` communicates better with its own kind than literal `L_lack` exactly
when `λ > log (5/3)`, and pragmatic `L_lack` worse than literal `L_lack` whenever
`λ ≤ 2 log (5/2)`. -/
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
-- communicates better with its own kind than literal `L_lack`.
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
  Kernel.ofFunOfCountable fun t ↦ Measure.pi fun _ ↦ pr ⊗ₘ speaker pr lam t.1.denote t.2

instance (k : ℕ) : IsMarkovKernel (produce lam k) :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofFunOfCountable _))

/-- Fig. 2: the prior over types favouring those with `L_lack` by a factor `c`. -/
noncomputable def biasedPrior (c : ℝ≥0) : Measure (Lex × Fin 2) :=
  ∑ t,
    ENNReal.ofReal ((if t.1 = .lack then (c : ℝ) else 1) / (2 * (c + 1))) • Measure.dirac t

private theorem lex_univ : (univ : Finset Lex) = {.bound, .lack} := by decide

private theorem biasedPrior_real_singleton (c : ℝ≥0) (t : Lex × Fin 2) :
    (biasedPrior c).real {t} = (if t.1 = .lack then (c : ℝ) else 1) / (2 * (c + 1)) :=
  Measure.finsetSum_ofReal_smul_dirac_real_singleton (fun t ↦ by positivity) t

instance (c : ℝ≥0) : IsProbabilityMeasure (biasedPrior c) := by
  refine Measure.isProbabilityMeasure_finsetSum_ofReal_smul_dirac (fun t ↦ by positivity) ?_
  rw [Fintype.sum_prod_type, lex_univ, sum_pair (by decide)]
  simp only [Fin.sum_univ_two, ↓reduceIte, reduceCtorEq]
  field_simp
  ring

private theorem biasedPrior_real_lex (c : ℝ≥0) (x : Lex) :
    (biasedPrior c).real (Prod.fst ⁻¹' {x}) = (if x = .lack then (c : ℝ) else 1) / (c + 1) := by
  have : (Prod.fst ⁻¹' {x} : Set (Lex × Fin 2)) = ↑({(x, 0), (x, 1)} : Finset (Lex × Fin 2)) := by
    ext t; obtain ⟨y, i⟩ := t; fin_cases i <;> simp
  rw [this, ← sum_measureReal_singleton, sum_pair (by simp), biasedPrior_real_singleton,
    biasedPrior_real_singleton]
  field_simp
  ring

/-- §3.1, Fig. 2(b): learners who sample from the posterior keep the prior, so a population under
mutation alone settles where users of `L_lack` outnumber users of `L_bound` by the factor by which
the prior favours them. -/
theorem invariant_biasedPrior (k : ℕ) (c : ℝ≥0) :
    (exponentiatedPosterior (produce lam k) (biasedPrior c) 1 ∘ₖ produce lam k).Invariant
      (biasedPrior c) ∧
      (biasedPrior c).real (Prod.fst ⁻¹' {.lack}) /
        (biasedPrior c).real (Prod.fst ⁻¹' {.bound}) = c := by
  refine ⟨invariant_exponentiatedPosterior_one _ _, ?_⟩
  rw [biasedPrior_real_lex, biasedPrior_real_lex]
  simp only [↓reduceIte, reduceCtorEq]
  field_simp

example :
    (biasedPrior 1.05).real (Prod.fst ⁻¹' {.lack}) /
      (biasedPrior 1.05).real (Prod.fst ⁻¹' {.bound}) = 1.05 := by
  rw [(invariant_biasedPrior (lam := 0) 0 1.05).2]
  norm_num

end TwoStates

/-! ### Three states: the lexica of §3.2

The states are the three vertices of the triangle of opposition, *none* (`Triangle.none`), *some
but not all* (`Triangle.someNotAll`) and *all* (`Triangle.all`), equally likely, and a lexicon sends
each of three messages to a set of states. -/

section ThreeStates

open Aristotelian.Triangle (corners)

/-- §3.2.1: a lexical representation, a set of states other than the empty and the full one. -/
abbrev Representation := {r : Finset Triangle // r ≠ ∅ ∧ r ≠ univ}

-- §3.2.1: six representations, `6³ = 216` lexica and `432` types.
theorem card_types : Fintype.card Representation = 6 ∧ Fintype.card (Fin 3 → Representation) = 216 ∧
    Fintype.card ((Fin 3 → Representation) × Fin 2) = 432 := by
  have h : Fintype.card Representation = 6 := by decide
  simp [Fintype.card_prod, h]

/-- Table 2: the complexity assigned to each representation. -/
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

-- §3.2.2: the prior favours `lexAll` over `lexLack` over `lexBound`.
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

-- §3.2.2: no lexicon is likelier a priori than `lexAll`.
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

/-- The flat prior over the three states. -/
noncomputable def flat : Measure Triangle := uniformOn Set.univ

/-- A lexicon's denotations. -/
def denote (L : Fin 3 → Representation) (m : Fin 3) : Set Triangle := ↑(L m).1

private theorem measurePreserving_swap_flat :
    MeasurePreserving (Equiv.swap Triangle.none .all) flat flat := by
  refine ⟨.of_discrete, Measure.ext_of_singleton fun s ↦ ?_⟩
  rw [Measure.map_apply .of_discrete (.singleton s), preimage_singleton_equiv, flat,
    uniformOn_univ_singleton_eq]

-- The order-reversing permutation of the states, which swaps *none* and *all*, takes `lexLack`
-- to `lexMirror`. The flat prior is symmetric under it, so `lexMirror` communicates with every
-- type as `lexLack` does at every level and rationality; only the prior separates them, 7 : 6.
theorem success_lexMirror (lam : ℝ) (L : Fin 3 → Set Triangle) (n n' : ℕ) :
    success flat (speaker flat lam (denote lexMirror) n)
        (hearer flat lam (fun m ↦ Equiv.swap .none .all '' L m) n') =
      success flat (speaker flat lam (denote lexLack) n) (hearer flat lam L n') ∧
      lexiconWeight lexLack = 7 / 6 * lexiconWeight lexMirror := by
  have he : denote lexMirror = fun m ↦ Equiv.swap .none .all '' denote lexLack m := by
    funext m
    rw [denote, denote, ← Equiv.coe_toEmbedding, ← Finset.coe_map, Finset.coe_inj]
    fin_cases m <;> decide
  refine ⟨he ▸ success_image lam _ L measurePreserving_swap_flat (Equiv.refl _) n n', ?_⟩
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
  ENNReal.ofReal (∫ j, U i j ∂x)

/-- Eq. (2): the replicator step, which reweights each type by its fitness and normalizes. -/
noncomputable def replicator (f : T → ℝ≥0∞) (x : Measure T) : Measure T :=
  (x.withDensity f)[|Set.univ]

/-- Eqs. (1)–(2): the replicator mutator step. -/
noncomputable def rmd (Q : Kernel T T) (f : T → ℝ≥0∞) (x : Measure T) : Measure T :=
  Q ∘ₘ replicator f x

-- The replicator step is Bayes' rule with fitness as likelihood.
theorem replicator_eq_ofDensity (f : T → ℝ≥0∞) (x : Measure T) :
    replicator f x = Kernel.ofDensity x (fun (_ : Unit) ↦ f) () := by
  rw [replicator, Kernel.ofDensity_apply]

instance (f : T → ℝ≥0∞) (x : Measure T) : IsFiniteMeasure (replicator f x) :=
  inferInstanceAs (IsFiniteMeasure ((x.withDensity f)[|Set.univ]))

theorem replicator_real_singleton (f : T → ℝ≥0∞) (hf : ∀ i, f i ≠ ⊤) (x : Measure T)
    [IsFiniteMeasure x] (i : T) :
    (replicator f x).real {i} = (f i).toReal * x.real {i} / ∑ k, (f k).toReal * x.real {k} := by
  rw [replicator_eq_ofDensity]
  exact Kernel.ofDensity_real_singleton x _ () hf i

omit [Fintype T] [MeasurableSingletonClass T] in
-- p. 2761: without mutation the dynamic is the replicator dynamic.
theorem rmd_id (f : T → ℝ≥0∞) (x : Measure T) : rmd Kernel.id f x = replicator f x :=
  Measure.id_comp

omit [Fintype T] [MeasurableSingletonClass T] in
-- p. 2761: under equal fitness the dynamic is iterated mutation.
theorem rmd_const (Q : Kernel T T) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) (x : Measure T)
    [IsProbabilityMeasure x] : rmd Q (fun _ ↦ c) x = Q ∘ₘ x := by
  rw [rmd, replicator, withDensity_const, cond_smul hc hc', cond_univ]

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
  Kernel.ofFunOfCountable fun j ↦
    ∑ i, ENNReal.ofReal (if i = j then 0.9 else 0.1) • Measure.dirac i

theorem univ_eq : (univ : Finset Sign) = {negative, positive} := by decide

end Sign

open Sign

private theorem mutation_real_negative (j : Sign) :
    (mutation j).real {negative} = if negative = j then 0.9 else 0.1 := by
  rw [mutation, Kernel.ofFunOfCountable_apply,
    Measure.finsetSum_ofReal_smul_dirac_real_singleton (fun i ↦ by split_ifs <;> norm_num)]

instance : IsMarkovKernel mutation :=
  ⟨fun j ↦ by
    rw [mutation, Kernel.ofFunOfCountable_apply]
    refine Measure.isProbabilityMeasure_finsetSum_ofReal_smul_dirac
      (fun i ↦ by split_ifs <;> norm_num) ?_
    cases j <;> simp [univ_eq] <;> norm_num⟩

private theorem real_positive (x : Measure Sign) [IsProbabilityMeasure x] :
    x.real {positive} = 1 - x.real {negative} := by
  have : x.real {negative} + x.real {positive} = 1 :=
    measureReal_singleton_add_singleton_of_pair x (by decide) fun i _ ↦ by cases i <;> simp
  linarith

private theorem ext_of_real_negative {x y : Measure Sign} [IsProbabilityMeasure x]
    [IsProbabilityMeasure y] (h : x.real {negative} = y.real {negative}) : x = y :=
  Measure.ext_of_measureReal_singleton fun i ↦ by
    cases i
    · exact h
    · rw [real_positive, real_positive, h]

-- App. A: mutation alone sends the share `x` of negatives to `0.8x + 0.1`, so its one rest point
-- is the even population.
theorem invariant_mutation_iff (x : Measure Sign) [IsProbabilityMeasure x] :
    mutation.Invariant x ↔ x.real {negative} = 1 / 2 := by
  have h : (mutation ∘ₘ x).real {negative} = 0.8 * x.real {negative} + 0.1 := by
    rw [Measure.comp_real_singleton, univ_eq, sum_pair (by decide), mutation_real_negative,
      mutation_real_negative, real_positive]
    simp only [↓reduceIte, reduceCtorEq]
    ring
  refine ⟨fun hx ↦ ?_, fun hx ↦ ext_of_real_negative ?_⟩
  · have := congrArg (fun μ ↦ μ.real {negative}) hx.def
    rw [h] at this
    linarith
  · rw [h, hx]
    norm_num

private theorem replicator_real (x : Measure Sign) [IsProbabilityMeasure x] (i : Sign) :
    (replicator (fitness payoff x) x).real {i} =
      (if i = negative then x.real {negative} ^ 2 else 2 * (1 - x.real {negative}) ^ 2) /
        (3 * x.real {negative} ^ 2 - 4 * x.real {negative} + 2) := by
  have h₀ := measureReal_nonneg (μ := x) (s := {negative})
  have h₁ : x.real {negative} ≤ 1 := measureReal_le_one
  have hp := real_positive x
  have hf (j : Sign) : fitness payoff x j = ENNReal.ofReal
      (x.real {negative} * payoff j negative + (1 - x.real {negative}) * payoff j positive) := by
    rw [fitness, integral_fintype .of_finite, univ_eq, sum_pair (by decide), smul_eq_mul,
      smul_eq_mul, hp]
  rw [replicator_real_singleton (fitness payoff x) (fun _ ↦ ENNReal.ofReal_ne_top), univ_eq,
    sum_pair (by decide)]
  cases i <;>
    simp only [hf, payoff, hp, ↓reduceIte, reduceCtorEq] <;>
    rw [ENNReal.toReal_ofReal (by nlinarith), ENNReal.toReal_ofReal (by nlinarith)] <;>
    congr 1 <;> ring

-- App. A: the replicator step alone rests at the shares `0`, `2/3` and `1` of negatives.
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

-- App. A: the replicator mutator step sends the share `x` of negatives to
-- `(1.1x² - 0.4x + 0.2) / (3x² - 4x + 2)`.
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

-- App. A: so the replicator mutator step rests where the share of negatives is a root of
-- `30x³ - 51x² + 24x - 2`.
theorem rmd_real_negative_eq_iff (x : Measure Sign) [IsProbabilityMeasure x] :
    (rmd mutation (fitness payoff x) x).real {negative} = x.real {negative} ↔
      30 * x.real {negative} ^ 3 - 51 * x.real {negative} ^ 2 + 24 * x.real {negative} - 2 = 0 := by
  rw [rmd_real_negative]
  set a := x.real {negative}
  have hΦ : 3 * a ^ 2 - 4 * a + 2 ≠ 0 := by nlinarith [sq_nonneg (a - 2 / 3)]
  rw [div_eq_iff hΦ]
  exact ⟨fun h ↦ by linear_combination (-10 : ℝ) * h, fun h ↦ by linear_combination (-1 / 10 : ℝ) * h⟩

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
  Kernel.ofFunOfCountable fun i ↦
    ∑ j, ENNReal.ofReal (lhWeight ε δ i j) • Measure.dirac j

/-- App. B: the population `(δ, ε, ε) / (δ + 2ε)` over the three types. -/
noncomputable def lhStationary (ε δ : ℝ) : Measure (Fin 3) :=
  ∑ i, ENNReal.ofReal ((if i = 0 then δ else ε) / (δ + 2 * ε)) • Measure.dirac i

private theorem lhWeight_nonneg (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) (i j : Fin 3) :
    0 ≤ lhWeight ε δ i j := by
  unfold lhWeight
  split_ifs <;> linarith

private theorem lh_apply_singleton (i j : Fin 3) :
    lh ε δ i {j} = ENNReal.ofReal (lhWeight ε δ i j) := by
  rw [lh, Kernel.ofFunOfCountable_apply, Measure.finsetSum_smul_dirac_singleton]

theorem isMarkovKernel_lh (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : δ + 2 * ε < 1) :
    IsMarkovKernel (lh ε δ) := by
  refine ⟨fun i ↦ ?_⟩
  rw [lh, Kernel.ofFunOfCountable_apply]
  refine Measure.isProbabilityMeasure_finsetSum_ofReal_smul_dirac (lhWeight_nonneg hε hδ h i) ?_
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
  refine Measure.isProbabilityMeasure_finsetSum_ofReal_smul_dirac (fun i ↦ by positivity) ?_
  simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  field_simp
  ring

private theorem lhStationary_real_singleton (hε : 0 < ε) (hδ : 0 ≤ δ) (i : Fin 3) :
    (lhStationary ε δ).real {i} = (if i = 0 then δ else ε) / (δ + 2 * ε) :=
  Measure.finsetSum_ofReal_smul_dirac_real_singleton (fun i ↦ by positivity) i

private theorem real_add_three (ν : Measure (Fin 3)) [IsProbabilityMeasure ν] :
    ν.real {0} + ν.real {1} + ν.real {2} = 1 := by
  have := sum_measureReal_singleton (μ := ν) (univ : Finset (Fin 3))
  rwa [Fin.sum_univ_three, coe_univ, probReal_univ] at this

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
  refine ⟨fun hν ↦ Measure.ext_of_measureReal_singleton fun i ↦ ?_, ?_⟩
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
    refine Measure.ext_of_measureReal_singleton fun j ↦ ?_
    rw [hcomp, lhStationary_real_singleton hε hδ, lhStationary_real_singleton hε hδ,
      lhStationary_real_singleton hε hδ, lhStationary_real_singleton hε hδ]
    fin_cases j <;> simp [lhWeight] <;> field_simp <;> ring

/-- App. B: learners who sample from the posterior keep the flat prior, while learners who adopt the
likeliest type learn `LH` itself, whose only stationary population is `(δ, ε, ε) / (δ + 2ε)`, which
favours `t₁` exactly when `δ > ε`. -/
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
