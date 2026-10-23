module

public import Linglib.Core.InformationTheory.Hellinger
public import Linglib.Core.Probability.Distributions.Hypergeometric
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Data.Examples.HerbstrittFranke2019
public import Linglib.Pragmatics.RSA.Belief

/-!
# Herbstritt and Franke (2019): Complex probability expressions and higher-order uncertainty

This file formalizes the rational speech act model of Herbstritt and Franke for a speaker who has
drawn some balls from an urn of ten and tells a listener how likely the next draw is to be red. The
speaker's belief of (12) is the posterior over the number of red balls given her observation,
`belief`, the Bayesian inverse of the hypergeometric observation kernel; a simple expression holds
at a state by the threshold semantics of (13) and (14), `Thresholds.meaning`, and the literal
listener of (15) conditions the prior on the extension. The speaker of (16) and (17), `speaker`, is
the softmax of the negative Hellinger distance between her belief and the literal listener's, and
the pragmatic listener of (18) inverts her against the joint prior over states, observations and
accesses, whose marginals are (19) and (20). A complex expression holds at an observation by (23)
when the belief it induces gives the inner expression's extension more than the outer threshold,
`ComplexThresholds.complex`.

Because the Hellinger distance is finite, every message is used with positive probability at every
observation (`speaker_apply_singleton_ne_zero`), where the Kullback–Leibler speaker of Goodman and
Stuhlmüller never uses a message whose extension misses a state of positive belief, the paper's
*probably red* after three red balls of four. The distance is also at most one, so the utility is
at least minus one. With complete access the belief is a point mass, so a false message has that
least utility and a true message beats it, and among true messages the one whose extension carries
less prior mass wins, the scalar implicature of the paper's introductory example; the pragmatic
listener never rules a state out entirely; and with complete access an outer modifier below one is
vacuous.

## Implementation notes

* The observation kernel normalizes the hypergeometric weight `C(s, o) C(10 − s, a − o)`
  row by row, and the priors over states and accesses are arbitrary measures where the paper
  fits beta-binomials; the thresholds are parameters, the paper's fitted values (Tables 6
  and 9) being prose. The bare copula of Experiment 3 is the simple expression.
* The Kullback–Leibler speaker is stated to make the contrast of the paper's footnote on
  utilities a theorem; the paper does not run it.
* At a message whose extension has prior mass zero, where Bayes' rule in (15) is undefined, the
  literal listener is the zero measure; the complete-access theorems about a false message assume
  its extension has positive prior mass.

## TODO

* The complex utility of (26) and (27) and the complex speaker and listener of (28) and (29).
* The posterior predictive checks and the modal concord reading of *might be possible* (§6).

## References

* [herbstritt-franke-2019]
* [goodman-stuhlmuller-2013]
* [fagin-halpern-1994]
* [frank-goodman-2012]
* [zeijlstra-2007]
-/

@[expose] public section

namespace HerbstrittFranke2019

open MeasureTheory ProbabilityTheory RSA InformationTheory
open scoped ENNReal

/-- A state records how many of the ten balls in the urn are red. -/
abbrev State := Fin 11

/-- The speaker's access is how many balls she draws. -/
abbrev Access := Fin 11

/-- An observation records how many of the drawn balls are red. -/
abbrev Obs := Fin 11

/-- The probability of drawing a red ball in a state. -/
noncomputable def proportion (s : State) : ℝ := (s : ℕ) / 10

/-! ### Belief formation, (12) -/

/-- The observation kernel `Hypergeometric(o | a, s, 10)` gives the number of red balls among
`a` drawn without replacement from ten of which `s` are red. -/
noncomputable def obs (a : Access) : Kernel State Obs := hypergeometric 10 a

instance (a : Access) : IsFiniteKernel (obs a) :=
  inferInstanceAs (IsFiniteKernel (hypergeometric 10 a))

theorem obs_apply_singleton_ne_zero_iff (a : Access) (s : State) (o : Obs) :
    obs a s {o} ≠ 0 ↔ hypergeometricCount 10 s a o ≠ 0 :=
  hypergeometric_apply_singleton_ne_zero_iff s o

section Belief

variable (P : Measure State) [IsFiniteMeasure P]

/-- The speaker's rational belief of (12) is the posterior over states given an observation at
an access, against the prior. -/
noncomputable def belief (a : Access) : Kernel Obs State := (obs a)†P

instance (a : Access) : IsMarkovKernel (belief P a) := inferInstanceAs (IsMarkovKernel ((obs a)†P))

theorem belief_apply_singleton_ne_zero {a : Access} {o : Obs} {s : State} (hP : P {s} ≠ 0)
    (h : hypergeometricCount 10 s a o ≠ 0) : belief P a o {s} ≠ 0 :=
  have ho := (obs_apply_singleton_ne_zero_iff a s o).2 h
  (posterior_apply_singleton_ne_zero_iff _ _ (Measure.comp_apply_singleton_ne_zero _ _ hP ho) s).2
    ⟨hP, ho⟩

theorem belief_full {o : Obs} (hP : P {o} ≠ 0) : belief P 10 o = Measure.dirac o :=
  posterior_hypergeometric_self o P hP

end Belief

/-! ### Simple expressions, (13) to (15) -/

/-- The five simple expressions of Experiment 2. -/
inductive SimpleExpr where
  | certainlyNot
  | probablyNot
  | possibly
  | probably
  | certainly
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace SimpleExpr := ⊤

/-- The semantic thresholds of the three uncertainty expressions, free parameters of the
model. -/
structure Thresholds where
  /-- The threshold of *certainly*. -/
  certainly : ℝ
  /-- The threshold of *probably*. -/
  probably : ℝ
  /-- The threshold of *possibly*. -/
  possibly : ℝ

namespace Thresholds

variable (θ : Thresholds)

/-- Under the threshold semantics of (13) and (14), a positive expression holds where the
proportion of red balls exceeds its threshold, and a negated one where the proportion falls below
one less the threshold. -/
def meaning : SimpleExpr → State → Prop
  | .certainly, s => θ.certainly < proportion s
  | .probably, s => θ.probably < proportion s
  | .possibly, s => θ.possibly < proportion s
  | .probablyNot, s => proportion s < 1 - θ.probably
  | .certainlyNot, s => proportion s < 1 - θ.certainly

/-- The extension of a simple expression. -/
def ext (m : SimpleExpr) : Set State := {s | θ.meaning m s}

theorem ext_certainly_subset (h : θ.probably ≤ θ.certainly) :
    θ.ext .certainly ⊆ θ.ext .probably := fun _ hs ↦ lt_of_le_of_lt h hs

theorem ext_probably_subset (h : θ.possibly ≤ θ.probably) :
    θ.ext .probably ⊆ θ.ext .possibly := fun _ hs ↦ lt_of_le_of_lt h hs

theorem ext_certainlyNot_subset (h : θ.probably ≤ θ.certainly) :
    θ.ext .certainlyNot ⊆ θ.ext .probablyNot := fun s hs ↦ by
  simp only [ext, meaning, Set.mem_ofPred_eq] at hs ⊢
  linarith

end Thresholds

section Listener

variable (θ : Thresholds) (P : Measure State)

/-- The literal listener of (15) conditions the prior on the expression's extension. -/
noncomputable def L0 : Kernel SimpleExpr State := RSA.listener P (truthful θ.ext)

instance : IsFiniteKernel (L0 θ P) := inferInstanceAs (IsFiniteKernel (RSA.listener _ (truthful _)))

instance (m : SimpleExpr) : IsZeroOrProbabilityMeasure (L0 θ P m) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (RSA.listener _ (truthful _) m))

theorem isProbabilityMeasure_L0 [IsFiniteMeasure P] {m : SimpleExpr} (h : P (θ.ext m) ≠ 0) :
    IsProbabilityMeasure (L0 θ P m) :=
  ⟨listener_truthful_apply_univ P θ.ext h⟩

theorem L0_apply_singleton_of_notMem {m : SimpleExpr} {s : State} (h : s ∉ θ.ext m) :
    L0 θ P m {s} = 0 :=
  listener_truthful_apply_singleton_of_notMem P θ.ext h

theorem L0_real_of_notMem {m : SimpleExpr} {s : State} (h : s ∉ θ.ext m) :
    (L0 θ P m).real {s} = 0 := by
  rw [measureReal_def, L0_apply_singleton_of_notMem θ P h, ENNReal.toReal_zero]

theorem L0_real_of_mem {m : SimpleExpr} {s : State} (h : s ∈ θ.ext m) :
    (L0 θ P m).real {s} = P.real {s} / P.real (θ.ext m) :=
  listener_truthful_real_singleton P θ.ext h

end Listener

/-! ### The speaker, (16) and (17) -/

section Speaker

variable (lam : ℝ) (θ : Thresholds) (P : Measure State) [IsFiniteMeasure P]

/-- The expected utility of (16) is the negative Hellinger distance between the speaker's
belief after her observation and the literal listener's belief after the message. -/
noncomputable def utility (x : Obs × Access) (m : SimpleExpr) : ℝ :=
  -hellingerDist (belief P x.2 x.1) (L0 θ P m)

/-- The utility is minus the Hellinger distance of the paper's footnote on utilities. -/
theorem utility_eq (x : Obs × Access) (m : SimpleExpr) :
    utility θ P x m = -(√(∑ s, (√((belief P x.2 x.1).real {s}) - √((L0 θ P m).real {s})) ^ 2) /
      √2) := by
  simp [utility, hellingerDist, EuclideanSpace.dist_eq, Real.dist_eq]

theorem neg_one_le_utility (x : Obs × Access) (m : SimpleExpr) : -1 ≤ utility θ P x m :=
  neg_le_neg (hellingerDist_le_one _ _)

/-- The speaker of (17) is the softmax of the utility at the rationality `lam`. -/
noncomputable def speaker : Kernel (Obs × Access) SimpleExpr :=
  Kernel.softmax fun x m ↦ ((lam * utility θ P x m : ℝ) : EReal)

theorem speaker_apply_singleton_ne_zero (x : Obs × Access) (m : SimpleExpr) :
    speaker lam θ P x {m} ≠ 0 :=
  Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _

instance : IsMarkovKernel (speaker lam θ P) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨.possibly, EReal.coe_ne_bot _⟩)
    fun _ _ ↦ EReal.coe_ne_top _

/-- The speaker prefers the message of higher utility, whose literal listener lies closer to her
belief. -/
theorem speaker_real_lt_iff (hlam : 0 < lam) (x : Obs × Access) (m m' : SimpleExpr) :
    (speaker lam θ P x).real {m} < (speaker lam θ P x).real {m'} ↔
      utility θ P x m < utility θ P x m' := by
  rw [speaker, Kernel.softmax_coe_real_singleton_lt_iff, mul_lt_mul_iff_of_pos_left hlam]

/-- The speaker of [goodman-stuhlmuller-2013], with the Kullback–Leibler divergence in place
of the Hellinger distance (the paper's footnote on utilities). -/
noncomputable def klSpeaker : Kernel (Obs × Access) SimpleExpr :=
  RSA.speaker lam 0 (L0 θ P) fun x ↦ belief P x.2 x.1

theorem klSpeaker_probably_eq_zero (hlam : 0 < lam) (hθ : 3 / 10 ≤ θ.probably)
    (hP : P {3} ≠ 0) : klSpeaker lam θ P (3, 4) {.probably} = 0 := by
  refine (speaker_apply_singleton_eq_zero_iff_not_ac hlam).2 fun hac ↦ ?_
  have h0 : L0 θ P .probably {3} = 0 :=
    L0_apply_singleton_of_notMem θ P (not_lt.2 (by simpa [proportion] using hθ))
  exact belief_apply_singleton_ne_zero P hP (a := 4) (o := 3) (s := 3) (by decide +kernel) (hac h0)

end Speaker

/-! ### Complete access: informativity from the Hellinger distance -/

section FullAccess

variable {lam : ℝ} (θ : Thresholds) (P : Measure State) [IsFiniteMeasure P] {s : State}

theorem utility_full (hP : P {s} ≠ 0) {m : SimpleExpr} (hm : P (θ.ext m) ≠ 0) :
    utility θ P (s, 10) m = -√(1 - √((L0 θ P m).real {s})) := by
  have := isProbabilityMeasure_L0 θ P hm
  rw [utility, belief_full P hP, hellingerDist_dirac_left]

theorem utility_full_of_notMem (hP : P {s} ≠ 0) {m : SimpleExpr} (hm : P (θ.ext m) ≠ 0)
    (h : s ∉ θ.ext m) : utility θ P (s, 10) m = -1 := by
  rw [utility_full θ P hP hm, L0_real_of_notMem θ P h, Real.sqrt_zero, sub_zero, Real.sqrt_one]

theorem utility_full_of_mem (hP : P {s} ≠ 0) {m : SimpleExpr} (h : s ∈ θ.ext m) :
    utility θ P (s, 10) m = -√(1 - √(P.real {s} / P.real (θ.ext m))) := by
  rw [utility_full θ P hP (measure_pos_of_superset (Set.singleton_subset_iff.2 h) hP).ne',
    L0_real_of_mem θ P h]

theorem speaker_full_lt_of_notMem_of_mem (hlam : 0 < lam) (hP : P {s} ≠ 0) {m m' : SimpleExpr}
    (hm : P (θ.ext m) ≠ 0) (h : s ∉ θ.ext m) (h' : s ∈ θ.ext m') :
    (speaker lam θ P (s, 10)).real {m} < (speaker lam θ P (s, 10)).real {m'} := by
  rw [speaker_real_lt_iff lam θ P hlam, utility_full_of_notMem θ P hP hm h,
    utility_full_of_mem θ P hP h', neg_lt_neg_iff, Real.sqrt_lt' one_pos, one_pow,
    sub_lt_self_iff, Real.sqrt_pos]
  have hs : 0 < P.real {s} := ENNReal.toReal_pos hP (measure_ne_top _ _)
  exact div_pos hs (hs.trans_le (measureReal_mono (Set.singleton_subset_iff.2 h')))

/-- With complete access, among true messages the one whose extension carries less prior
mass, the more informative one, is preferred. -/
theorem speaker_full_lt_iff_of_mem (hlam : 0 < lam) (hP : P {s} ≠ 0) {m m' : SimpleExpr}
    (h : s ∈ θ.ext m) (h' : s ∈ θ.ext m') :
    (speaker lam θ P (s, 10)).real {m} < (speaker lam θ P (s, 10)).real {m'} ↔
      P.real (θ.ext m') < P.real (θ.ext m) := by
  have hs : 0 < P.real {s} := ENNReal.toReal_pos hP (measure_ne_top _ _)
  have hE : 0 < P.real (θ.ext m) := hs.trans_le (measureReal_mono (Set.singleton_subset_iff.2 h))
  have hE' : 0 < P.real (θ.ext m') :=
    hs.trans_le (measureReal_mono (Set.singleton_subset_iff.2 h'))
  have hle : √(P.real {s} / P.real (θ.ext m')) ≤ 1 :=
    Real.sqrt_le_one.2 ((div_le_one hE').2 (measureReal_mono (Set.singleton_subset_iff.2 h')))
  rw [speaker_real_lt_iff lam θ P hlam, utility_full_of_mem θ P hP h,
    utility_full_of_mem θ P hP h', neg_lt_neg_iff, Real.sqrt_lt_sqrt_iff (by linarith),
    sub_lt_sub_iff_left, Real.sqrt_lt_sqrt_iff (div_nonneg hs.le hE.le),
    div_lt_div_iff_of_pos_left hs hE hE']

/-- With complete access and a prior positive on every state, a message strictly entailing
another is preferred to it whenever both are true, the scalar implicature of the introductory
example. -/
theorem speaker_full_lt_of_ssubset (hlam : 0 < lam) (hP : ∀ s, P {s} ≠ 0) {m m' : SimpleExpr}
    (hsub : θ.ext m ⊂ θ.ext m') (h : s ∈ θ.ext m) :
    (speaker lam θ P (s, 10)).real {m'} < (speaker lam θ P (s, 10)).real {m} := by
  obtain ⟨hle, x, hx, hxm⟩ := Set.ssubset_iff_exists.1 hsub
  rw [speaker_full_lt_iff_of_mem θ P hlam (hP s) (hle h) h]
  have hx0 : 0 < P.real {x} := ENNReal.toReal_pos (hP x) (measure_ne_top _ _)
  calc P.real (θ.ext m) < P.real (θ.ext m) + P.real {x} := by linarith
    _ = P.real (θ.ext m ∪ {x}) := by
        rw [measureReal_union₀ MeasurableSet.of_discrete.nullMeasurableSet
      (Set.disjoint_singleton_right.2 hxm).aedisjoint]
    _ ≤ P.real (θ.ext m') :=
        measureReal_mono (Set.union_subset hle (Set.singleton_subset_iff.2 hx))

end FullAccess

/-! ### The pragmatic listener, (18) to (20) -/

section PragmaticListener

variable (lam : ℝ) (θ : Thresholds) (P : Measure State) (A : Measure Access)

/-- The joint prior of (18) over states, observations and accesses combines the state prior,
the access prior, and the observation given both. -/
noncomputable def joint : Measure (State × (Obs × Access)) :=
  ∑ x, (P {x.1} * A {x.2.2} * obs x.2.2 x.1 {x.2.1}) • Measure.dirac x

theorem joint_apply_singleton (x : State × (Obs × Access)) :
    joint P A {x} = P {x.1} * A {x.2.2} * obs x.2.2 x.1 {x.2.1} := by
  simp only [joint, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable [IsFiniteMeasure P] [IsFiniteMeasure A]

instance : IsFiniteMeasure (joint P A) :=
  ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    exact ENNReal.sum_lt_top.2 fun x _ ↦ by
      rw [joint_apply_singleton]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _))
        (measure_lt_top _ _)⟩

/-- As the listener models the speaker, her choice depends on the observation and the access
alone. -/
noncomputable def jointSpeaker : Kernel (State × (Obs × Access)) SimpleExpr :=
  Kernel.ofFunOfCountable fun x ↦ speaker lam θ P x.2

instance : IsMarkovKernel (jointSpeaker lam θ P) :=
  ⟨fun x ↦ by rw [jointSpeaker, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- The pragmatic listener of (18) inverts the speaker against the joint prior; its first
marginal is the state listener of (19), its second the observation listener of (20). -/
noncomputable def listener : Kernel SimpleExpr (State × (Obs × Access)) :=
  RSA.listener (joint P A) (jointSpeaker lam θ P)

theorem listener_fst_apply_singleton_ne_zero {s : State} (hP : P {s} ≠ 0) (hA : A {0} ≠ 0)
    (m : SimpleExpr) : (listener lam θ P A m).fst {s} ≠ 0 := by
  have hj : joint P A {(s, (0, 0))} ≠ 0 := by
    rw [joint_apply_singleton]
    exact mul_ne_zero (mul_ne_zero hP hA)
      ((obs_apply_singleton_ne_zero_iff 0 s 0).2 (by simp))
  have hs : jointSpeaker lam θ P (s, (0, 0)) {m} ≠ 0 := speaker_apply_singleton_ne_zero lam θ P _ m
  exact (RSA.listener_fst_apply_singleton_ne_zero_iff _ _ m s).2 ⟨(0, 0), hj, hs⟩

end PragmaticListener

/-! ### Complex expressions, (22) to (25) -/

/-- The inner expressions of Experiment 3. -/
inductive Inner where
  | likely
  | possible
  | unlikely
  deriving DecidableEq, Fintype

instance : MeasurableSpace Inner := ⊤

/-- The outer modifiers of Experiment 3; the bare copula is the simple expression. -/
inductive Outer where
  | certainly
  | probably
  | might
  deriving DecidableEq, Fintype

instance : MeasurableSpace Outer := ⊤

/-- The semantic thresholds of Experiment 3's inner and outer expressions. -/
structure ComplexThresholds where
  /-- The threshold of the inner *likely*. -/
  likely : ℝ
  /-- The threshold of the inner *possible*. -/
  possible : ℝ
  /-- The threshold of the outer *certainly*. -/
  certainly : ℝ
  /-- The threshold of the outer *probably*. -/
  probably : ℝ
  /-- The threshold of the outer *might*. -/
  might : ℝ

namespace ComplexThresholds

variable (θ : ComplexThresholds)

/-- The threshold semantics of the inner expressions (22), *unlikely* the negation of
*likely*. -/
def inner : Inner → State → Prop
  | .likely, s => θ.likely < proportion s
  | .possible, s => θ.possible < proportion s
  | .unlikely, s => proportion s < 1 - θ.likely

/-- The threshold of an outer modifier. -/
def outer : Outer → ℝ
  | .certainly => θ.certainly
  | .probably => θ.probably
  | .might => θ.might

/-- The extension of an inner expression. -/
def innerExt (X : Inner) : Set State := {s | θ.inner X s}

variable (P : Measure State) [IsFiniteMeasure P]

/-- Under the compositional semantics of (23), a complex expression holds at an observation
exactly when the belief it induces gives the inner expression's extension more than the outer
threshold. -/
def complex (Y : Outer) (X : Inner) : Set (Obs × Access) :=
  {x | θ.outer Y < (belief P x.2 x.1).real (θ.innerExt X)}

theorem mem_complex_full {s : State} (hP : P {s} ≠ 0) {Y : Outer} (h0 : 0 ≤ θ.outer Y)
    (X : Inner) : (s, 10) ∈ θ.complex P Y X ↔ s ∈ θ.innerExt X ∧ θ.outer Y < 1 := by
  classical
  simp only [complex, Set.mem_ofPred_eq, belief_full P hP, measureReal_def,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_apply, Pi.one_apply]
  split_ifs with hs
  · simp [hs]
  · simpa [hs] using h0

/-- The literal listener for complex expressions of (25) conditions the observation prior of
(24), the marginal of the joint prior, on the expression's extension. -/
noncomputable def complexL0 (A : Measure Access) [IsFiniteMeasure A] :
    Kernel (Outer × Inner) (Obs × Access) :=
  RSA.listener (joint P A).snd (truthful fun m : Outer × Inner ↦ θ.complex P m.1 m.2)

end ComplexThresholds

end HerbstrittFranke2019
