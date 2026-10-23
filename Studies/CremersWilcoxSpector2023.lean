module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.Probability.Kernel.Module
public import Linglib.Core.Probability.UniformOn
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Semantics.Exhaustification.Finite

/-!
# Exhaustivity and anti-exhaustivity in the Rational Speech Act framework

A listener who hears *A* where *A and B* was available infers that B is false. In the
baseline Rational Speech Act model a prior biased towards the world of both A and B reverses
the inference: the listener is anti-exhaustive exactly when the log odds of the prior exceed
the cost disadvantage of *A and not B* over *A and B*, whatever the rationality. Lexical
uncertainty over free strengthenings and the wonky-world models stay anti-exhaustive for
suitable priors, while grammatical lexical uncertainty, the lexical-intentions speaker and
the supervaluationist speaker keep the posterior of both below the prior whenever *A and B*
costs no more than *A and not B*. The experiment finds no anti-exhaustivity.

We state each model on the substrate's kernel face and prove the paper's conditions on reals
for an arbitrary prior, rationality and costs. The lexical-uncertainty models and the Bayesian
wonky model are given in the paper both as a joint posterior over worlds and a latent and as the
inverse of the speaker averaged over the latent, and the two agree (`luJointListener_fst`,
`bayesWonkyJointListener_fst`).

## TODO

* The non-Bayesian wonky model's limits in the prior and the Bayesian wonky model's
  wonkiness threshold are not derived.

## References

* [A. Cremers, E. G. Wilcox, B. Spector, *Exhaustivity and anti-exhaustivity in the RSA
  framework* (2023)][cremers-wilcox-spector-2023]
* [M. C. Frank, N. D. Goodman, *Predicting pragmatic reasoning in language games*
  (2012)][frank-goodman-2012]
* [J. Degen et al., *Wonky worlds* (2015)][degen-etal-2015]
* [B. Spector, *The pragmatics of plural predication* (2017)][spector-2017]
* [L. Bergen, R. Levy, N. D. Goodman, *Pragmatic reasoning through semantic inference*
  (2016)][bergen-levy-goodman-2016]
* [M. Franke, L. Bergen, *Theory-driven statistical modeling for semantics and pragmatics*
  (2020)][franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CremersWilcoxSpector2023

/-! ### Worlds, messages and interpretations -/

/-- In one world only A is true, in the other both A and B are. -/
inductive World where
  | wa
  | wab
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

/-- The three messages are *A*, *A and B* and *A and not B*. -/
inductive Message where
  | a
  | aAndB
  | aAndNotB
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Message := ⊤

/-- The literal meaning of each message. -/
def truth : Message → World → Bool
  | .a, _ => true
  | .aAndB, .wab => true
  | .aAndB, .wa => false
  | .aAndNotB, .wa => true
  | .aAndNotB, .wab => false

/-- *A* has the scale-mate *A and B* as its alternative. -/
def alternatives : Message → List (World → Bool)
  | .a => [truth .a, truth .aAndB]
  | u => [truth u]

/-- The exhaustified meaning, by innocent exclusion of the alternatives. -/
def exh (u : Message) (w : World) : Bool :=
  decide (w ∈ Exhaustification.innocent.exh (Exhaustification.altsFromPreds (alternatives u))
    (Exhaustification.predToFinset (truth u)))

theorem exh_a : exh .a = truth .aAndNotB := by decide

/-- *A and B* has no stronger alternative. -/
theorem exh_aAndB : exh .aAndB = truth .aAndB := by decide

/-- *A and not B* has no stronger alternative. -/
theorem exh_aAndNotB : exh .aAndNotB = truth .aAndNotB := by decide

/-- An interpretation function under which every message is true somewhere and every world
is described by some message, so that the literal listener and the speaker are defined. -/
structure Meaning where
  /-- The truth value of a message at a world. -/
  sat : Message → World → Bool
  /-- Every message is true somewhere. -/
  exists_world : ∀ u, ∃ w, sat u w = true
  /-- Every world is described by some message. -/
  exists_message : ∀ w, ∃ u, sat u w = true

namespace Meaning

variable (m : Meaning)

/-- The extension of a message. -/
def extension (u : Message) : Set World := {w | m.sat u w = true}

theorem mem_extension {u : Message} {w : World} : w ∈ m.extension u ↔ m.sat u w = true :=
  Iff.rfl

theorem extension_eq_univ {u : Message} (h : ∀ w, m.sat u w = true) :
    m.extension u = Set.univ :=
  Set.eq_univ_of_forall h

theorem extension_eq_singleton {u : Message} {w : World}
    (h : ∀ w', m.sat u w' = true ↔ w' = w) : m.extension u = {w} :=
  Set.ext fun w' ↦ (h w').trans Set.mem_singleton_iff.symm

end Meaning

/-- The literal interpretation. -/
def literal : Meaning := ⟨truth, by decide, by decide⟩

/-- The exhaustified interpretation, *A* read as *A and not B*. -/
def exhaustified : Meaning := ⟨exh, by decide, by decide⟩

/-- The anti-exhaustive interpretation of the free lexical-uncertainty model, *A* read as
*A and B*. -/
def antiExhaustive : Meaning :=
  ⟨fun u w ↦ match u with | .a => truth .aAndB w | u => truth u w, by decide, by decide⟩

/-- The two grammatical interpretations, literal and exhaustified. -/
inductive Interpretation where
  | lit
  | exh
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Interpretation := ⊤

/-- The meaning of a grammatical interpretation. -/
def Interpretation.meaning : Interpretation → Meaning
  | .lit => literal
  | .exh => exhaustified

/-- The three interpretations of the free lexical-uncertainty model. -/
inductive FreeInterpretation where
  | lit
  | exh
  | antiExh
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace FreeInterpretation := ⊤

/-- The meaning of a free interpretation. -/
def FreeInterpretation.meaning : FreeInterpretation → Meaning
  | .lit => literal
  | .exh => exhaustified
  | .antiExh => antiExhaustive

/-- The wonky-world listener considers two backgrounds, in which the speaker assumes a uniform
prior or the measured one. -/
inductive Background where
  | wonky
  | measured
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Background := ⊤

/-- The question under discussion asks whether A holds, which the two worlds answer alike, or
which world obtains. -/
inductive QUD where
  | coarse
  | fine
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace QUD := ⊤

section Sums

variable {β : Type*} [AddCommMonoid β]

theorem sum_world (f : World → β) : ∑ w, f w = f .wa + f .wab := by
  rw [show ∑ w, f w = f .wa + (f .wab + 0) from rfl, add_zero]

theorem sum_message (f : Message → β) : ∑ u, f u = f .a + f .aAndB + f .aAndNotB := by
  rw [show ∑ u, f u = f .a + (f .aAndB + (f .aAndNotB + 0)) from rfl, add_zero, add_assoc]

theorem sum_interpretation (f : Interpretation → β) : ∑ i, f i = f .lit + f .exh := by
  rw [show ∑ i, f i = f .lit + (f .exh + 0) from rfl, add_zero]

theorem sum_freeInterpretation (f : FreeInterpretation → β) :
    ∑ i, f i = f .lit + f .exh + f .antiExh := by
  rw [show ∑ i, f i = f .lit + (f .exh + (f .antiExh + 0)) from rfl, add_zero, add_assoc]

theorem sum_background (f : Background → β) : ∑ b, f b = f .wonky + f .measured := by
  rw [show ∑ b, f b = f .wonky + (f .measured + 0) from rfl, add_zero]

theorem sum_qud (f : QUD → β) : ∑ q, f q = f .coarse + f .fine := by
  rw [show ∑ q, f q = f .coarse + (f .fine + 0) from rfl, add_zero]

end Sums

/-! ### Priors and parameters -/

/-- A model is fixed by the prior probability of both A and B, the rationality, and the costs
of the two conjunctions, *A* itself costing nothing. -/
structure Setting where
  /-- The prior probability of the world where both A and B hold. -/
  p : ℝ
  /-- The rationality, the paper's λ. -/
  lam : ℝ
  /-- The cost of *A and B*. -/
  cAndB : ℝ
  /-- The cost of *A and not B*. -/
  cAndNotB : ℝ
  /-- The world of both has positive prior probability. -/
  p_pos : 0 < p
  /-- The world of A alone has positive prior probability. -/
  p_lt_one : p < 1
  /-- The rationality is positive. -/
  lam_pos : 0 < lam

namespace Setting

variable (s : Setting)

/-- The cost of a message. -/
def cost : Message → ℝ
  | .a => 0
  | .aAndB => s.cAndB
  | .aAndNotB => s.cAndNotB

/-- The cost factor of a message is the exponential of its cost scaled by the rationality. -/
noncomputable abbrev costFactor (u : Message) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(s.lam * s.cost u)))

theorem costFactor_ne_zero (u : Message) : s.costFactor u ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem costFactor_ne_top (u : Message) : s.costFactor u ≠ ∞ := ENNReal.ofReal_ne_top

theorem costFactor_toReal (u : Message) :
    (s.costFactor u).toReal = Real.exp (-(s.lam * s.cost u)) :=
  ENNReal.toReal_ofReal (Real.exp_pos _).le

/-- The paper's `f_λ` is the logistic function with rate the rationality. -/
noncomputable def logistic (x : ℝ) : ℝ := Real.sigmoid (s.lam * x)

theorem logistic_nonneg (x : ℝ) : 0 ≤ s.logistic x := Real.sigmoid_nonneg _

theorem logistic_lt_iff {x y : ℝ} : s.logistic x < s.logistic y ↔ x < y := by
  rw [logistic, logistic, Real.sigmoid_lt_iff, mul_lt_mul_iff_of_pos_left s.lam_pos]

theorem logistic_lt {x y : ℝ} (h : x < y) : s.logistic x < s.logistic y :=
  s.logistic_lt_iff.mpr h

/-- The weight of a world under the measured prior. -/
noncomputable def priorWeight : World → ℝ≥0∞
  | .wa => ENNReal.ofReal (1 - s.p)
  | .wab => ENNReal.ofReal s.p

/-- The measured prior over the two worlds. -/
noncomputable def prior : Measure World := ∑ w, s.priorWeight w • Measure.dirac w

theorem prior_apply_singleton (w : World) : s.prior {w} = s.priorWeight w :=
  Measure.sum_smul_dirac_apply_singleton _ w

theorem prior_wa : s.prior {.wa} = ENNReal.ofReal (1 - s.p) := prior_apply_singleton s .wa

theorem prior_wab : s.prior {.wab} = ENNReal.ofReal s.p := prior_apply_singleton s .wab

instance : IsProbabilityMeasure s.prior :=
  ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton, sum_world, prior_wa, prior_wab,
      ← ENNReal.ofReal_add (by linarith [s.p_lt_one]) s.p_pos.le, sub_add_cancel,
      ENNReal.ofReal_one]⟩

theorem prior_ne_zero (w : World) : s.prior {w} ≠ 0 := by
  cases w
  · exact prior_wa s ▸ (ENNReal.ofReal_pos.mpr (by linarith [s.p_lt_one])).ne'
  · exact prior_wab s ▸ (ENNReal.ofReal_pos.mpr s.p_pos).ne'

theorem prior_support (w : World) (_ : s.prior {w} ≠ 0) : w = .wab ∨ w = .wa := by
  cases w <;> simp

theorem prior_real_wa : s.prior.real {.wa} = 1 - s.p := by
  rw [measureReal_def, prior_wa, ENNReal.toReal_ofReal (by linarith [s.p_lt_one])]

theorem prior_real_wab : s.prior.real {.wab} = s.p := by
  rw [measureReal_def, prior_wab, ENNReal.toReal_ofReal s.p_pos.le]

end Setting

/-- The wonky prior is uniform over the two worlds. -/
noncomputable def wonkyPrior : Measure World := uniformOn Set.univ

instance : IsProbabilityMeasure wonkyPrior :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

theorem wonkyPrior_apply_singleton (w : World) : wonkyPrior {w} = 2⁻¹ := by
  rw [wonkyPrior, uniformOn_univ_apply_singleton, show Fintype.card World = 2 from rfl]
  norm_cast

theorem wonkyPrior_ne_zero (w : World) : wonkyPrior {w} ≠ 0 := by
  rw [wonkyPrior_apply_singleton]; simp

theorem wonkyPrior_real_singleton (w : World) : wonkyPrior.real {w} = 2⁻¹ := by
  rw [wonkyPrior, uniformOn_univ_real_singleton, show Fintype.card World = 2 from rfl]
  norm_num

/-! ### The literal listener and the speaker under an interpretation (eqs. 1 to 3) -/

section Speaker

variable (P : Measure World) (hP : ∀ w, P {w} ≠ 0) (m : Meaning)

/-- The literal listener conditions the prior on the message's extension (eq. 1). -/
noncomputable def L0 : Kernel Message World :=
  RSA.listener P (RSA.truthful m.extension)

instance : IsFiniteKernel (L0 P m) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ (RSA.truthful _)))

theorem L0_ne_top (u : Message) (w : World) : L0 P m u {w} ≠ ∞ := measure_ne_top _ _

theorem L0_eq_zero {u : Message} {w : World} (h : m.sat u w = false) : L0 P m u {w} = 0 :=
  RSA.listener_truthful_apply_singleton_of_notMem P m.extension
    (by rw [Meaning.mem_extension, h]; exact Bool.false_ne_true)

theorem L0_literal_a [IsProbabilityMeasure P] (w : World) : L0 P literal .a {w} = P {w} :=
  RSA.listener_truthful_apply_singleton_of_eq_univ P literal.extension
    (literal.extension_eq_univ fun w ↦ by cases w <;> rfl) w

variable (s : Setting)

/-- The speaker is the softmax of the literal listener's log probability less the cost, scaled
by the rationality (eqs. 2 and 3). -/
noncomputable def speaker : Kernel World Message := RSA.speaker s.lam s.cost (L0 P m) Measure.dirac

instance : IsFiniteKernel (speaker P m s) := inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

theorem weight_ne_top (u : Message) (w : World) :
    L0 P m u {w} ^ s.lam * s.costFactor u ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg s.lam_pos.le (L0_ne_top P m u w))
    (s.costFactor_ne_top u)

theorem weight_eq_zero {u : Message} {w : World} (h : m.sat u w = false) :
    L0 P m u {w} ^ s.lam * s.costFactor u = 0 := by
  rw [L0_eq_zero P m h, ENNReal.zero_rpow_of_pos s.lam_pos, zero_mul]

theorem speaker_eq_zero {u : Message} {w : World} (h : m.sat u w = false) :
    speaker P m s w {u} = 0 :=
  RSA.speaker_dirac_apply_singleton_eq_zero s.lam_pos (L0_eq_zero P m h)

variable [IsFiniteMeasure P]

include hP

theorem L0_ne_zero {u : Message} {w : World} (h : m.sat u w = true) : L0 P m u {w} ≠ 0 := by
  rw [L0, RSA.listener_truthful_apply_singleton P m.extension h]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hP w)

theorem L0_eq_one {u : Message} {w : World} (h : ∀ w', m.sat u w' = true ↔ w' = w) :
    L0 P m u {w} = 1 :=
  RSA.listener_truthful_apply_singleton_of_eq_singleton P m.extension
    (m.extension_eq_singleton h) (hP w)

theorem L0_apply_univ (u : Message) : L0 P m u Set.univ = 1 :=
  let ⟨w, hw⟩ := m.exists_world u
  RSA.listener_truthful_apply_univ P m.extension fun h ↦
    hP w (measure_mono_null (Set.singleton_subset_iff.mpr hw) h)

theorem weight_toReal {u : Message} {w : World} (h : m.sat u w = true) :
    (L0 P m u {w} ^ s.lam * s.costFactor u).toReal =
      Real.exp (s.lam * (Real.log (L0 P m u {w}).toReal - s.cost u)) := by
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    Real.rpow_def_of_pos (ENNReal.toReal_pos (L0_ne_zero P hP m h) (L0_ne_top P m u w)),
    Setting.costFactor_toReal, ← Real.exp_add]
  congr 1; ring

theorem speaker_ne_zero {u : Message} {w : World} (h : m.sat u w = true) :
    speaker P m s w {u} ≠ 0 :=
  RSA.speaker_dirac_apply_singleton_ne_zero s.lam_pos.le (L0_ne_zero P hP m h)

/-- Between two messages true at a world, the speaker prefers the one of higher utility. -/
theorem speaker_real_singleton_lt_iff {u v : Message} {w : World} (hu : m.sat u w = true)
    (hv : m.sat v w = true) :
    (speaker P m s w).real {u} < (speaker P m s w).real {v} ↔
      Real.log (L0 P m u {w}).toReal - s.cost u < Real.log (L0 P m v {w}).toReal - s.cost v :=
  RSA.speaker_dirac_real_singleton_lt_iff_log s.lam_pos (L0_ne_zero P hP m hu)
    (L0_ne_zero P hP m hv)

theorem speaker_real_singleton_of_pair {u v : Message} {w : World} (huv : u ≠ v)
    (hu : m.sat u w = true) (hv : m.sat v w = true)
    (hsupp : ∀ x, m.sat x w = true → x = u ∨ x = v) :
    (speaker P m s w).real {u} =
      s.logistic ((Real.log (L0 P m u {w}).toReal - s.cost u) -
        (Real.log (L0 P m v {w}).toReal - s.cost v)) :=
  RSA.speaker_dirac_real_singleton_of_pair s.lam_pos huv (L0_ne_zero P hP m hu)
    (L0_ne_zero P hP m hv) fun x hx ↦
      hsupp x (of_not_not fun h ↦ hx (L0_eq_zero P m (Bool.eq_false_iff.mpr h)))

end Speaker

/-- The literal listener with the measured prior. -/
noncomputable abbrev Setting.L0 (s : Setting) (m : Meaning) : Kernel Message World :=
  CremersWilcoxSpector2023.L0 s.prior m

/-- The speaker with the measured prior in the literal listener. -/
noncomputable abbrev Setting.speaker (s : Setting) (m : Meaning) : Kernel World Message :=
  CremersWilcoxSpector2023.speaker s.prior m s

/-! ### Closed forms: the speaker's use of *A* is a logistic function -/

section ClosedForms

variable (P : Measure World) [IsProbabilityMeasure P] (hP : ∀ w, P {w} ≠ 0) (s : Setting)
include hP

theorem speaker_literal_wab_a :
    (speaker P literal s .wab).real {.a} = s.logistic (s.cAndB + Real.log (P.real {.wab})) := by
  rw [speaker_real_singleton_of_pair P hP literal s (v := .aAndB) (by decide) rfl rfl
    (by decide)]
  simp (disch := decide) only [L0_literal_a, L0_eq_one P hP literal, ENNReal.toReal_one,
    Real.log_one, Setting.cost, ← measureReal_def]
  congr 1; ring

theorem speaker_literal_wa_a :
    (speaker P literal s .wa).real {.a} = s.logistic (s.cAndNotB + Real.log (P.real {.wa})) := by
  rw [speaker_real_singleton_of_pair P hP literal s (v := .aAndNotB) (by decide) rfl rfl
    (by decide)]
  simp (disch := decide) only [L0_literal_a, L0_eq_one P hP literal, ENNReal.toReal_one,
    Real.log_one, Setting.cost, ← measureReal_def]
  congr 1; ring

end ClosedForms

section SettingClosedForms

variable (s : Setting)

theorem speaker_exhaustified_wa_a :
    (s.speaker exhaustified .wa).real {.a} = s.logistic s.cAndNotB := by
  rw [Setting.speaker, speaker_real_singleton_of_pair s.prior s.prior_ne_zero exhaustified s
    (v := .aAndNotB) (by decide) (by decide) (by decide) (by decide)]
  simp (disch := decide) only [L0_eq_one s.prior s.prior_ne_zero exhaustified,
    ENNReal.toReal_one, Real.log_one, Setting.cost]
  congr 1; ring

theorem speaker_exhaustified_wab_a : (s.speaker exhaustified .wab).real {.a} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (speaker_eq_zero _ _ _ (by decide))

theorem speaker_antiExhaustive_wab_a :
    (s.speaker antiExhaustive .wab).real {.a} = s.logistic s.cAndB := by
  rw [Setting.speaker, speaker_real_singleton_of_pair s.prior s.prior_ne_zero antiExhaustive s
    (v := .aAndB) (by decide) rfl rfl (by decide)]
  simp (disch := decide) only [L0_eq_one s.prior s.prior_ne_zero antiExhaustive,
    ENNReal.toReal_one, Real.log_one, Setting.cost]
  congr 1; ring

theorem speaker_antiExhaustive_wa_a : (s.speaker antiExhaustive .wa).real {.a} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (speaker_eq_zero _ _ _ rfl)

end SettingClosedForms

/-! ### The baseline model (§3) -/

section Baseline

variable (s : Setting)

/-- In the world of both, the speaker prefers *A* to *A and B* exactly when the information
*A and B* would add, the negated log prior, does not exceed its cost (6a). -/
theorem baseline_aAndB_lt_a_iff :
    (s.speaker literal .wab).real {.aAndB} < (s.speaker literal .wab).real {.a} ↔
      -s.cAndB < Real.log s.p := by
  rw [Setting.speaker, speaker_real_singleton_lt_iff s.prior s.prior_ne_zero literal s rfl rfl]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero literal,
    ENNReal.toReal_one, Real.log_one, Setting.cost, ← measureReal_def, Setting.prior_real_wab,
    zero_sub, sub_zero]

/-- In the world of A alone, the speaker prefers *A and not B* to *A* exactly when the
negated log prior exceeds its cost (7). -/
theorem baseline_a_lt_aAndNotB_iff :
    (s.speaker literal .wa).real {.a} < (s.speaker literal .wa).real {.aAndNotB} ↔
      Real.log (1 - s.p) < -s.cAndNotB := by
  rw [Setting.speaker, speaker_real_singleton_lt_iff s.prior s.prior_ne_zero literal s rfl rfl]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero literal,
    ENNReal.toReal_one, Real.log_one, Setting.cost, ← measureReal_def, Setting.prior_real_wa,
    zero_sub, sub_zero]

theorem comp_speaker_literal_ne_zero (u : Message) : (s.speaker literal ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  Measure.comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w) (speaker_ne_zero _ s.prior_ne_zero _ s hw)

/-- The pragmatic listener (eq. 4). -/
noncomputable def listener : Kernel Message World :=
  RSA.listener s.prior (s.speaker literal)

theorem prior_lt_listener_iff_speaker_lt :
    s.prior.real {.wab} < (listener s .a).real {.wab} ↔
      (s.speaker literal .wa).real {.a} < (s.speaker literal .wab).real {.a} := by
  rw [listener, RSA.listener_apply_eq_posterior _ _ (comp_speaker_literal_ne_zero s _)]
  exact real_lt_posterior_real_singleton_iff_of_pair (s.speaker literal) s.prior (by decide)
    s.prior_support (comp_speaker_literal_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _)

/-- The listener is anti-exhaustive exactly when the log odds of the prior exceed the cost
disadvantage of *A and not B* over *A and B*, whatever the rationality (6b). -/
theorem prior_lt_listener_iff :
    s.prior.real {.wab} < (listener s .a).real {.wab} ↔
      s.cAndNotB - s.cAndB < Real.log s.p - Real.log (1 - s.p) := by
  rw [prior_lt_listener_iff_speaker_lt, Setting.speaker, speaker_literal_wa_a _ s.prior_ne_zero,
    speaker_literal_wab_a _ s.prior_ne_zero, Setting.prior_real_wa, Setting.prior_real_wab,
    s.logistic_lt_iff, sub_lt_sub_iff, add_comm (Real.log s.p)]

theorem prior_lt_listener_iff_of_cost_eq (hc : s.cAndB = s.cAndNotB) :
    s.prior.real {.wab} < (listener s .a).real {.wab} ↔ 1 / 2 < s.p := by
  rw [prior_lt_listener_iff, hc, sub_self, sub_pos,
    Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

end Baseline

/-! ### Lexical uncertainty (§4.3)

The listener holds independent priors over worlds and interpretation functions, infers both from
the message and marginalizes on the interpretation, which is to invert the speaker averaged over
the interpretations (item 4). The grammatical version (EXH-LU) has the literal and the
exhaustified interpretations, and the free version (FREE-LU) adds the anti-exhaustive one. -/

section LexicalUncertainty

variable (s : Setting) {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  (meaning : I → Meaning)

/-- The speaker marginalised over equiprobable interpretation functions (item 4 of the §4.3
model). -/
noncomputable def luSpeaker : Kernel World Message :=
  ∑ i, uniformOn Set.univ {i} • s.speaker (meaning i)

instance : IsFiniteKernel (luSpeaker s meaning) :=
  IsFiniteKernel.finsetSum _ fun _ _ ↦ IsFiniteKernel.smul_of_ne_top _ (measure_ne_top _ _)

theorem luSpeaker_real_singleton (w : World) (u : Message) :
    (luSpeaker s meaning w).real {u} =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, (s.speaker (meaning i) w).real {u} := by
  simp only [luSpeaker, measureReal_def, sum_apply, smul_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, uniformOn_univ_apply_singleton, ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

theorem luSpeaker_apply_singleton_ne_zero_iff {w : World} {u : Message} :
    luSpeaker s meaning w {u} ≠ 0 ↔ ∃ i, s.speaker (meaning i) w {u} ≠ 0 := by
  simp [luSpeaker, Measure.finsetSum_apply, uniformOn_univ_singleton_ne_zero]

variable [Nonempty I] in
theorem comp_luSpeaker_ne_zero (u : Message) : (luSpeaker s meaning ∘ₘ s.prior) {u} ≠ 0 :=
  let i := Classical.arbitrary I
  let ⟨w, hw⟩ := (meaning i).exists_world u
  Measure.comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w)
    ((luSpeaker_apply_singleton_ne_zero_iff s meaning).mpr
      ⟨i, speaker_ne_zero _ s.prior_ne_zero _ s hw⟩)

/-- The Bayesian inverse of the averaged speaker (item 4 of the §4.3 model). -/
noncomputable def luListener : Kernel Message World := RSA.listener s.prior (luSpeaker s meaning)

/-- The joint posterior over worlds and interpretation functions, under independent priors over
the two. -/
noncomputable def luJointListener : Kernel Message (World × I) :=
  RSA.listener (s.prior.prod (uniformOn Set.univ)) fun p ↦ s.speaker (meaning p.2) p.1

/-- The joint posterior marginalized on interpretation functions is the listener of item 4: the
two descriptions of the model in §4.3 agree. -/
theorem luJointListener_fst : (luJointListener s meaning).fst = luListener s meaning := by
  rw [luJointListener, RSA.listener_prod_fst, luListener]
  congr 1
  ext w : 1
  simp [luSpeaker]

theorem luListener_exh_lt_prior (hc : s.cAndB ≤ s.cAndNotB) :
    (luListener s Interpretation.meaning .a).real {.wab} < s.prior.real {.wab} := by
  rw [luListener, RSA.listener_apply_eq_posterior _ _ (comp_luSpeaker_ne_zero s _ _),
    posterior_real_singleton_lt_iff_of_pair _ _ (by decide) s.prior_support
      (comp_luSpeaker_ne_zero s _ _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    luSpeaker_real_singleton, luSpeaker_real_singleton]
  simp only [sum_interpretation, Interpretation.meaning]
  rw [speaker_exhaustified_wab_a, speaker_exhaustified_wa_a, Setting.speaker,
    speaker_literal_wab_a _ s.prior_ne_zero, speaker_literal_wa_a _ s.prior_ne_zero,
    Setting.prior_real_wab, Setting.prior_real_wa]
  have h₁ := s.logistic_lt (show s.cAndB + Real.log s.p < s.cAndNotB by
    linarith [Real.log_neg s.p_pos s.p_lt_one])
  have h₂ := s.logistic_nonneg (s.cAndNotB + Real.log (1 - s.p))
  rw [show Fintype.card Interpretation = 2 from rfl, Nat.cast_ofNat]
  linarith

theorem prior_lt_luListener_free_iff :
    s.prior.real {.wab} < (luListener s FreeInterpretation.meaning .a).real {.wab} ↔
      s.logistic (s.cAndNotB + Real.log (1 - s.p)) + s.logistic s.cAndNotB <
        s.logistic (s.cAndB + Real.log s.p) + s.logistic s.cAndB := by
  rw [luListener, RSA.listener_apply_eq_posterior _ _ (comp_luSpeaker_ne_zero s _ _),
    real_lt_posterior_real_singleton_iff_of_pair _ _ (by decide) s.prior_support
      (comp_luSpeaker_ne_zero s _ _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    luSpeaker_real_singleton, luSpeaker_real_singleton]
  simp only [sum_freeInterpretation, FreeInterpretation.meaning]
  rw [speaker_exhaustified_wab_a, speaker_exhaustified_wa_a, speaker_antiExhaustive_wab_a,
    speaker_antiExhaustive_wa_a, Setting.speaker, speaker_literal_wab_a _ s.prior_ne_zero,
    speaker_literal_wa_a _ s.prior_ne_zero, Setting.prior_real_wab, Setting.prior_real_wa]
  have hI : (0 : ℝ) < (Fintype.card FreeInterpretation : ℝ)⁻¹ := by positivity
  constructor <;> intro h <;> nlinarith

theorem prior_lt_luListener_free_iff_of_cost_eq (hc : s.cAndB = s.cAndNotB) :
    s.prior.real {.wab} < (luListener s FreeInterpretation.meaning .a).real {.wab} ↔
      1 / 2 < s.p := by
  rw [prior_lt_luListener_free_iff, hc, add_lt_add_iff_right, s.logistic_lt_iff,
    add_lt_add_iff_left, Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

end LexicalUncertainty

/-! ### Lexical intentions (§4.4) -/

section LexicalIntentions

variable (s : Setting)

/-- The literal listener of a message under a chosen interpretation (item 1 of the §4.4
model). -/
noncomputable def liL0 : Kernel (Message × Interpretation) World :=
  RSA.listener s.prior (RSA.truthful fun x ↦ x.2.meaning.extension x.1)

instance : IsFiniteKernel (liL0 s) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ (RSA.truthful _)))

theorem liL0_apply (x : Message × Interpretation) : liL0 s x = s.L0 x.2.meaning x.1 := by
  rw [liL0, RSA.listener_truthful_apply]
  exact (RSA.listener_truthful_apply _ _ _).symm

/-- The speaker over messages and interpretations (item 3 of the §4.4 model). -/
noncomputable def liSpeaker : Kernel World (Message × Interpretation) :=
  RSA.speaker s.lam (fun x ↦ s.cost x.1) (liL0 s) Measure.dirac

instance : IsFiniteKernel (liSpeaker s) := inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

/-- The speaker's messages, the interpretations marginalised (item 5 of the §4.4 model). -/
noncomputable def liMessageSpeaker : Kernel World Message := (liSpeaker s).map Prod.fst

instance : IsFiniteKernel (liMessageSpeaker s) :=
  inferInstanceAs (IsFiniteKernel (Kernel.map _ _))

theorem liMessageSpeaker_apply_singleton (w : World) (u : Message) :
    liMessageSpeaker s w {u} = liSpeaker s w {(u, .lit)} + liSpeaker s w {(u, .exh)} := by
  rw [liMessageSpeaker, Kernel.map_apply _ measurable_fst]
  exact (Measure.fst_apply_singleton (liSpeaker s w) u).trans (sum_interpretation _)

theorem liMessageSpeaker_real_singleton (w : World) (u : Message) :
    (liMessageSpeaker s w).real {u} =
      (liSpeaker s w).real {(u, .lit)} + (liSpeaker s w).real {(u, .exh)} := by
  rw [liMessageSpeaker, Kernel.map_apply _ measurable_fst]
  exact (Measure.fst_real_singleton_eq_sum (liSpeaker s w) u).trans (sum_interpretation _)

theorem liWeight_ne_top (w : World) (x : Message × Interpretation) :
    liL0 s x {w} ^ s.lam * s.costFactor x.1 ≠ ∞ := by
  rw [liL0_apply]
  exact weight_ne_top s.prior x.2.meaning s x.1 w

theorem liMessageSpeaker_real_wab_a :
    (liMessageSpeaker s .wab).real {.a} =
      Real.exp (s.lam * Real.log s.p) /
        (Real.exp (s.lam * Real.log s.p) + 2 * Real.exp (-(s.lam * s.cAndB))) := by
  rw [liMessageSpeaker_real_singleton, liSpeaker, RSA.speaker_dirac_eq_ofWeights,
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wab),
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wab), Fintype.sum_prod_type,
    sum_message]
  simp (disch := decide) only [sum_interpretation, liL0_apply, Interpretation.meaning, Setting.L0,
    weight_toReal s.prior s.prior_ne_zero, weight_eq_zero s.prior, ENNReal.toReal_zero]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero, ← measureReal_def,
    Setting.prior_real_wab, ENNReal.toReal_one, Real.log_one, Setting.cost, sub_zero, zero_sub,
    mul_neg, add_zero]
  ring

theorem liMessageSpeaker_real_wa_a :
    (liMessageSpeaker s .wa).real {.a} =
      (Real.exp (s.lam * Real.log (1 - s.p)) + 1) /
        (Real.exp (s.lam * Real.log (1 - s.p)) + 1 + 2 * Real.exp (-(s.lam * s.cAndNotB))) := by
  rw [liMessageSpeaker_real_singleton, liSpeaker, RSA.speaker_dirac_eq_ofWeights,
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wa),
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wa), Fintype.sum_prod_type,
    sum_message]
  simp (disch := decide) only [sum_interpretation, liL0_apply, Interpretation.meaning, Setting.L0,
    weight_toReal s.prior s.prior_ne_zero, weight_eq_zero s.prior, ENNReal.toReal_zero]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero, ← measureReal_def,
    Setting.prior_real_wa, ENNReal.toReal_one, Real.log_one, Setting.cost, sub_zero, zero_sub,
    mul_neg, mul_zero, Real.exp_zero, add_zero]
  ring

theorem liSpeaker_ne_zero {w : World} {u : Message} (hw : literal.sat u w = true) :
    liSpeaker s w {(u, .lit)} ≠ 0 :=
  RSA.speaker_dirac_apply_singleton_ne_zero s.lam_pos.le (by
    rw [liL0_apply]
    exact L0_ne_zero s.prior s.prior_ne_zero literal hw)

theorem comp_liMessageSpeaker_ne_zero (u : Message) :
    (liMessageSpeaker s ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  Measure.comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w) (by
    rw [liMessageSpeaker_apply_singleton]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (liSpeaker_ne_zero s hw)) le_self_add))

/-- The pragmatic listener of the lexical-intentions model (item 6 of the §4.4 model). -/
noncomputable def liListener : Kernel Message World :=
  RSA.listener s.prior (liMessageSpeaker s)

theorem liListener_lt_prior (hc : s.cAndB ≤ s.cAndNotB) :
    (liListener s .a).real {.wab} < s.prior.real {.wab} := by
  rw [liListener, RSA.listener_apply_eq_posterior _ _ (comp_liMessageSpeaker_ne_zero s _),
    posterior_real_singleton_lt_iff_of_pair _ _ (by decide) s.prior_support
      (comp_liMessageSpeaker_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    liMessageSpeaker_real_wab_a, liMessageSpeaker_real_wa_a,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have h₁ : Real.exp (s.lam * Real.log s.p) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg s.lam_pos (Real.log_neg s.p_pos s.p_lt_one))
  have h₂ : Real.exp (-(s.lam * s.cAndNotB)) ≤ Real.exp (-(s.lam * s.cAndB)) :=
    Real.exp_le_exp.mpr (by nlinarith [s.lam_pos])
  have h₃ := Real.exp_pos (-(s.lam * s.cAndNotB))
  have h₄ := Real.exp_pos (s.lam * Real.log (1 - s.p))
  nlinarith [mul_lt_mul_of_pos_right h₁ h₃, mul_pos h₄ (Real.exp_pos (-(s.lam * s.cAndB)))]

end LexicalIntentions

/-! ### The supervaluationist model (§4.2) -/

section Supervaluationist

variable (s : Setting)

/-- The coarse question puts both worlds in one cell, and the fine one distinguishes them. -/
def QUD.cell : QUD → World → Set World
  | .coarse, _ => Set.univ
  | .fine, w => {w}

/-- The literal listener's mass, under an interpretation, on the cell of a world in a question
(item 3 of the §4.2 model, conditioned on the question). -/
noncomputable def cell (i : Interpretation) (q : QUD) (u : Message) (w : World) : ℝ≥0∞ :=
  s.L0 i.meaning u (q.cell w)

theorem cell_coarse (i : Interpretation) (u : Message) (w : World) :
    cell s i .coarse u w = 1 :=
  L0_apply_univ s.prior s.prior_ne_zero _ u

theorem cell_fine (i : Interpretation) (u : Message) (w : World) :
    cell s i .fine u w = s.L0 i.meaning u {w} := rfl

/-- The supervaluationist weight is the geometric mean over the two interpretations, taken
equiprobable, of the literal listener's mass on the cell, raised to the rationality, times the
cost factor. The prior of the question, common to every message, is left out (item 4 of the
§4.2 model). -/
noncomputable def svWeight (x : World × QUD) (u : Message) : ℝ≥0∞ :=
  cell s .lit x.2 u x.1 ^ (s.lam / 2) * cell s .exh x.2 u x.1 ^ (s.lam / 2) * s.costFactor u

theorem svWeight_ne_top (x : World × QUD) (u : Message) : svWeight s x u ≠ ∞ :=
  ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (half_pos s.lam_pos).le
        (measure_ne_top _ _))
      (ENNReal.rpow_ne_top_of_nonneg (half_pos s.lam_pos).le (measure_ne_top _ _)))
    (s.costFactor_ne_top u)

theorem svWeight_fine_ne_zero {w : World} {u : Message} (hl : truth u w = true)
    (he : exh u w = true) : svWeight s (w, .fine) u ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero
      ((ENNReal.rpow_eq_zero_iff_of_pos (half_pos s.lam_pos)).not.2
        (L0_ne_zero s.prior s.prior_ne_zero literal hl))
      ((ENNReal.rpow_eq_zero_iff_of_pos (half_pos s.lam_pos)).not.2
        (L0_ne_zero s.prior s.prior_ne_zero exhaustified he)))
    (s.costFactor_ne_zero u)

/-- The supervaluationist speaker, at a world and a question (item 5 of the §4.2 model). -/
noncomputable def svSpeaker : Kernel (World × QUD) Message := Kernel.ofWeights (svWeight s)

instance : IsFiniteKernel (svSpeaker s) := inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

theorem svSpeaker_coarse : svSpeaker s (.wa, .coarse) = svSpeaker s (.wab, .coarse) := by
  have h : svWeight s (.wa, .coarse) = svWeight s (.wab, .coarse) :=
    funext fun u ↦ by simp only [svWeight, cell_coarse]
  simp only [svSpeaker, Kernel.ofWeights, Kernel.ofFunOfCountable_apply, h]

theorem svSpeaker_wab_fine_a : svSpeaker s (.wab, .fine) {.a} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by
    simp (disch := decide) only [svWeight, cell_fine, Setting.L0, Interpretation.meaning,
      L0_eq_zero, ENNReal.zero_rpow_of_pos (half_pos s.lam_pos), mul_zero, zero_mul])

theorem svSpeaker_real_wab_fine_a : (svSpeaker s (.wab, .fine)).real {.a} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (svSpeaker_wab_fine_a s)

theorem svSpeaker_fine_ne_zero {w : World} {u : Message} (hl : truth u w = true)
    (he : exh u w = true) : svSpeaker s (w, .fine) {u} ≠ 0 :=
  Kernel.ofWeights_apply_singleton_ne_zero (svWeight_fine_ne_zero s hl he) (svWeight_ne_top s _)

/-- Under either question, *A* is used no more in the world of both than in the world of A
alone (Appendix A.3, the speaker). -/
theorem svSpeaker_wab_le_wa (q : QUD) : svSpeaker s (.wab, q) {.a} ≤ svSpeaker s (.wa, q) {.a} := by
  cases q
  · rw [svSpeaker_coarse]
  · rw [svSpeaker_wab_fine_a]; exact zero_le

variable (Q : Measure QUD) (hQ : Q {.fine} ≠ 0)

/-- The joint prior over worlds and questions, independent. -/
noncomputable def svJoint : Measure (World × QUD) := s.prior.prod Q

theorem svJoint_apply_singleton (w : World) (q : QUD) :
    svJoint s Q {(w, q)} = s.prior {w} * Q {q} := by
  show (s.prior.prod Q) {(w, q)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

theorem svJoint_real_singleton (w : World) (q : QUD) :
    (svJoint s Q).real {(w, q)} = s.prior.real {w} * Q.real {q} :=
  Measure.prod_real_singleton _ _ _ _

theorem exists_truth_and_exh (u : Message) : ∃ w, truth u w = true ∧ exh u w = true := by
  cases u
  · exact ⟨.wa, rfl, by decide⟩
  · exact ⟨.wab, rfl, by decide⟩
  · exact ⟨.wa, rfl, by decide⟩

include hQ in
theorem comp_svSpeaker_ne_zero (u : Message) : (svSpeaker s ∘ₘ svJoint s Q) {u} ≠ 0 :=
  let ⟨w, hw⟩ := exists_truth_and_exh u
  have hj : svJoint s Q {(w, .fine)} ≠ 0 := by
    rw [svJoint_apply_singleton]; exact mul_ne_zero (s.prior_ne_zero w) hQ
  Measure.comp_apply_singleton_ne_zero _ _ hj (svSpeaker_fine_ne_zero s hw.1 hw.2)

variable [IsProbabilityMeasure Q]

instance : IsProbabilityMeasure (svJoint s Q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))

/-- The pragmatic listener, jointly over worlds and questions (item 6 of the §4.2 model). -/
noncomputable def svListener : Kernel Message (World × QUD) :=
  RSA.listener (svJoint s Q) (svSpeaker s)

include hQ in
/-- The posterior of both A and B falls below its prior, for every prior in the open interval,
every prior on the questions that gives the fine one positive probability, and every cost,
since the fine question contributes a use of *A* in the world of A alone and none in the
world of both (Appendix A.3, the listener). -/
theorem svListener_fst_lt_prior : (svListener s Q .a).fst.real {.wab} < s.prior.real {.wab} := by
  have hm : 0 < ∑ p, (svJoint s Q).real {p} * (svSpeaker s p).real {.a} := by
    rw [← Measure.comp_real_singleton]
    exact ENNReal.toReal_pos (comp_svSpeaker_ne_zero s Q hQ _) (measure_ne_top _ _)
  have hy : 0 < (svSpeaker s (.wa, .fine)).real {.a} :=
    ENNReal.toReal_pos (svSpeaker_fine_ne_zero s rfl (by decide)) (measure_ne_top _ _)
  have hqf : 0 < Q.real {.fine} := ENNReal.toReal_pos hQ (measure_ne_top _ _)
  have hz := measureReal_nonneg (μ := svSpeaker s (.wa, .coarse)) (s := {.a})
  have hqc := measureReal_nonneg (μ := Q) (s := {.coarse})
  have hp' : 0 < 1 - s.p := by linarith [s.p_lt_one]
  rw [svListener, RSA.listener_fst_real_singleton, div_lt_iff₀ hm]
  simp only [Fintype.sum_prod_type, sum_world, sum_qud, svJoint_real_singleton,
    Setting.prior_real_wa, Setting.prior_real_wab, svSpeaker_real_wab_fine_a, ← svSpeaker_coarse,
    mul_zero, add_zero]
  nlinarith [mul_pos (mul_pos (mul_pos s.p_pos hp') hqf) hy]

end Supervaluationist

/-! ### The wonky-world models (§4.1) -/

section Wonky

variable (s : Setting) (ω : ℝ) (hω₀ : 0 ≤ ω) (hω₁ : ω ≤ 1)

/-- The speaker's prior is uniform in the wonky background and the measured one otherwise. -/
noncomputable def worldPrior : Background → Measure World
  | .wonky => wonkyPrior
  | .measured => s.prior

instance (b : Background) : IsProbabilityMeasure (worldPrior s b) := by
  cases b <;> dsimp only [worldPrior] <;> infer_instance

theorem worldPrior_ne_zero (b : Background) (w : World) : worldPrior s b {w} ≠ 0 := by
  cases b
  · exact wonkyPrior_ne_zero w
  · exact s.prior_ne_zero w

/-- The speaker under a background, with the background's prior in the literal listener
(items 1 to 3 of the §4.1 model). -/
noncomputable def bgSpeaker (b : Background) : Kernel World Message :=
  speaker (worldPrior s b) literal s

instance (b : Background) : IsFiniteKernel (bgSpeaker s b) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _))

theorem bgSpeaker_wonky_wab_a :
    (bgSpeaker s .wonky .wab).real {.a} = s.logistic (s.cAndB - Real.log 2) := by
  rw [bgSpeaker, speaker_literal_wab_a _ (worldPrior_ne_zero s .wonky), worldPrior,
    wonkyPrior_real_singleton, Real.log_inv, ← sub_eq_add_neg]

theorem bgSpeaker_wonky_wa_a :
    (bgSpeaker s .wonky .wa).real {.a} = s.logistic (s.cAndNotB - Real.log 2) := by
  rw [bgSpeaker, speaker_literal_wa_a _ (worldPrior_ne_zero s .wonky), worldPrior,
    wonkyPrior_real_singleton, Real.log_inv, ← sub_eq_add_neg]

theorem bgSpeaker_measured_wab_a :
    (bgSpeaker s .measured .wab).real {.a} = s.logistic (s.cAndB + Real.log s.p) := by
  rw [bgSpeaker, speaker_literal_wab_a _ (worldPrior_ne_zero s .measured), worldPrior,
    Setting.prior_real_wab]

theorem bgSpeaker_measured_wa_a :
    (bgSpeaker s .measured .wa).real {.a} = s.logistic (s.cAndNotB + Real.log (1 - s.p)) := by
  rw [bgSpeaker, speaker_literal_wa_a _ (worldPrior_ne_zero s .measured), worldPrior,
    Setting.prior_real_wa]

/-- The wonky background has weight the wonkiness `ω`, and the measured one `1 - ω`. -/
noncomputable def bgWeight : Background → ℝ≥0∞
  | .wonky => ENNReal.ofReal ω
  | .measured => ENNReal.ofReal (1 - ω)

theorem bgWeight_ne_top (b : Background) : bgWeight ω b ≠ ∞ := by
  cases b <;> exact ENNReal.ofReal_ne_top

theorem bgWeight_exists_ne_zero : ∃ b, bgWeight ω b ≠ 0 :=
  (le_or_gt ω 0).elim (fun h ↦ ⟨.measured, by simp [bgWeight]; linarith⟩)
    (fun h ↦ ⟨.wonky, by simp [bgWeight, h]⟩)

/-- The prior on backgrounds puts `ω` on the wonky background and `1 - ω` on the measured
one. -/
noncomputable def bgPrior : Measure Background := ∑ b, bgWeight ω b • Measure.dirac b

theorem bgPrior_apply_singleton (b : Background) : bgPrior ω {b} = bgWeight ω b :=
  Measure.sum_smul_dirac_apply_singleton _ b

instance : IsFiniteMeasure (bgPrior ω) :=
  ⟨by
    rw [bgPrior, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun b _ ↦ by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact (bgWeight_ne_top ω b).lt_top⟩

/-- The speaker marginalised over the listener's uncertainty about the speaker's prior (item 5
of the §4.1 model, the Bayesian version). -/
noncomputable def bayesWonkySpeaker : Kernel World Message :=
  ∑ b, bgWeight ω b • bgSpeaker s b

instance : IsFiniteKernel (bayesWonkySpeaker s ω) :=
  IsFiniteKernel.finsetSum _ fun b _ ↦ IsFiniteKernel.smul_of_ne_top _ (bgWeight_ne_top ω b)

include hω₀ hω₁ in
theorem bayesWonkySpeaker_real_singleton (w : World) (u : Message) :
    (bayesWonkySpeaker s ω w).real {u} =
      ω * (bgSpeaker s .wonky w).real {u} + (1 - ω) * (bgSpeaker s .measured w).real {u} := by
  simp only [bayesWonkySpeaker, measureReal_def, sum_apply, smul_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [sum_background,
    ENNReal.toReal_add (ENNReal.mul_ne_top (bgWeight_ne_top ω _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (bgWeight_ne_top ω _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [bgWeight, ENNReal.toReal_ofReal hω₀, ENNReal.toReal_ofReal (sub_nonneg.mpr hω₁)]

theorem bayesWonkySpeaker_zero (w : World) : bayesWonkySpeaker s 0 w = s.speaker literal w := by
  simp [bayesWonkySpeaker, sum_background, bgWeight, bgSpeaker, worldPrior]

theorem comp_bayesWonkySpeaker_ne_zero (u : Message) :
    (bayesWonkySpeaker s ω ∘ₘ s.prior) {u} ≠ 0 := by
  obtain ⟨w, hw⟩ := literal.exists_world u
  obtain ⟨b, hb⟩ := bgWeight_exists_ne_zero ω
  refine Measure.comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w) ?_
  simp only [bayesWonkySpeaker, sum_apply, smul_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ,
    true_implies, mul_eq_zero, not_forall, not_or]
  exact ⟨b, hb, speaker_ne_zero _ (worldPrior_ne_zero s b) _ s hw⟩

/-- The Bayesian wonky listener, with the measured prior (item 5 of the Bayesian §4.1
model). -/
noncomputable def bayesWonkyListener : Kernel Message World :=
  RSA.listener s.prior (bayesWonkySpeaker s ω)

/-- The joint posterior over worlds and the speaker's background, with the measured prior on
worlds independent of the prior on backgrounds (item 4 of the Bayesian §4.1 model). -/
noncomputable def bayesWonkyJointListener : Kernel Message (World × Background) :=
  RSA.listener (s.prior.prod (bgPrior ω)) fun p ↦ bgSpeaker s p.2 p.1

theorem bayesWonkyJointListener_fst :
    (bayesWonkyJointListener s ω).fst = bayesWonkyListener s ω := by
  rw [bayesWonkyJointListener, RSA.listener_prod_fst, bayesWonkyListener]
  congr 1
  ext w : 1
  simp [bayesWonkySpeaker, bgPrior_apply_singleton]

include hω₀ hω₁ in
/-- Anti-exhaustivity exactly when the wonkiness-weighted excess of the use of *A* in the
world of both over its use in the world of A alone is positive (Appendix A.2, the Bayesian
model). -/
theorem prior_lt_bayesWonkyListener_iff :
    s.prior.real {.wab} < (bayesWonkyListener s ω .a).real {.wab} ↔
      0 < (1 - ω) * (s.logistic (s.cAndB + Real.log s.p) -
          s.logistic (s.cAndNotB + Real.log (1 - s.p))) +
        ω * (s.logistic (s.cAndB - Real.log 2) - s.logistic (s.cAndNotB - Real.log 2)) := by
  rw [bayesWonkyListener,
    RSA.listener_apply_eq_posterior _ _ (comp_bayesWonkySpeaker_ne_zero s ω _),
    real_lt_posterior_real_singleton_iff_of_pair _ _ (by decide)
      s.prior_support (comp_bayesWonkySpeaker_ne_zero s ω _) (s.prior_ne_zero _)
      (s.prior_ne_zero _),
    bayesWonkySpeaker_real_singleton s ω hω₀ hω₁, bayesWonkySpeaker_real_singleton s ω hω₀ hω₁,
    bgSpeaker_wonky_wab_a, bgSpeaker_wonky_wa_a, bgSpeaker_measured_wab_a,
    bgSpeaker_measured_wa_a]
  constructor <;> intro h <;> nlinarith

/-- The world given the background. -/
noncomputable def worldKernel : Kernel Background World := Kernel.ofFunOfCountable (worldPrior s)

instance : IsMarkovKernel (worldKernel s) :=
  ⟨fun b ↦ by rw [worldKernel, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- The prior of the non-Bayesian model draws the background, then the world under it (item 4
of the §4.1 model). -/
noncomputable def wonkyJoint : Measure (Background × World) := bgPrior ω ⊗ₘ worldKernel s

instance : IsFiniteMeasure (wonkyJoint s ω) :=
  inferInstanceAs (IsFiniteMeasure (bgPrior ω ⊗ₘ worldKernel s))

theorem wonkyJoint_apply_singleton (b : Background) (w : World) :
    wonkyJoint s ω {(b, w)} = bgWeight ω b * worldPrior s b {w} := by
  rw [wonkyJoint, Measure.compProd_apply_singleton, bgPrior_apply_singleton, worldKernel,
    Kernel.ofFunOfCountable_apply]

theorem wonkyJoint_real_singleton (b : Background) (w : World) :
    (wonkyJoint s ω).real {(b, w)} = (bgWeight ω b).toReal * (worldPrior s b).real {w} := by
  rw [measureReal_def, wonkyJoint_apply_singleton, ENNReal.toReal_mul, measureReal_def]

/-- The speaker of the non-Bayesian model, at a background and a world. -/
noncomputable def wonkySpeaker : Kernel (Background × World) Message :=
  Kernel.ofFunOfCountable fun x ↦ bgSpeaker s x.1 x.2

theorem wonkySpeaker_apply (x : Background × World) : wonkySpeaker s x = bgSpeaker s x.1 x.2 :=
  rfl

instance : IsFiniteKernel (wonkySpeaker s) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x ↦ by
    rw [wonkySpeaker_apply, bgSpeaker, speaker, RSA.speaker]
    exact Kernel.ofWeights_apply_univ_le_one _ _⟩⟩

theorem wonkySpeaker_ne_zero {w : World} {u : Message} (b : Background)
    (hw : literal.sat u w = true) : wonkySpeaker s (b, w) {u} ≠ 0 := by
  rw [wonkySpeaker_apply]
  exact speaker_ne_zero _ (worldPrior_ne_zero s _) _ s hw

theorem comp_wonkySpeaker_ne_zero (u : Message) : (wonkySpeaker s ∘ₘ wonkyJoint s ω) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  let ⟨b, hb⟩ := bgWeight_exists_ne_zero ω
  have hj : wonkyJoint s ω {(b, w)} ≠ 0 := by
    rw [wonkyJoint_apply_singleton]; exact mul_ne_zero hb (worldPrior_ne_zero s b w)
  Measure.comp_apply_singleton_ne_zero _ _ hj (wonkySpeaker_ne_zero s b hw)

/-- The non-Bayesian listener, uncertain about the background and the world jointly (item 4
of the §4.1 model). -/
noncomputable def wonkyListener : Kernel Message (Background × World) :=
  RSA.listener (wonkyJoint s ω) (wonkySpeaker s)

include hω₀ hω₁ in
theorem prior_lt_wonkyListener_iff :
    s.prior.real {.wab} < (wonkyListener s ω .a).snd.real {.wab} ↔
      s.p * (ω * 2⁻¹ * (s.logistic (s.cAndNotB - Real.log 2) + s.logistic (s.cAndB - Real.log 2)) +
        (1 - ω) * ((1 - s.p) * s.logistic (s.cAndNotB + Real.log (1 - s.p)) +
          s.p * s.logistic (s.cAndB + Real.log s.p))) <
      ω * 2⁻¹ * s.logistic (s.cAndB - Real.log 2) +
        (1 - ω) * (s.p * s.logistic (s.cAndB + Real.log s.p)) := by
  have hm : 0 < ∑ p, (wonkyJoint s ω).real {p} * (wonkySpeaker s p).real {.a} := by
    rw [← Measure.comp_real_singleton]
    exact ENNReal.toReal_pos (comp_wonkySpeaker_ne_zero s ω _) (measure_ne_top _ _)
  rw [wonkyListener, RSA.listener_snd_real_singleton, lt_div_iff₀ hm]
  simp only [Fintype.sum_prod_type, sum_background, sum_world, wonkyJoint_real_singleton,
    wonkySpeaker_apply, bgSpeaker_wonky_wab_a, bgSpeaker_wonky_wa_a, bgSpeaker_measured_wab_a,
    bgSpeaker_measured_wa_a, bgWeight, ENNReal.toReal_ofReal hω₀,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hω₁), worldPrior, wonkyPrior_real_singleton,
    Setting.prior_real_wa, Setting.prior_real_wab]
  constructor <;> intro h <;> linarith

end Wonky

end CremersWilcoxSpector2023
