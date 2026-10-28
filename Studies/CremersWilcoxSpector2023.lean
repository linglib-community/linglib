module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.Probability.Kernel.Module
public import Linglib.Core.Probability.UniformOn
public import Linglib.Pragmatics.RSA.LexicalUncertainty
public import Linglib.Pragmatics.RSA.QUD
public import Linglib.Semantics.Exhaustification.Finite

/-!
# Exhaustivity and anti-exhaustivity in the Rational Speech Act framework

This file formalizes the Rational Speech Act models that Cremers, Wilcox and Spector compare on
the symmetry problem: after *A*, where *A and B* was available, does the listener's belief in the
world of both rise above its prior? Each model's section ends in its verdict, stated with
`Setting.AntiExhaustive` and `Setting.Exhaustive` (6b).

## Implementation notes

* The supervaluationist speaker takes any prior on exhaustification; the paper fixes
  `P(i_exh) = 1/2` only in its fit (Appendix B.3).
* The wonky models share one speaker on worlds and backgrounds, and their posteriors are (A.5a)
  and (A.5b). Lexical uncertainty and intentions take the interpretations equiprobable.

## Errata

* Appendix A.2 writes `P(w_ab|b1)` for the measured prior, which is `P(w_ab|b2)`.
* Appendix B.2's `L1(w_ab|A)` exchanges `w_a` and `w_ab`; corrected, it is (A.5).
* Item 7 of the §4.2 model takes the log of a sum of logs, and item 7 of §4.3 has `L_n ∝ log S_n`.

## TODO

* The verdict on Degen and colleagues' model and the Bayesian wonkiness threshold (A.2).
* The second-level speakers, the production models of Appendix B, and the data of §5.

## References

* [cremers-wilcox-spector-2023]
* [frank-goodman-2012]
* [degen-etal-2015]
* [spector-2017]
* [bergen-levy-goodman-2016]
* [franke-bergen-2020]
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
instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩

/-- The three messages are *A*, *A and B* and *A and not B*. -/
inductive Message where
  | a
  | aAndB
  | aAndNotB
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Message := ⊤
instance : DiscreteMeasurableSpace Message := ⟨fun _ ↦ trivial⟩

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

theorem exh_aAndB : exh .aAndB = truth .aAndB := by decide

theorem exh_aAndNotB : exh .aAndNotB = truth .aAndNotB := by decide

/-- An interpretation function under which every message is true somewhere and every world is
described by some message. -/
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

/-- The anti-exhaustive interpretation, *A* read as *A and B*. -/
def antiExhaustive : Meaning :=
  ⟨fun u w ↦ match u with | .a => truth .aAndB w | u => truth u w, by decide, by decide⟩

/-- The two grammatical interpretations, literal and exhaustified. -/
inductive Interpretation where
  | lit
  | exh
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Interpretation := ⊤
instance : DiscreteMeasurableSpace Interpretation := ⟨fun _ ↦ trivial⟩

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

/-- The backgrounds of the wonky-world models, in which the speaker assumes a uniform prior or the
measured one. -/
inductive Background where
  | wonky
  | measured
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Background := ⊤

/-- The questions under discussion: whether A holds, and which world obtains. -/
inductive QUD where
  | coarse
  | fine
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨fun _ ↦ trivial⟩

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

/-- The parameters of a model: the prior of the world of both, the rationality, and the costs of
the two conjunctions, *A* costing nothing. -/
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

/-- The exponential of a message's cost, scaled by the rationality. -/
noncomputable abbrev costFactor (u : Message) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(s.lam * s.cost u)))

theorem costFactor_ne_zero (u : Message) : s.costFactor u ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem costFactor_ne_top (u : Message) : s.costFactor u ≠ ∞ := ENNReal.ofReal_ne_top

theorem costFactor_toReal (u : Message) :
    (s.costFactor u).toReal = Real.exp (-(s.lam * s.cost u)) :=
  ENNReal.toReal_ofReal (Real.exp_pos _).le

/-- The logistic function with rate the rationality, the paper's `f_λ`. -/
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

/-- A posterior over the worlds is anti-exhaustive when it puts more on the world of both than the
prior does (6b). -/
def AntiExhaustive (μ : Measure World) : Prop := s.prior.real {.wab} < μ.real {.wab}

/-- A posterior over the worlds is exhaustive when it puts less on the world of both than the prior
does. -/
def Exhaustive (μ : Measure World) : Prop := μ.real {.wab} < s.prior.real {.wab}

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

/-- The speaker under an interpretation (eqs. 2 and 3). -/
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

theorem baseline_aAndB_lt_a_iff :
    (s.speaker literal .wab).real {.aAndB} < (s.speaker literal .wab).real {.a} ↔
      -s.cAndB < Real.log s.p := by
  rw [Setting.speaker, speaker_real_singleton_lt_iff s.prior s.prior_ne_zero literal s rfl rfl]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero literal,
    ENNReal.toReal_one, Real.log_one, Setting.cost, ← measureReal_def, Setting.prior_real_wab,
    zero_sub, sub_zero]

theorem baseline_a_lt_aAndNotB_iff :
    (s.speaker literal .wa).real {.a} < (s.speaker literal .wa).real {.aAndNotB} ↔
      Real.log (1 - s.p) < -s.cAndNotB := by
  rw [Setting.speaker, speaker_real_singleton_lt_iff s.prior s.prior_ne_zero literal s rfl rfl]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero literal,
    ENNReal.toReal_one, Real.log_one, Setting.cost, ← measureReal_def, Setting.prior_real_wa,
    zero_sub, sub_zero]

theorem comp_speaker_literal_ne_zero (u : Message) : (s.speaker literal ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  Measure.comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w)
    (speaker_ne_zero _ s.prior_ne_zero _ s hw)

/-- The pragmatic listener (eq. 4). -/
noncomputable def listener : Kernel Message World :=
  RSA.listener s.prior (s.speaker literal)

theorem antiExhaustive_listener_iff_speaker_lt :
    s.AntiExhaustive (listener s .a) ↔
      (s.speaker literal .wa).real {.a} < (s.speaker literal .wab).real {.a} := by
  rw [Setting.AntiExhaustive, listener,
    RSA.listener_apply_eq_posterior _ _ (comp_speaker_literal_ne_zero s _)]
  exact real_lt_posterior_real_singleton_iff_of_pair (s.speaker literal) s.prior (by decide)
    s.prior_support (comp_speaker_literal_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _)

/-- The baseline listener is anti-exhaustive iff the prior log odds exceed the cost disadvantage of
*A and not B* over *A and B*. -/
theorem antiExhaustive_listener_iff :
    s.AntiExhaustive (listener s .a) ↔
      s.cAndNotB - s.cAndB < Real.log s.p - Real.log (1 - s.p) := by
  rw [antiExhaustive_listener_iff_speaker_lt, Setting.speaker,
    speaker_literal_wa_a _ s.prior_ne_zero,
    speaker_literal_wab_a _ s.prior_ne_zero, Setting.prior_real_wa, Setting.prior_real_wab,
    s.logistic_lt_iff, sub_lt_sub_iff, add_comm (Real.log s.p)]

theorem antiExhaustive_listener_iff_of_cost_eq (hc : s.cAndB = s.cAndNotB) :
    s.AntiExhaustive (listener s .a) ↔ 1 / 2 < s.p := by
  rw [antiExhaustive_listener_iff, hc, sub_self, sub_pos,
    Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

end Baseline

/-! ### The wonky-world models (§4.1)

The listener is unsure whether the speaker assumes the measured prior or the uniform prior of a
wonky background. The two models share the speaker and differ in the listener's prior: a
background and then a world in Degen and colleagues' model, the measured prior on worlds in the
Bayesian one. -/

section Wonky

variable (s : Setting) (β : Measure Background)

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

/-- The speaker who assumes a background's prior (items 1 to 3 of the §4.1 model). -/
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

/-- The speaker at a world and a background. -/
noncomputable def wonkySpeaker : Kernel (World × Background) Message :=
  Kernel.ofFunOfCountable fun x ↦ bgSpeaker s x.2 x.1

theorem wonkySpeaker_apply (x : World × Background) : wonkySpeaker s x = bgSpeaker s x.2 x.1 :=
  rfl

instance : IsFiniteKernel (wonkySpeaker s) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x ↦ by
    rw [wonkySpeaker_apply, bgSpeaker, speaker, RSA.speaker]
    exact Kernel.ofWeights_apply_univ_le_one _ _⟩⟩

/-- The world given the background. -/
noncomputable def worldKernel : Kernel Background World := Kernel.ofFunOfCountable (worldPrior s)

instance : IsMarkovKernel (worldKernel s) :=
  ⟨fun b ↦ by rw [worldKernel, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- The prior of Degen and colleagues' listener: a background, then a world under it (item 4). -/
noncomputable def wonkyJoint : Measure (World × Background) :=
  (β ⊗ₘ worldKernel s).map Prod.swap

/-- The listener of Degen and colleagues' model (item 4). -/
noncomputable def wonkyListener : Kernel Message (World × Background) :=
  RSA.listener (wonkyJoint s β) (wonkySpeaker s)

/-- The Bayesian listener, whose prior on the worlds is the measured one (item 4). -/
noncomputable def bayesWonkyJointListener : Kernel Message (World × Background) :=
  RSA.listener (s.prior.prod β) (wonkySpeaker s)

/-- The speaker averaged over the backgrounds (item 5). -/
noncomputable def bayesWonkySpeaker : Kernel World Message := ∑ b, β {b} • bgSpeaker s b

/-- The Bayesian listener as the inverse of the averaged speaker (item 5). -/
noncomputable def bayesWonkyListener : Kernel Message World :=
  RSA.listener s.prior (bayesWonkySpeaker s β)

theorem bayesWonkySpeaker_dirac_measured :
    bayesWonkySpeaker s (Measure.dirac .measured) = s.speaker literal := by
  ext1 w
  simp [bayesWonkySpeaker, sum_background, bgSpeaker, worldPrior]

theorem bayesWonkyJointListener_fst :
    (bayesWonkyJointListener s β).fst = bayesWonkyListener s β := by
  rw [bayesWonkyJointListener, RSA.listener_prod_fst, bayesWonkyListener]
  congr 1

variable [IsFiniteMeasure β]

instance : IsFiniteMeasure (wonkyJoint s β) := by
  unfold wonkyJoint; infer_instance

instance : IsFiniteKernel (bayesWonkySpeaker s β) :=
  IsFiniteKernel.finsetSum _ fun _ _ ↦ IsFiniteKernel.smul_of_ne_top _ (measure_ne_top _ _)

omit [IsFiniteMeasure β] in
theorem wonkyJoint_real_singleton (w : World) (b : Background) :
    (wonkyJoint s β).real {(w, b)} = β.real {b} * (worldPrior s b).real {w} := by
  rw [measureReal_def, wonkyJoint, Measure.map_apply measurable_swap (measurableSet_singleton _),
    show Prod.swap ⁻¹' {(w, b)} = {(b, w)} by ext; exact Prod.swap_eq_iff_eq_swap,
    Measure.compProd_apply_singleton,
    worldKernel, Kernel.ofFunOfCountable_apply, ENNReal.toReal_mul, ← measureReal_def,
    ← measureReal_def]

theorem bayesWonkySpeaker_real_singleton (w : World) (u : Message) :
    (bayesWonkySpeaker s β w).real {u} =
      β.real {.wonky} * (bgSpeaker s .wonky w).real {u} +
        β.real {.measured} * (bgSpeaker s .measured w).real {u} := by
  simp only [bayesWonkySpeaker, measureReal_def, sum_apply, smul_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [sum_background,
    ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]

theorem wonkyListener_fst_real_wab :
    (wonkyListener s β .a).fst.real {.wab} =
      (β.real {.measured} * s.p * s.logistic (s.cAndB + Real.log s.p) +
          β.real {.wonky} * 2⁻¹ * s.logistic (s.cAndB - Real.log 2)) /
        (β.real {.measured} * s.p * s.logistic (s.cAndB + Real.log s.p) +
          β.real {.wonky} * 2⁻¹ * s.logistic (s.cAndB - Real.log 2) +
          β.real {.measured} * (1 - s.p) * s.logistic (s.cAndNotB + Real.log (1 - s.p)) +
          β.real {.wonky} * 2⁻¹ * s.logistic (s.cAndNotB - Real.log 2)) := by
  rw [wonkyListener, RSA.listener_fst_real_singleton]
  simp only [Fintype.sum_prod_type, sum_world, sum_background, wonkyJoint_real_singleton,
    wonkySpeaker_apply, bgSpeaker_wonky_wab_a, bgSpeaker_wonky_wa_a, bgSpeaker_measured_wab_a,
    bgSpeaker_measured_wa_a, worldPrior, wonkyPrior_real_singleton, Setting.prior_real_wa,
    Setting.prior_real_wab]
  ring

theorem bayesWonkyListener_real_wab :
    (bayesWonkyListener s β .a).real {.wab} =
      s.p * (β.real {.measured} * s.logistic (s.cAndB + Real.log s.p) +
          β.real {.wonky} * s.logistic (s.cAndB - Real.log 2)) /
        (s.p * (β.real {.measured} * s.logistic (s.cAndB + Real.log s.p) +
            β.real {.wonky} * s.logistic (s.cAndB - Real.log 2)) +
          (1 - s.p) * (β.real {.measured} * s.logistic (s.cAndNotB + Real.log (1 - s.p)) +
            β.real {.wonky} * s.logistic (s.cAndNotB - Real.log 2))) := by
  rw [bayesWonkyListener, RSA.listener_real_singleton]
  simp only [sum_world, bayesWonkySpeaker_real_singleton, bgSpeaker_wonky_wab_a,
    bgSpeaker_wonky_wa_a, bgSpeaker_measured_wab_a, bgSpeaker_measured_wa_a,
    Setting.prior_real_wa, Setting.prior_real_wab]
  ring

/-- The Bayesian wonky listener is anti-exhaustive iff *A* is used more in the world of both than
in the world of A alone, averaged over the backgrounds. -/
theorem antiExhaustive_bayesWonkyListener_iff [IsProbabilityMeasure β] :
    s.AntiExhaustive (bayesWonkyListener s β .a) ↔
      0 < β.real {.measured} * (s.logistic (s.cAndB + Real.log s.p) -
          s.logistic (s.cAndNotB + Real.log (1 - s.p))) +
        β.real {.wonky} * (s.logistic (s.cAndB - Real.log 2) -
          s.logistic (s.cAndNotB - Real.log 2)) := by
  have hβ : β.real {.wonky} + β.real {.measured} = 1 := by
    rw [← sum_background (fun b ↦ β.real {b}), sum_measureReal_singleton, Finset.coe_univ,
      probReal_univ]
  have hf (x : ℝ) : 0 < s.logistic x := Real.sigmoid_pos _
  have hw := measureReal_nonneg (μ := β) (s := {.wonky})
  have hm := measureReal_nonneg (μ := β) (s := {.measured})
  have hp' : 0 < 1 - s.p := by linarith [s.p_lt_one]
  have hX : 0 < β.real {.measured} * s.logistic (s.cAndB + Real.log s.p) +
      β.real {.wonky} * s.logistic (s.cAndB - Real.log 2) := by
    rcases (show 0 < β.real {.measured} ∨ 0 < β.real {.wonky} by
      by_contra h; push Not at h; linarith) with h | h
    · have := mul_nonneg hw (hf (s.cAndB - Real.log 2)).le
      nlinarith [mul_pos h (hf (s.cAndB + Real.log s.p))]
    · have := mul_nonneg hm (hf (s.cAndB + Real.log s.p)).le
      nlinarith [mul_pos h (hf (s.cAndB - Real.log 2))]
  have hY : 0 ≤ β.real {.measured} * s.logistic (s.cAndNotB + Real.log (1 - s.p)) +
      β.real {.wonky} * s.logistic (s.cAndNotB - Real.log 2) := by
    nlinarith [hf (s.cAndNotB + Real.log (1 - s.p)), hf (s.cAndNotB - Real.log 2)]
  rw [Setting.AntiExhaustive, bayesWonkyListener_real_wab, Setting.prior_real_wab,
    lt_div_iff₀ (by nlinarith [s.p_pos])]
  constructor <;> intro h <;> nlinarith [mul_pos s.p_pos hp']

end Wonky

/-! ### The supervaluationist model (§4.2)

Spector's 2017 first speaker, applied to exhaustification: she addresses a question and maximizes
her expected utility over the interpretations. -/

section Supervaluationist

/-- The coarse question has a single answer, and the fine one answers with the world. -/
def QUD.answer : QUD → World → Option World
  | .coarse, _ => none
  | .fine, w => some w

/-- The answer at a world and a question, together with the question. -/
def answer (x : World × QUD) : Option World × QUD := (x.2.answer x.1, x.2)

variable (s : Setting) (ρ : Measure QUD) (ν : Measure Interpretation)

/-- The prior over worlds and questions (items 3 and 6 of the §4.2 model). -/
noncomputable def svJoint : Measure (World × QUD) := s.prior.prod ρ

instance [IsFiniteMeasure ρ] : IsFiniteMeasure (svJoint s ρ) := by
  unfold svJoint; infer_instance

/-- The literal listener of an interpretation, over worlds and questions (item 3). -/
noncomputable def svL0 (i : Interpretation) : Kernel Message (World × QUD) :=
  RSA.listener (svJoint s ρ) (RSA.truthful fun u ↦ Prod.fst ⁻¹' i.meaning.extension u)

instance (i : Interpretation) : IsFiniteKernel (svL0 s ρ i) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ (RSA.truthful _)))

/-- The supervaluationist speaker, who maximizes her expected utility over the interpretations
under the prior `ν` (items 4 and 5). -/
noncomputable def svSpeaker : Kernel (World × QUD) Message :=
  RSA.speaker s.lam s.cost (RSA.parseListener fun i ↦ (svL0 s ρ i).map answer)
    fun x ↦ ν.prod (Measure.dirac (answer x))

instance : IsFiniteKernel (svSpeaker s ρ ν) :=
  inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

/-- The pragmatic listener over worlds and questions (item 6). -/
noncomputable def svListener : Kernel Message (World × QUD) :=
  RSA.listener (svJoint s ρ) (svSpeaker s ρ ν)

theorem svSpeaker_coarse : svSpeaker s ρ ν (.wa, .coarse) = svSpeaker s ρ ν (.wab, .coarse) :=
  rfl

theorem svJoint_apply_singleton (w : World) (q : QUD) :
    svJoint s ρ {(w, q)} = s.prior {w} * ρ {q} := by
  rw [svJoint, ← Set.singleton_prod_singleton, Measure.prod_prod]

theorem svJoint_real_singleton (w : World) (q : QUD) :
    (svJoint s ρ).real {(w, q)} = s.prior.real {w} * ρ.real {q} :=
  Measure.prod_real_singleton _ _ _ _

theorem exists_truth_and_exh (u : Message) : ∃ w, truth u w = true ∧ exh u w = true := by
  cases u
  · exact ⟨.wa, rfl, by decide⟩
  · exact ⟨.wab, rfl, by decide⟩
  · exact ⟨.wa, rfl, by decide⟩

variable {s ρ ν} [IsFiniteMeasure ρ] (hρ : ∀ q, ρ {q} ≠ 0)
include hρ

theorem svL0_map_answer_eq_zero_iff (i : Interpretation) (u : Message) (w : World) (q : QUD) :
    (svL0 s ρ i).map answer u {answer (w, q)} = 0 ↔
      ∀ v, q.answer v = q.answer w → i.meaning.sat u v = false := by
  rw [svL0, RSA.listener_truthful_map_apply_singleton, ENNReal.div_eq_zero_iff,
    or_iff_left (measure_ne_top _ _), measure_null_iff_singleton (Set.to_countable _)]
  have hprod (p : World × QUD) : svJoint s ρ {p} ≠ 0 := by
    rw [← Prod.mk.eta (p := p), svJoint_apply_singleton]
    exact mul_ne_zero (s.prior_ne_zero p.1) (hρ p.2)
  simp only [hprod, imp_false]
  refine ⟨fun h v hv ↦ Bool.eq_false_iff.2 fun hvu ↦ h (v, q) ⟨hvu, by simp [answer, hv]⟩, ?_⟩
  rintro h ⟨v, q'⟩ ⟨hvu, hx⟩
  simp only [answer, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨hv, rfl⟩ := hx
  exact Bool.false_ne_true ((h v hv).symm.trans hvu)

variable [IsFiniteMeasure ν]

theorem svSpeaker_apply_singleton_eq_zero_iff (w : World) (q : QUD) (u : Message) :
    svSpeaker s ρ ν (w, q) {u} = 0 ↔
      ∃ i, ν {i} ≠ 0 ∧ ∀ v, q.answer v = q.answer w → i.meaning.sat u v = false := by
  rw [svSpeaker, RSA.speaker_parseListener_apply_singleton_eq_zero_iff _ s.lam_pos]
  exact exists_congr fun i ↦ and_congr_right fun _ ↦ svL0_map_answer_eq_zero_iff hρ i u w q

theorem svSpeaker_wab_fine_a (hν : ν {.exh} ≠ 0) : svSpeaker s ρ ν (.wab, .fine) {.a} = 0 :=
  (svSpeaker_apply_singleton_eq_zero_iff hρ _ _ _).2 ⟨.exh, hν, fun v hv ↦ by
    obtain rfl : v = .wab := Option.some.inj hv
    decide⟩

theorem svSpeaker_fine_ne_zero {w : World} {u : Message} (hl : truth u w = true)
    (he : exh u w = true) : svSpeaker s ρ ν (w, .fine) {u} ≠ 0 := by
  rw [ne_eq, svSpeaker_apply_singleton_eq_zero_iff hρ]
  rintro ⟨i, -, h⟩
  cases i
  · exact Bool.false_ne_true ((h w rfl).symm.trans hl)
  · exact Bool.false_ne_true ((h w rfl).symm.trans he)

theorem svSpeaker_wab_le_wa (hν : ν {.exh} ≠ 0) (q : QUD) :
    svSpeaker s ρ ν (.wab, q) {.a} ≤ svSpeaker s ρ ν (.wa, q) {.a} := by
  cases q
  · rw [svSpeaker_coarse]
  · rw [svSpeaker_wab_fine_a hρ hν]; exact zero_le

theorem comp_svSpeaker_ne_zero (u : Message) :
    (svSpeaker s ρ ν ∘ₘ svJoint s ρ) {u} ≠ 0 :=
  let ⟨w, hw⟩ := exists_truth_and_exh u
  Measure.comp_apply_singleton_ne_zero _ _
    (by rw [svJoint_apply_singleton]; exact mul_ne_zero (s.prior_ne_zero w) (hρ .fine))
    (svSpeaker_fine_ne_zero hρ hw.1 hw.2)

/-- The supervaluationist listener is exhaustive. -/
theorem exhaustive_svListener [IsProbabilityMeasure ρ] (hν : ν {.exh} ≠ 0) :
    s.Exhaustive (svListener s ρ ν .a).fst := by
  have hm : 0 < ∑ p, (svJoint s ρ).real {p} * (svSpeaker s ρ ν p).real {.a} := by
    rw [← Measure.comp_real_singleton]
    exact ENNReal.toReal_pos (comp_svSpeaker_ne_zero hρ _) (measure_ne_top _ _)
  have hy : 0 < (svSpeaker s ρ ν (.wa, .fine)).real {.a} :=
    ENNReal.toReal_pos (svSpeaker_fine_ne_zero hρ rfl (by decide)) (measure_ne_top _ _)
  have hqf : 0 < ρ.real {.fine} := ENNReal.toReal_pos (hρ .fine) (measure_ne_top _ _)
  have hz := measureReal_nonneg (μ := svSpeaker s ρ ν (.wa, .coarse)) (s := {.a})
  have hqc := measureReal_nonneg (μ := ρ) (s := {.coarse})
  have hp' : 0 < 1 - s.p := by linarith [s.p_lt_one]
  have h0 : (svSpeaker s ρ ν (.wab, .fine)).real {.a} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (svSpeaker_wab_fine_a hρ hν)
  rw [Setting.Exhaustive, svListener, RSA.listener_fst_real_singleton, div_lt_iff₀ hm]
  simp only [Fintype.sum_prod_type, sum_world, sum_qud, svJoint_real_singleton,
    Setting.prior_real_wa, Setting.prior_real_wab, h0, ← svSpeaker_coarse, mul_zero, add_zero]
  nlinarith [mul_pos (mul_pos (mul_pos s.p_pos hp') hqf) hy]

end Supervaluationist

/-! ### Lexical uncertainty (§4.3)

The listener infers the world and an interpretation from the message. The grammatical version has
the literal and exhaustified interpretations, the free version also the anti-exhaustive one. -/

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

theorem luJointListener_fst : (luJointListener s meaning).fst = luListener s meaning := by
  rw [luJointListener, RSA.listener_prod_fst, luListener]
  congr 1
  ext w : 1
  simp [luSpeaker]

/-- The grammatical lexical-uncertainty listener is exhaustive when *A and B* costs no more than
*A and not B* (§4.3). -/
theorem exhaustive_luListener (hc : s.cAndB ≤ s.cAndNotB) :
    s.Exhaustive (luListener s Interpretation.meaning .a) := by
  rw [Setting.Exhaustive, luListener,
    RSA.listener_apply_eq_posterior _ _ (comp_luSpeaker_ne_zero s _ _),
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

theorem antiExhaustive_luListener_free_iff :
    s.AntiExhaustive (luListener s FreeInterpretation.meaning .a) ↔
      s.logistic (s.cAndNotB + Real.log (1 - s.p)) + s.logistic s.cAndNotB <
        s.logistic (s.cAndB + Real.log s.p) + s.logistic s.cAndB := by
  rw [Setting.AntiExhaustive, luListener,
    RSA.listener_apply_eq_posterior _ _ (comp_luSpeaker_ne_zero s _ _),
    real_lt_posterior_real_singleton_iff_of_pair _ _ (by decide) s.prior_support
      (comp_luSpeaker_ne_zero s _ _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    luSpeaker_real_singleton, luSpeaker_real_singleton]
  simp only [sum_freeInterpretation, FreeInterpretation.meaning]
  rw [speaker_exhaustified_wab_a, speaker_exhaustified_wa_a, speaker_antiExhaustive_wab_a,
    speaker_antiExhaustive_wa_a, Setting.speaker, speaker_literal_wab_a _ s.prior_ne_zero,
    speaker_literal_wa_a _ s.prior_ne_zero, Setting.prior_real_wab, Setting.prior_real_wa]
  have hI : (0 : ℝ) < (Fintype.card FreeInterpretation : ℝ)⁻¹ := by positivity
  constructor <;> intro h <;> nlinarith

theorem antiExhaustive_luListener_free_iff_of_cost_eq (hc : s.cAndB = s.cAndNotB) :
    s.AntiExhaustive (luListener s FreeInterpretation.meaning .a) ↔ 1 / 2 < s.p := by
  rw [antiExhaustive_luListener_free_iff, hc, add_lt_add_iff_right, s.logistic_lt_iff,
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

theorem liMessageSpeaker_wab_lt_wa (hc : s.cAndB ≤ s.cAndNotB) :
    (liMessageSpeaker s .wab).real {.a} < (liMessageSpeaker s .wa).real {.a} := by
  rw [liMessageSpeaker_real_wab_a, liMessageSpeaker_real_wa_a,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have h₁ : Real.exp (s.lam * Real.log s.p) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg s.lam_pos (Real.log_neg s.p_pos s.p_lt_one))
  have h₂ : Real.exp (-(s.lam * s.cAndNotB)) ≤ Real.exp (-(s.lam * s.cAndB)) :=
    Real.exp_le_exp.mpr (by nlinarith [s.lam_pos])
  have h₃ := Real.exp_pos (-(s.lam * s.cAndNotB))
  have h₄ := Real.exp_pos (s.lam * Real.log (1 - s.p))
  nlinarith [mul_lt_mul_of_pos_right h₁ h₃, mul_pos h₄ (Real.exp_pos (-(s.lam * s.cAndB)))]

/-- The lexical-intentions listener is exhaustive when *A and B* costs no more than *A and not B*
(§4.4). -/
theorem exhaustive_liListener (hc : s.cAndB ≤ s.cAndNotB) :
    s.Exhaustive (liListener s .a) := by
  rw [Setting.Exhaustive, liListener,
    RSA.listener_apply_eq_posterior _ _ (comp_liMessageSpeaker_ne_zero s _),
    posterior_real_singleton_lt_iff_of_pair _ _ (by decide) s.prior_support
      (comp_liMessageSpeaker_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _)]
  exact liMessageSpeaker_wab_lt_wa s hc

end LexicalIntentions

end CremersWilcoxSpector2023
