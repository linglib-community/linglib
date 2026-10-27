module

public import Studies.Rett2015
public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Bumford and Rett (2021): Rationalizing evaluativity

Bumford and Rett derive the evaluativity of a degree construction, the inference that a measure
lies beyond the norm of its comparison class, as an implicature drawn by a Rational Speech Act
listener, and they make it graded. A world fixes the subject's height and the centre of its class,
after Barker; each antonym is true relative to a threshold offset from the centre, about which the
listener is uncertain as in the lexical uncertainty model of Bergen, Levy and Goodman; and the
marked antonym costs the speaker more. Evaluativity is the listener's expected deviation of the
measured height from the class centre.

For the positive construction and the exact equative the sign of that expectation is the
antonym's, at every rationality and every cost. Reversing the height scale exchanges the antonyms,
so the two antonyms of a construction differ only through their costs. How strong each inference
is, and so whether the model recovers Rett's categorical classification, is a numerical matter.

## Implementation notes

* A world is the subject's deviation from the class centre, in `[-4, 4]`, together with the
  centre, in `[5, 13]`, which gives exactly the paper's worlds, heights `1..17` within two standard
  deviations of the centre. The prior is the class's Gaussian density, standard deviation 2, at the
  subject's height, and the threshold offsets, in `[-4, 4]`, are uniform.
* The text puts the centre in `[5, 14]`, but the nine centres `5..13` are the figures' columns,
  and a direct simulation of the model with them reproduces all eight first-listener values of
  Table 1 to two decimals.
* Rationality and costs are parameters, and the theorems hold at every rationality and every
  cost. The paper's rationality 4 and costs 0, 1 and 2 enter only the prose. At those costs Rett's
  classification holds as a gap in magnitude, every evaluative cell above every non-evaluative one,
  only for rationality between about 3 and 20, so it is not stated.
* Only the first pragmatic listener is modelled, not the stable iterate the paper also reports.
  The paper ranks the marked antonyms of the positive, the exact equative and the minimum
  equative by strength, but Table 1 bears this out only at the stable iterate: at the first
  listener the minimum equative's −1.52 exceeds the exact equative's −1.06.

## TODO

* In the positive construction and the exact equative the costlier antonym should be the more
  evaluative one at every rationality and cost, as it is in every model checked numerically,
  including random priors and thresholds. Without silence it follows from
  `evaluativity_balances`: the antonyms' expected deviations are then inversely proportional to
  how often each is said, and pairing each point with its reflection shows the costlier antonym is
  said less often. With silence, both constructions reduce to the deviation `X` alone, with
  posterior weight `g X * ℓ X`, and the claim for every symmetric prior `g` is the copositivity of a
  quadratic form. It follows from two facts about the ratio `ρ` of the costlier antonym's `ℓ` to the
  cheaper one's, that `ρ (-X) ≤ ρ X` for `X > 0` and that `ρ` is increasing on `X ≥ 0`, which hold
  numerically but are unproved.
* For the minimum equative the costlier antonym is not always the more evaluative one: it fails
  at high rationality when the two costs are close.
* The stable iterate of the listener.

## References

* [bumford-rett-2021]
* [barker-2002-vagueness]
* [bergen-levy-goodman-2016]
* [rett-2015]
-/

@[expose] public section

namespace BumfordRett2021

open MeasureTheory ProbabilityTheory Degree
open scoped ENNReal

/-! ### Worlds -/

local instance : Nonempty (Finset.Icc (-4 : ℤ) 4) := ⟨⟨0, by decide⟩⟩

/-- The reflection `x ↦ -x` of the interval `[-4, 4]`, in which deviations from the class centre
and threshold offsets both range. -/
def negate (x : Finset.Icc (-4 : ℤ) 4) : Finset.Icc (-4 : ℤ) 4 :=
  ⟨-x, by have := x.2; simp only [Finset.mem_Icc] at *; omega⟩

@[simp] theorem coe_negate (x : Finset.Icc (-4 : ℤ) 4) : (negate x : ℤ) = -x := rfl

theorem negate_involutive : Function.Involutive negate := fun x ↦ by grind [negate]

/-- A world fixes the subject's height relative to the centre of its comparison class, and that
centre. -/
structure World where
  /-- The deviation of the subject's height from the class centre. -/
  deviation : Finset.Icc (-4 : ℤ) 4
  /-- The centre of the comparison class. -/
  centre : Finset.Icc (5 : ℤ) 13
  deriving DecidableEq, Fintype

namespace World

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩
instance : Nonempty World := ⟨⟨⟨0, by decide⟩, ⟨9, by decide⟩⟩⟩

/-- The subject's height. -/
def height (w : World) : ℤ := w.centre + w.deviation

/-- Reversing the height scale about `9`, the middle of the heights `1..17`, which maps the paper's
worlds onto themselves. -/
def reflect (w : World) : World :=
  ⟨negate w.deviation,
    ⟨18 - w.centre, by have := w.centre.2; simp only [Finset.mem_Icc] at *; omega⟩⟩

theorem reflect_involutive : Function.Involutive reflect := fun w ↦ by
  cases w; grind [reflect, negate]

@[simp] theorem centre_reflect (w : World) : (w.reflect.centre : ℤ) = 18 - w.centre := rfl

@[simp] theorem height_reflect (w : World) : w.reflect.height = 18 - w.height := by
  grind [reflect, height, negate]

/-- Reflecting the subject's height about the class centre. -/
def mirror (w : World) : World := ⟨negate w.deviation, w.centre⟩

theorem mirror_involutive : Function.Involutive mirror := fun w ↦ by
  cases w; grind [mirror, negate]

end World

/-! ### Utterances and their interpretations -/

/-- Keisha's height, the median height, is the standard of the equatives and the comparative, and
both speaker and listener know it. -/
def keishaHeight : ℤ := 9

/-- The speaker says the antonym of a polarity, *tall* or *short*, or says nothing. -/
inductive Utterance where
  | say (p : Polarity)
  | silence
  deriving DecidableEq, Fintype

namespace Utterance

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- Exchanging the two antonyms. -/
def antonym : Utterance → Utterance
  | say p => say (Polarity.negative * p)
  | silence => silence

theorem antonym_involutive : Function.Involutive antonym := by
  rintro (⟨_ | _⟩ | _) <;> rfl

end Utterance

/-- The degree an antonym places relative to the threshold is the subject's height in the positive
construction (`none`), which relates the subject to no standard, and Keisha's height in the
constructions relating the subject to Keisha by `=`, `≥` or `>`. -/
def measured (c : Option Comparison) (w : World) : ℤ := c.elim w.height fun _ ↦ keishaHeight

/-- Under the threshold offset `σ`, silence is true everywhere, and the antonym of polarity `p` says
that the subject stands in the construction's relation to Keisha and that the measured height lies
on `p`'s side of the class centre shifted by `σ`. The negative antonym's relations are the order
duals. -/
def Holds (c : Option Comparison) : Utterance → Finset.Icc (-4 : ℤ) 4 → World → Prop
  | .silence, _, _ => True
  | .say p, σ, w => (∀ r ∈ c, (p • r).Rel w.height keishaHeight) ∧
      (p • Comparison.ge).Rel (measured c w) (w.centre + σ)

instance (c : Option Comparison) (u : Utterance) (σ : Finset.Icc (-4 : ℤ) 4) (w : World) :
    Decidable (Holds c u σ w) := by
  cases u <;> unfold Holds <;> infer_instance

theorem holds_reflect (c : Option Comparison) (u : Utterance) (σ : Finset.Icc (-4 : ℤ) 4)
    (w : World) : Holds c u.antonym (negate σ) w.reflect ↔ Holds c u σ w := by
  obtain ⟨⟨d, hd⟩, ⟨m, hm⟩⟩ := w
  obtain ⟨s, hs⟩ := σ
  rcases u with p | _
  · rcases c with _ | r <;> try cases r
    all_goals cases p <;>
      simp [Holds, Utterance.antonym, measured, World.reflect, World.height, keishaHeight] <;> omega
  · rfl

theorem exists_holds (c : Option Comparison) (u : Utterance) :
    ∃ (w : World) (σ : Finset.Icc (-4 : ℤ) 4), Holds c u σ w := by
  rcases u with p | _
  · rcases c with _ | r
    · exact ⟨⟨⟨0, by decide⟩, ⟨9, by decide⟩⟩, ⟨0, by decide⟩, by cases p <;> decide⟩
    · cases r <;> cases p
      all_goals first
        | exact ⟨⟨⟨0, by decide⟩, ⟨9, by decide⟩⟩, ⟨0, by decide⟩, by decide⟩
        | exact ⟨⟨⟨1, by decide⟩, ⟨9, by decide⟩⟩, ⟨0, by decide⟩, by decide⟩
        | exact ⟨⟨⟨-1, by decide⟩, ⟨9, by decide⟩⟩, ⟨0, by decide⟩, by decide⟩
  · exact ⟨⟨⟨0, by decide⟩, ⟨9, by decide⟩⟩, ⟨0, by decide⟩, trivial⟩

/-! ### The listener -/

/-- The listener's prior weights a world by the density of its comparison class's heights, Gaussian
about the centre with standard deviation 2, at the subject's height, so the centre is uniform. -/
noncomputable def prior : Measure World :=
  Measure.count.withDensity fun w ↦
    ENNReal.ofReal (gaussianPDFReal (w.centre : ℤ) 4 w.height)

theorem prior_singleton (w : World) :
    prior {w} = ENNReal.ofReal (gaussianPDFReal (w.centre : ℤ) 4 w.height) := by
  rw [prior, withDensity_apply _ (.singleton w), Measure.restrict_singleton,
    Measure.count_singleton, one_smul, lintegral_dirac]

instance : IsFiniteMeasure prior :=
  isFiniteMeasure_withDensity (by
    rw [lintegral_fintype]
    exact ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))

theorem prior_singleton_ne_zero (w : World) : prior {w} ≠ 0 := by
  rw [prior_singleton]
  exact (ENNReal.ofReal_pos.mpr (gaussianPDFReal_pos _ _ _ (by norm_num))).ne'

theorem prior_singleton_congr {w w' : World} (h : (w.deviation : ℤ) ^ 2 = (w'.deviation : ℤ) ^ 2) :
    prior {w} = prior {w'} := by
  have h' : ((w.height : ℝ) - ((w.centre : ℤ) : ℝ)) ^ 2
      = ((w'.height : ℝ) - ((w'.centre : ℤ) : ℝ)) ^ 2 := by
    simp only [World.height]; push_cast; ring_nf; exact_mod_cast h
  rw [prior_singleton, prior_singleton]
  simp only [gaussianPDFReal, h']

theorem prior_reflect (w : World) : prior {w.reflect} = prior {w} :=
  prior_singleton_congr (by simp [World.reflect])

theorem prior_mirror (w : World) : prior {w.mirror} = prior {w} :=
  prior_singleton_congr (by simp [World.mirror])

theorem prior_prod_count_singleton (q : World × Finset.Icc (-4 : ℤ) 4) :
    (prior.prod Measure.count) {q} = prior {q.1} := by
  rw [← Prod.mk.eta (p := q), ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, mul_one]

/-- The literal listener under the threshold offset `σ` conditions the prior on the truth of the
utterance. -/
noncomputable def literal (c : Option Comparison) (σ : Finset.Icc (-4 : ℤ) 4) :
    Kernel Utterance World :=
  RSA.listener prior (RSA.truthful fun u ↦ {w | Holds c u σ w})

instance (c : Option Comparison) (σ : Finset.Icc (-4 : ℤ) 4) : IsFiniteKernel (literal c σ) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ (RSA.truthful _)))

/-- The speaker at a world and a threshold offset addresses the literal listener under that
offset, at rationality `α` with costs `cost`. -/
noncomputable def speaker (c : Option Comparison) (α : ℝ) (cost : Utterance → ℝ) :
    Kernel (World × Finset.Icc (-4 : ℤ) 4) Utterance :=
  Kernel.ofFunOfCountable fun q ↦ RSA.speaker α cost (literal c q.2) Measure.dirac q.1

@[simp] theorem speaker_apply (c : Option Comparison) (α : ℝ) (cost : Utterance → ℝ)
    (q : World × Finset.Icc (-4 : ℤ) 4) :
    speaker c α cost q = RSA.speaker α cost (literal c q.2) Measure.dirac q.1 := rfl

instance (c : Option Comparison) (α : ℝ) (cost : Utterance → ℝ) :
    IsFiniteKernel (speaker c α cost) :=
  ⟨⟨1, ENNReal.one_lt_top, fun q ↦ RSA.speaker_apply_univ_le_one α cost _ Measure.dirac q.1⟩⟩

/-- The pragmatic listener at rationality `α`, with the speaker's costs `cost`, inverts the
speakers indexed by the threshold offsets against the prior on worlds and uniform offsets. -/
noncomputable def listener (c : Option Comparison) (α : ℝ) (cost : Utterance → ℝ) :
    Kernel Utterance (World × Finset.Icc (-4 : ℤ) 4) :=
  RSA.listener (prior.prod Measure.count) (speaker c α cost)

instance (c : Option Comparison) (α : ℝ) (cost : Utterance → ℝ) :
    IsFiniteKernel (listener c α cost) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ _))

/-- The listener's expected deviation of the measured height from the class centre, after the
antonym of polarity `p`, is the statistic of evaluativity that the paper's Table 1 reports. -/
noncomputable def expectedDeviation (c : Option Comparison) (α : ℝ) (cost : Utterance → ℝ)
    (p : Polarity) : ℝ :=
  ∫ w, ((measured c w - w.centre : ℤ) : ℝ) ∂(listener c α cost (.say p)).fst

section Pipeline

variable {α : ℝ} {cost : Utterance → ℝ}

private theorem literal_ne_zero {c σ u w} (h : Holds c u σ w) : literal c σ u {w} ≠ 0 :=
  (RSA.listener_truthful_apply_singleton_ne_zero_iff prior
    (fun u ↦ {w | Holds c u σ w}) u w).mpr ⟨h, prior_singleton_ne_zero w⟩

private theorem literal_eq_zero {c σ u w} (h : ¬ Holds c u σ w) : literal c σ u {w} = 0 :=
  RSA.listener_truthful_apply_singleton_of_notMem prior (fun u ↦ {w | Holds c u σ w}) h

theorem comp_speaker_ne_zero (hα : 0 ≤ α) (c : Option Comparison) (u : Utterance) :
    (speaker c α cost ∘ₘ prior.prod Measure.count) {u} ≠ 0 := by
  obtain ⟨w, σ, h⟩ := exists_holds c u
  refine Measure.comp_apply_singleton_ne_zero _ _ (a := (w, σ))
    (by rw [prior_prod_count_singleton]; exact prior_singleton_ne_zero w) ?_
  rw [speaker_apply]
  exact RSA.speaker_dirac_apply_singleton_ne_zero hα (literal_ne_zero h)

private theorem listener_fst_real_singleton (c : Option Comparison) (u : Utterance) (w : World) :
    (listener c α cost u).fst.real {w} =
      (prior {w}).toReal * (∑ σ, (RSA.speaker α cost (literal c σ) Measure.dirac w).real {u}) /
        (speaker c α cost ∘ₘ prior.prod Measure.count).real {u} := by
  rw [listener, Measure.comp_real_singleton, RSA.listener_prod_fst_real_singleton]
  simp [measureReal_def]

private theorem speaker_real_le (hα : 0 < α) {c σ u} {w₁ w₂ : World}
    (hu : Holds c u σ w₁ → Holds c u σ w₂)
    (halt : Holds c u σ w₁ → ∀ u', Holds c u' σ w₂ → Holds c u' σ w₁) :
    (RSA.speaker α cost (literal c σ) Measure.dirac w₁).real {u} ≤
      (RSA.speaker α cost (literal c σ) Measure.dirac w₂).real {u} := by
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  by_cases h₁ : Holds c u σ w₁
  · exact RSA.speaker_listener_truthful_dirac_le_of_subset hα cost prior _
      (prior_singleton_ne_zero w₂) (halt h₁) (hu h₁)
  · rw [RSA.speaker_dirac_apply_singleton_eq_zero hα (literal_eq_zero h₁)]; exact zero_le

private theorem listener_fst_real_le (hα : 0 < α) {c u} {w₁ w₂ : World}
    (hp : prior {w₁} = prior {w₂})
    (hu : ∀ σ, Holds c u σ w₁ → Holds c u σ w₂)
    (halt : ∀ σ, Holds c u σ w₁ → ∀ u', Holds c u' σ w₂ → Holds c u' σ w₁) :
    (listener c α cost u).fst.real {w₁} ≤ (listener c α cost u).fst.real {w₂} := by
  rw [listener_fst_real_singleton, listener_fst_real_singleton, hp]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun σ _ ↦ speaker_real_le hα (hu σ) (halt σ)) ENNReal.toReal_nonneg)
    measureReal_nonneg

private theorem listener_fst_real_lt (hα : 0 < α) {c u} {w₁ w₂ : World}
    (hp : prior {w₁} = prior {w₂})
    (hu : ∀ σ, Holds c u σ w₁ → Holds c u σ w₂)
    (halt : ∀ σ, Holds c u σ w₁ → ∀ u', Holds c u' σ w₂ → Holds c u' σ w₁)
    {σ₀ : Finset.Icc (-4 : ℤ) 4} (h₁ : ¬ Holds c u σ₀ w₁) (h₂ : Holds c u σ₀ w₂) :
    (listener c α cost u).fst.real {w₁} < (listener c α cost u).fst.real {w₂} := by
  rw [listener_fst_real_singleton, listener_fst_real_singleton, hp]
  refine div_lt_div_of_pos_right (mul_lt_mul_of_pos_left ?_
    (ENNReal.toReal_pos (prior_singleton_ne_zero _) (measure_ne_top _ _)))
    (ENNReal.toReal_pos (comp_speaker_ne_zero hα.le c u) (measure_ne_top _ _))
  refine Finset.sum_lt_sum (fun σ _ ↦ speaker_real_le hα (hu σ) (halt σ))
    ⟨σ₀, Finset.mem_univ _, ?_⟩
  rw [measureReal_def, measureReal_def,
    RSA.speaker_dirac_apply_singleton_eq_zero hα (literal_eq_zero h₁), ENNReal.toReal_zero]
  exact ENNReal.toReal_pos (RSA.speaker_dirac_apply_singleton_ne_zero hα.le (literal_ne_zero h₂))
    (measure_ne_top _ _)

private theorem integral_pos_of_involutive {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (P : Measure β) [IsFiniteMeasure P] (X : β → ℝ) {R : β → β}
    (hR : Function.Involutive R) (hX : ∀ b, X (R b) = -X b)
    (hle : ∀ b, 0 < X b → P.real {R b} ≤ P.real {b})
    {b₀ : β} (hb₀ : 0 < X b₀) (hlt : P.real {R b₀} < P.real {b₀}) : 0 < ∫ b, X b ∂P := by
  rw [integral_fintype .of_finite]
  simp only [smul_eq_mul]
  have hrefl : ∑ b, P.real {b} * X b = -∑ b, P.real {R b} * X b := by
    rw [← Equiv.sum_comp hR.toPerm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [Function.Involutive.coe_toPerm, hX]; ring
  suffices 0 < ∑ b, (P.real {b} - P.real {R b}) * X b by
    simp only [sub_mul, Finset.sum_sub_distrib] at this; linarith
  refine Finset.sum_pos' (fun b _ ↦ ?_) ⟨b₀, Finset.mem_univ _, mul_pos (by linarith) hb₀⟩
  have hR' := hle (R b); rw [hX, hR b] at hR'
  rcases lt_trichotomy (X b) 0 with h | h | h
  · nlinarith [hR' (by linarith)]
  · simp [h]
  · nlinarith [hle b h]

end Pipeline

/-! ### Antonym symmetry -/

section Antonym

variable {α : ℝ} {cost : Utterance → ℝ}

theorem literal_antonym (c : Option Comparison) (σ : Finset.Icc (-4 : ℤ) 4) (u : Utterance)
    (w : World) : literal c (negate σ) u.antonym {w.reflect} = literal c σ u {w} :=
  RSA.listener_truthful_apply_singleton_of_equiv World.reflect_involutive.toPerm prior_reflect
    (fun w ↦ by simp only [Function.Involutive.coe_toPerm, Set.mem_ofPred_eq, holds_reflect]) w

theorem listener_antonym (c : Option Comparison) (u : Utterance) (w : World)
    (σ : Finset.Icc (-4 : ℤ) 4) :
    listener c α cost u.antonym {(w.reflect, negate σ)} =
      listener c α (cost ∘ Utterance.antonym) u {(w, σ)} :=
  RSA.listener_apply_singleton_of_equiv _ _
    (World.reflect_involutive.toPerm.prodCongr negate_involutive.toPerm)
    (fun p ↦ by
      rw [Equiv.prodCongr_apply, Prod.map, prior_prod_count_singleton,
        prior_prod_count_singleton]
      exact prior_reflect p.1)
    (fun p ↦ RSA.speaker_dirac_apply_singleton_of_equiv Utterance.antonym_involutive.toPerm α cost
      (fun v ↦ literal_antonym c p.2 v p.1) u)
    (w, σ)

theorem measured_reflect (c : Option Comparison) (w : World) :
    measured c w.reflect - w.reflect.centre = -(measured c w - w.centre) := by
  rcases c with _ | _ <;> grind [measured, keishaHeight, World.height_reflect, World.centre_reflect]

/-- The negative antonym's expected deviation is minus the positive antonym's with the costs of
the antonyms exchanged, so the antonyms of a construction differ only through their costs. -/
theorem expectedDeviation_antonym (c : Option Comparison) (p : Polarity) :
    expectedDeviation c α cost (Polarity.negative * p) =
      -expectedDeviation c α (cost ∘ Utterance.antonym) p := by
  rw [expectedDeviation, expectedDeviation, Measure.fst, Measure.fst,
    integral_map measurable_fst.aemeasurable (by fun_prop),
    integral_map measurable_fst.aemeasurable (by fun_prop),
    integral_fintype .of_finite, integral_fintype .of_finite,
    ← (World.reflect_involutive.toPerm.prodCongr negate_involutive.toPerm).sum_comp,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [Equiv.prodCongr_apply, Prod.map, Function.Involutive.coe_toPerm, smul_eq_mul,
    measureReal_def]
  rw [show Utterance.say (Polarity.negative * p) = (Utterance.say p).antonym from rfl,
    listener_antonym c (.say p) q.1 q.2, measured_reflect]
  push_cast; ring

theorem expectedDeviation_negative_of_cost_eq
    (hc : cost (.say .positive) = cost (.say .negative)) (c : Option Comparison) :
    expectedDeviation c α cost .negative = -expectedDeviation c α cost .positive := by
  have hcost : cost ∘ Utterance.antonym = cost := funext fun u ↦ by
    rcases u with ⟨_ | _⟩ | _ <;> simp [Utterance.antonym, hc]
  simpa [hcost] using expectedDeviation_antonym (cost := cost) c .positive

end Antonym

/-! ### Evaluativity of the positive and the exact equative -/

section Evaluative

variable {α : ℝ} {cost : Utterance → ℝ}

private theorem positive_tall (hα : 0 < α) :
    0 < expectedDeviation none α cost .positive := by
  refine integral_pos_of_involutive _ _ World.mirror_involutive (fun w ↦ ?_) (fun w hw ↦ ?_)
    (b₀ := ⟨⟨1, by decide⟩, ⟨9, by decide⟩⟩) (by simp [measured, World.height])
    (listener_fst_real_lt hα (prior_mirror _) ?_ ?_ (σ₀ := ⟨0, by decide⟩)
      (by decide) (by decide))
  · simp only [measured, Option.elim, World.mirror, World.height, coe_negate]; push_cast; ring
  · obtain ⟨⟨d, hd⟩, ⟨m, hm⟩⟩ := w
    have hw' : 0 < d := by simpa [measured, World.height] using hw
    refine listener_fst_real_le hα (prior_mirror _) (fun ⟨s, hs⟩ h ↦ ?_)
      fun ⟨s, hs⟩ h u' h' ↦ ?_
    · simp [Holds, measured, World.mirror, World.height] at *; omega
    · rcases u' with ⟨_ | _⟩ | _ <;>
        simp [Holds, measured, World.mirror, World.height] at * <;> omega
  · rintro ⟨s, hs⟩ h; simp [Holds, measured, World.mirror, World.height] at *; omega
  · rintro ⟨s, hs⟩ h u' h'
    rcases u' with ⟨_ | _⟩ | _ <;>
      simp [Holds, measured, World.mirror, World.height] at * <;> omega

private theorem exactEquative_tall (hα : 0 < α) :
    0 < expectedDeviation (some .eq) α cost .positive := by
  refine integral_pos_of_involutive _ _ World.reflect_involutive
    (fun w ↦ by rw [measured_reflect]; push_cast; ring) (fun w hw ↦ ?_)
    (b₀ := ⟨⟨1, by decide⟩, ⟨8, by decide⟩⟩) (by simp [measured, keishaHeight])
    (listener_fst_real_lt hα (prior_reflect _) ?_ ?_ (σ₀ := ⟨0, by decide⟩)
      (by decide) (by decide))
  · obtain ⟨⟨d, hd⟩, ⟨m, hm⟩⟩ := w
    have hw' : (m : ℝ) < 9 := by simpa [measured, keishaHeight] using hw
    have hw'' : m < 9 := by exact_mod_cast hw'
    refine listener_fst_real_le hα (prior_reflect _) (fun ⟨s, hs⟩ h ↦ ?_)
      fun ⟨s, hs⟩ h u' h' ↦ ?_
    · simp [Holds, measured, World.reflect, World.height, keishaHeight] at *; omega
    · rcases u' with ⟨_ | _⟩ | _ <;>
        simp [Holds, measured, World.reflect, World.height, keishaHeight] at * <;> omega
  · rintro ⟨s, hs⟩ h; simp [Holds, measured, World.reflect, World.height, keishaHeight] at *; omega
  · rintro ⟨s, hs⟩ h u' h'
    rcases u' with ⟨_ | _⟩ | _ <;>
      simp [Holds, measured, World.reflect, World.height, keishaHeight] at * <;> omega

/-- The positive construction is evaluative for both antonyms, at every rationality and every
cost. After *tall* the listener expects the subject above the centre of the class, and after
*short* below it. -/
theorem positive_evaluative (hα : 0 < α) (p : Polarity) :
    0 < p • expectedDeviation none α cost p := by
  cases p
  · simpa using positive_tall hα
  · rw [Polarity.negative_smul, show Polarity.negative = Polarity.negative * .positive from rfl,
      expectedDeviation_antonym, neg_neg]
    exact positive_tall hα

/-- The exact equative shifts the listener for both antonyms, at every rationality and every
cost. After *exactly as tall as Keisha* the listener expects Keisha above the centre of the class,
and after *exactly as short as Keisha* below it, so the unmarked antonym is evaluative in direction
and its weakness in the paper is one of magnitude. -/
theorem exactEquative_evaluative (hα : 0 < α) (p : Polarity) :
    0 < p • expectedDeviation (some .eq) α cost p := by
  cases p
  · simpa using exactEquative_tall hα
  · rw [Polarity.negative_smul, show Polarity.negative = Polarity.negative * .positive from rfl,
      expectedDeviation_antonym, neg_neg]
    exact exactEquative_tall hα

end Evaluative

/-! ### What the positive construction leaves open -/

section Centre

variable {α : ℝ} {cost : Utterance → ℝ}

/-- Exchanging two class centres, keeping the subject's deviation. -/
private def World.recentre (m m' : Finset.Icc (5 : ℤ) 13) (w : World) : World :=
  ⟨w.deviation, Equiv.swap m m' w.centre⟩

private theorem World.recentre_involutive (m m' : Finset.Icc (5 : ℤ) 13) :
    Function.Involutive (World.recentre m m') := fun w ↦ by
  simp [World.recentre]

private theorem holds_none_recentre (m m' : Finset.Icc (5 : ℤ) 13) (u : Utterance)
    (σ : Finset.Icc (-4 : ℤ) 4) (w : World) :
    Holds none u σ (w.recentre m m') ↔ Holds none u σ w := by
  rcases u with p | _
  · cases p <;> simp [Holds, measured, World.recentre, World.height]
  · rfl

private theorem listener_positive_recentre (hα : 0 < α) (m m' : Finset.Icc (5 : ℤ) 13)
    (u : Utterance) (w : World) :
    (listener none α cost u).fst {w.recentre m m'} = (listener none α cost u).fst {w} := by
  rw [Measure.fst_apply_singleton, Measure.fst_apply_singleton]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [listener, RSA.listener_apply_singleton_eq_div,
    RSA.listener_apply_singleton_eq_div, prior_prod_count_singleton,
    prior_prod_count_singleton, prior_singleton_congr (w' := w) (by simp [World.recentre])]
  congr 2
  exact congrFun (congrArg _ (RSA.speaker_listener_truthful_dirac_congr hα cost prior
    (fun u ↦ {w | Holds none u σ w}) (prior_singleton_ne_zero w) (prior_singleton_ne_zero _)
    fun u ↦ (holds_none_recentre m m' u σ w).symm)) _

theorem positive_centre_uniform (hα : 0 < α) (u : Utterance) :
    (listener none α cost u).fst.map World.centre = uniformOn Set.univ := by
  have : IsProbabilityMeasure (listener none α cost u) :=
    RSA.isProbabilityMeasure_listener _ _ (comp_speaker_ne_zero hα.le none u)
  set P := (listener none α cost u).fst
  have hconst : ∀ m m', P.map World.centre {m'} = P.map World.centre {m} := fun m m' ↦ by
    have hR : P.map (World.recentre m m') = P := Measure.ext_of_singleton fun w ↦ by
      rw [Measure.map_apply (by fun_prop) (.singleton w),
        show World.recentre m m' ⁻¹' {w} = {World.recentre m m' w} from by
          ext v; simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h ↦ h ▸ (World.recentre_involutive m m' v).symm,
            fun h ↦ h ▸ World.recentre_involutive m m' w⟩,
        listener_positive_recentre hα]
    have hpre : World.centre ⁻¹' {m'} = World.recentre m m' ⁻¹' (World.centre ⁻¹' {m}) := by
      ext w; simp [World.recentre, Equiv.swap_apply_eq_iff]
    rw [Measure.map_apply (by fun_prop) (.singleton _),
      Measure.map_apply (by fun_prop) (.singleton _),
      hpre, ← Measure.map_apply (by fun_prop) (by measurability), hR]
  refine Measure.ext_of_singleton fun m ↦ ?_
  have hsum : ∑ m', P.map World.centre {m'} = 1 := by
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
  simp only [hconst m, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [uniformOn_univ, Measure.count_singleton, ENNReal.eq_div_iff (by simp) (by simp)]
  exact hsum

end Centre

/-! ### Evaluativity balances across the speaker's choices -/

section Balance

variable {α : ℝ} {cost : Utterance → ℝ}

theorem isMarkovKernel_speaker (hα : 0 ≤ α) (c : Option Comparison) :
    IsMarkovKernel (speaker c α cost) :=
  ⟨fun q ↦ by
    rw [speaker_apply]
    exact (RSA.isMarkovKernel_speaker_dirac hα cost (literal c q.2)
      (fun w ↦ ⟨.silence, literal_ne_zero (c := c) trivial⟩)).isProbabilityMeasure q.1⟩

/-- Weighted by how often the speaker makes each utterance, the listener's expected deviations sum
to the prior's, which is zero. The listener's beliefs average back to the prior, so an antonym the
speaker says rarely carries a more extreme inference. -/
theorem evaluativity_balances (hα : 0 ≤ α) (c : Option Comparison) :
    ∑ u, (speaker c α cost ∘ₘ prior.prod Measure.count).real {u} *
      ∫ w, ((measured c w - w.centre : ℤ) : ℝ) ∂(listener c α cost u).fst = 0 := by
  have := isMarkovKernel_speaker (cost := cost) hα c
  set f : World × Finset.Icc (-4 : ℤ) 4 → ℝ := fun q ↦ ((measured c q.1 - q.1.centre : ℤ) : ℝ)
  have hint : ∀ u, ∫ w, ((measured c w - w.centre : ℤ) : ℝ) ∂(listener c α cost u).fst =
      ∑ q, (listener c α cost u).real {q} * f q := fun u ↦ by
    rw [Measure.fst, integral_map measurable_fst.aemeasurable (by fun_prop),
      integral_fintype .of_finite]
    simp [f, smul_eq_mul]
  have hsym : ∑ q, (prior.prod Measure.count).real {q} * f q = 0 := by
    set e := World.reflect_involutive.toPerm.prodCongr negate_involutive.toPerm
    have hneg : ∑ q, (prior.prod Measure.count).real {e q} * f (e q) =
        -∑ q, (prior.prod Measure.count).real {q} * f q := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      have hm : (prior.prod Measure.count).real {(q.1.reflect, negate q.2)} =
          (prior.prod Measure.count).real {q} := by
        rw [measureReal_def, measureReal_def, prior_prod_count_singleton,
          prior_prod_count_singleton, prior_reflect]
      have hf : f (q.1.reflect, negate q.2) = -f q := by
        simp only [f]; rw [measured_reflect]; push_cast; ring
      simp only [e, Equiv.prodCongr_apply, Prod.map, Function.Involutive.coe_toPerm]
      rw [hm, hf]; ring
    rw [e.sum_comp (fun q ↦ (prior.prod Measure.count).real {q} * f q)] at hneg
    linarith
  calc ∑ u, (speaker c α cost ∘ₘ prior.prod Measure.count).real {u} *
        ∫ w, ((measured c w - w.centre : ℤ) : ℝ) ∂(listener c α cost u).fst
      = ∑ q, (∑ u, (speaker c α cost ∘ₘ prior.prod Measure.count).real {u} *
          (listener c α cost u).real {q}) * f q := by
        simp_rw [hint, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc]
    _ = ∑ q, (prior.prod Measure.count).real {q} * f q := by
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [listener]
        simp_rw [RSA.comp_real_mul_listener_real]
        rw [← Finset.mul_sum, sum_measureReal_singleton_eq_one, mul_one]
    _ = 0 := hsym

end Balance

/-! ### Competition between the antonyms and Rett's classification

Rett derives the evaluativity of the marked antonym from its competition with an unmarked antonym
of the same truth conditions, which only the polar-invariant constructions provide. In the graded
model the antonyms compete wherever both are true; where they never are, as in the comparative,
each antonym's listener ignores the other antonym's cost, and markedness acts only through the
antonym's own cost. -/

/-- A simulated construction instantiates the positive construction, the equative for the
comparisons `=` and `≥`, or the comparative for `>`, in Rett's classification. -/
def construction : Option Comparison → Construction
  | none => .positive
  | some .gt | some .lt => .comparative
  | some _ => .equative

/-- The antonyms of a construction exclude each other when no world verifies both under any
offset. -/
def AntonymsExclusive (c : Option Comparison) : Prop :=
  ∀ σ w, ¬ (Holds c (.say .positive) σ w ∧ Holds c (.say .negative) σ w)

theorem antonymsExclusive_comparative : AntonymsExclusive (some .gt) := fun σ w h ↦ by
  simp [Holds] at h; omega

/-- Among the constructions relating the subject to Keisha, the antonyms exclude each other exactly
where Rett's classification makes the construction polar-variant. -/
theorem antonymsExclusive_iff_not_isPolarInvariant {r : Comparison}
    (hr : r = .eq ∨ r = .ge ∨ r = .gt) :
    AntonymsExclusive (some r) ↔ ¬ Rett2015.IsPolarInvariant (construction (some r)) := by
  have hboth : ∀ r, r = .eq ∨ r = .ge → ¬ AntonymsExclusive (some r) := by
    rintro r (rfl | rfl) h <;>
      exact h ⟨0, by decide⟩ ⟨⟨0, by decide⟩, ⟨9, by decide⟩⟩ (by decide)
  rcases hr with rfl | rfl | rfl
  · exact iff_of_false (hboth _ (.inl rfl)) (by decide)
  · exact iff_of_false (hboth _ (.inr rfl)) (by decide)
  · exact iff_of_true antonymsExclusive_comparative (by decide)

section Competition

variable {α : ℝ} {cost cost' : Utterance → ℝ}

private theorem speaker_congr_of_antonymsExclusive (hα : 0 < α) {c : Option Comparison}
    (hex : AntonymsExclusive c) {p : Polarity} (hp : cost (.say p) = cost' (.say p))
    (hs : cost .silence = cost' .silence) (σ : Finset.Icc (-4 : ℤ) 4) (w : World) :
    RSA.speaker α cost (literal c σ) Measure.dirac w {.say p} =
      RSA.speaker α cost' (literal c σ) Measure.dirac w {.say p} := by
  by_cases h : Holds c (.say p) σ w
  · have hw : ∀ u, literal c σ u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * cost u))) =
        literal c σ u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * cost' u))) := by
      rintro (q | _)
      · by_cases hq : q = p
        · rw [hq, hp]
        · have hq' : ¬ Holds c (.say q) σ w := fun h' ↦ by
            cases p <;> cases q
            all_goals first | exact hq rfl | exact hex σ w ⟨h, h'⟩ | exact hex σ w ⟨h', h⟩
          rw [literal_eq_zero hq', ENNReal.zero_rpow_of_pos hα, zero_mul, zero_mul]
      · rw [hs]
    simp only [RSA.speaker_dirac_apply_singleton, hw]
  · rw [RSA.speaker_dirac_apply_singleton_eq_zero hα (literal_eq_zero h),
      RSA.speaker_dirac_apply_singleton_eq_zero hα (literal_eq_zero h)]

/-- Where the antonyms exclude each other, an antonym's expected deviation depends on the costs only
through its own cost and silence's, since the other antonym never competes with it. -/
theorem expectedDeviation_congr_of_antonymsExclusive (hα : 0 < α) {c : Option Comparison}
    (hex : AntonymsExclusive c) {p : Polarity} (hp : cost (.say p) = cost' (.say p))
    (hs : cost .silence = cost' .silence) :
    expectedDeviation c α cost p = expectedDeviation c α cost' p := by
  have hS := speaker_congr_of_antonymsExclusive hα hex hp hs
  have hM : (speaker c α cost ∘ₘ prior.prod Measure.count) {.say p} =
      (speaker c α cost' ∘ₘ prior.prod Measure.count) {.say p} := by
    simp only [Measure.comp_apply_singleton, speaker_apply, hS]
  rw [expectedDeviation, expectedDeviation, integral_fintype .of_finite,
    integral_fintype .of_finite]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [listener_fst_real_singleton, listener_fst_real_singleton]
  simp only [measureReal_def, hS, hM]

theorem comparative_negative_eq_neg (hα : 0 < α)
    (hp : cost' (.say .positive) = cost (.say .negative)) (hs : cost' .silence = cost .silence) :
    expectedDeviation (some .gt) α cost .negative =
      -expectedDeviation (some .gt) α cost' .positive := by
  rw [show Polarity.negative = Polarity.negative * .positive from rfl,
    expectedDeviation_antonym,
    expectedDeviation_congr_of_antonymsExclusive (cost := cost ∘ Utterance.antonym)
      (cost' := cost') (p := .positive) hα antonymsExclusive_comparative hp.symm hs.symm]

end Competition

end BumfordRett2021
