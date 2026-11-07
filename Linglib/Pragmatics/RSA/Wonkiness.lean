module

public import Linglib.Pragmatics.RSA.LexicalUncertainty

/-!
# Wonky worlds

This file defines the wonky-world model of Degen, Tessler and Goodman. The listener is unsure
whether the world is normal, the speaker's prior over states being the measured one, or wonky,
the prior being uniform; in each world the speaker addresses the literal listener of that
world's prior. Under the measured prior on states, as Cremers, Wilcox and Spector propose, the
wonkiness is a latent coordinate of the lexical-uncertainty kind, and the listener comes to
believe more in the wonky world exactly when the utterance is likelier from the speaker who
assumes the uniform prior.

## Main statements

* `RSA.Wonkiness.listener_prod_snd_real_wonky`
* `RSA.Wonkiness.lt_listener_prod_snd_real_wonky_iff`

## References

* [degen-etal-2015]
* [cremers-wilcox-spector-2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

/-- The world is normal, the speaker's prior over states being the measured one, or wonky, the
prior being uniform. -/
inductive Wonkiness where
  | normal
  | wonky
  deriving DecidableEq, Fintype, Nonempty

namespace Wonkiness

instance : MeasurableSpace Wonkiness := ⊤
instance : DiscreteMeasurableSpace Wonkiness := ⟨fun _ ↦ trivial⟩

theorem sum_univ {β : Type*} [AddCommMonoid β] (f : Wonkiness → β) :
    ∑ b, f b = f .normal + f .wonky := by
  rw [show ∑ b, f b = f .normal + (f .wonky + 0) from rfl, add_zero]

variable {W U : Type*} [MeasurableSpace W] [MeasurableSpace U]

/-- The prior over states in each world: the measured prior `μ` in the normal world and the
uniform prior in the wonky one. -/
noncomputable def prior (μ : Measure W) : Kernel Wonkiness W :=
  Kernel.ofFunOfCountable fun
    | .normal => μ
    | .wonky => uniformOn Set.univ

@[simp] theorem prior_normal (μ : Measure W) : prior μ .normal = μ := rfl

@[simp] theorem prior_wonky (μ : Measure W) : prior μ .wonky = uniformOn Set.univ := rfl

instance [Finite W] [Nonempty W] [MeasurableSingletonClass W] (μ : Measure W)
    [IsProbabilityMeasure μ] : IsMarkovKernel (prior μ) :=
  ⟨fun b ↦ by
    cases b
    · exact inferInstanceAs (IsProbabilityMeasure μ)
    · exact isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty⟩

theorem prior_apply_singleton_ne_zero [Fintype W] [MeasurableSingletonClass W] {μ : Measure W}
    {w : W} (hμ : μ {w} ≠ 0) (b : Wonkiness) : prior μ b {w} ≠ 0 := by
  cases b
  · exact hμ
  · exact uniformOn_univ_singleton_ne_zero w

/-- In each world the speaker addresses the literal listener of that world's prior: `S π` is the
speaker under the prior `π`. -/
noncomputable def speaker (S : Measure W → Kernel W U) (μ : Measure W) (p : W × Wonkiness) :
    Measure U :=
  S (prior μ p.2) p.1

theorem speaker_apply (S : Measure W → Kernel W U) (μ : Measure W) (w : W) (b : Wonkiness) :
    speaker S μ (w, b) = S (prior μ b) w := rfl

/-! ### The posterior wonkiness under the measured prior on states -/

variable [Fintype W] [MeasurableSingletonClass W] [Countable U] [MeasurableSingletonClass U]
  (S : Measure W → Kernel W U) [∀ π, IsFiniteKernel (S π)]
  (μ : Measure W) [IsFiniteMeasure μ] (ν : Measure Wonkiness) [IsFiniteMeasure ν] (u : U)

instance (p : W × Wonkiness) : IsFiniteMeasure (speaker S μ p) :=
  inferInstanceAs (IsFiniteMeasure (S _ p.1))

/-- The probability that the speaker of a world produces `u`, averaged over the measured prior. -/
noncomputable def likelihood (b : Wonkiness) : ℝ := ∑ w, μ.real {w} * (S (prior μ b) w).real {u}

omit [MeasurableSingletonClass W] [Countable U] [MeasurableSingletonClass U]
  [∀ π, IsFiniteKernel (S π)] [IsFiniteMeasure μ] in
theorem likelihood_nonneg (b : Wonkiness) : 0 ≤ likelihood S μ u b :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg

/-- After `u`, the listener's belief in the wonky world is its prior weighted by the likelihood
of `u` there, normalized. -/
theorem listener_prod_snd_real_wonky :
    (listener (μ.prod ν) (speaker S μ) u).snd.real {.wonky} =
      ν.real {.wonky} * likelihood S μ u .wonky /
        (ν.real {.normal} * likelihood S μ u .normal +
          ν.real {.wonky} * likelihood S μ u .wonky) := by
  have hT (b : Wonkiness) : (∑ w, μ {w} • speaker S μ (w, b)).real {u} = likelihood S μ u b := by
    rw [measureReal_def, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_sum fun w _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    exact Finset.sum_congr rfl fun w _ ↦ by rw [ENNReal.toReal_mul]; rfl
  have (b : Wonkiness) : IsFiniteMeasure (∑ w, μ {w} • speaker S μ (w, b)) :=
    ⟨by
      rw [Measure.finsetSum_apply]
      exact ENNReal.sum_lt_top.2 fun w _ ↦ by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
  rw [show (listener (μ.prod ν) (speaker S μ) u).snd = (listener (μ.prod ν) (speaker S μ)).snd u
      from (Kernel.snd_apply _ _).symm, listener_prod_snd, listener_real_singleton, sum_univ,
    hT, hT]

variable [IsProbabilityMeasure ν]

omit [MeasurableSingletonClass W] [Countable U] [MeasurableSingletonClass U]
  [∀ π, IsFiniteKernel (S π)] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
private theorem sub_eq_mul_sub :
    ν.real {.wonky} * likelihood S μ u .wonky - ν.real {.wonky} *
        (ν.real {.normal} * likelihood S μ u .normal +
          ν.real {.wonky} * likelihood S μ u .wonky) =
      ν.real {.normal} * ν.real {.wonky} *
        (likelihood S μ u .wonky - likelihood S μ u .normal) := by
  have h1 : ν.real {.normal} + ν.real {.wonky} = 1 := by
    rw [← sum_univ fun b ↦ ν.real {b}, sum_measureReal_singleton_eq_one]
  linear_combination (-(ν.real {.wonky} * likelihood S μ u .wonky)) * h1

variable (hn : ν {.normal} ≠ 0) (hw : ν {.wonky} ≠ 0)
include hn hw

/-- The listener believes more in the wonky world after `u` than before exactly when `u` is
likelier from the speaker who assumes the uniform prior than from the one who assumes the
measured prior. -/
theorem lt_listener_prod_snd_real_wonky_iff :
    ν.real {.wonky} < (listener (μ.prod ν) (speaker S μ) u).snd.real {.wonky} ↔
      likelihood S μ u .normal < likelihood S μ u .wonky := by
  have hn' : 0 < ν.real {.normal} := ENNReal.toReal_pos hn (measure_ne_top _ _)
  have hw' : 0 < ν.real {.wonky} := ENNReal.toReal_pos hw (measure_ne_top _ _)
  have hLn := likelihood_nonneg S μ u .normal
  have hLw := likelihood_nonneg S μ u .wonky
  rw [listener_prod_snd_real_wonky]
  rcases (by positivity : 0 ≤ ν.real {.normal} * likelihood S μ u .normal +
      ν.real {.wonky} * likelihood S μ u .wonky).eq_or_lt with h0 | h0
  · have hn0 : likelihood S μ u .normal = 0 := (mul_eq_zero.1 (by nlinarith)).resolve_left hn'.ne'
    have hw0 : likelihood S μ u .wonky = 0 := (mul_eq_zero.1 (by nlinarith)).resolve_left hw'.ne'
    rw [← h0, div_zero, hn0, hw0]
    exact iff_of_false hw'.not_gt (lt_irrefl 0)
  · rw [lt_div_iff₀ h0, ← sub_pos, sub_eq_mul_sub S μ ν u,
      mul_pos_iff_of_pos_left (mul_pos hn' hw'), sub_pos]

/-- When `u` is possible, the listener believes less in the wonky world after `u` than before
exactly when `u` is likelier from the speaker who assumes the measured prior. -/
theorem listener_prod_snd_real_wonky_lt_iff
    (hu : 0 < likelihood S μ u .normal + likelihood S μ u .wonky) :
    (listener (μ.prod ν) (speaker S μ) u).snd.real {.wonky} < ν.real {.wonky} ↔
      likelihood S μ u .wonky < likelihood S μ u .normal := by
  have hn' : 0 < ν.real {.normal} := ENNReal.toReal_pos hn (measure_ne_top _ _)
  have hw' : 0 < ν.real {.wonky} := ENNReal.toReal_pos hw (measure_ne_top _ _)
  have hLn := likelihood_nonneg S μ u .normal
  have hLw := likelihood_nonneg S μ u .wonky
  have h0 : 0 < ν.real {.normal} * likelihood S μ u .normal +
      ν.real {.wonky} * likelihood S μ u .wonky := by
    rcases hLn.eq_or_lt with h | h
    · rw [← h] at hu ⊢
      simpa using mul_pos hw' (by simpa using hu)
    · exact add_pos_of_pos_of_nonneg (mul_pos hn' h) (mul_nonneg hw'.le hLw)
  rw [listener_prod_snd_real_wonky, div_lt_iff₀ h0, ← sub_pos,
    show ν.real {.wonky} * (ν.real {.normal} * likelihood S μ u .normal +
        ν.real {.wonky} * likelihood S μ u .wonky) - ν.real {.wonky} * likelihood S μ u .wonky =
      ν.real {.normal} * ν.real {.wonky} *
        (likelihood S μ u .normal - likelihood S μ u .wonky) by
      linear_combination -sub_eq_mul_sub S μ ν u,
    mul_pos_iff_of_pos_left (mul_pos hn' hw'), sub_pos]

end Wonkiness

end RSA
