module

public import Studies.DegenEtAl2020
public import Linglib.Data.Statistics.KursatDegen2021

/-!
# Kursat and Degen (2021): Perceptual difficulty differences predict asymmetry in redundant modification with color and material adjectives

Kursat and Degen's Perceptual Difficulty Hypothesis. In the continuous-semantics model of Degen
and colleagues an adjective is noisy to a degree, and the hypothesis is that the noise reflects
how hard it is to see whether an object has the property, so the semantic value of an adjective
falls as its property gets harder to verify. The model then predicts that a harder property is
mentioned redundantly less often. This file derives the prediction for the critical display of the
paper's production experiment, which shows a target, a competitor sharing the redundant property
with it, and two distractors sharing the sufficient property with the competitor, and reads the
paper's findings off its printed statistics.

## Implementation notes

* The display is reduced to the roles of its two properties, so a colour-redundant trial and a
  material-redundant trial are one model with the semantic values swapped, and the cost of an
  expression depends only on how many adjectives it has.
* The hypothesis is rendered as a strictly decreasing map from difficulty to semantic value. The
  paper says only that the noise reflects the difficulty.
* An effect counts as found when its printed p-value is below .05.

## References

* [kursat-degen-2021]
* [degen-etal-2020]
-/

@[expose] public section

namespace KursatDegen2021

open Data.Statistics DegenEtAl2020

/-! ### The critical display of the production experiment -/

/-- A critical trial shows four objects of one kind, the target, a competitor that shares the
redundant property with it, and two distractors that share the sufficient property with the
competitor. -/
inductive Object where
  | target
  | competitor
  | distractor₁
  | distractor₂
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Object := ⊤
instance : DiscreteMeasurableSpace Object := ⟨fun _ ↦ trivial⟩

/-- A referring expression has the sufficient adjective alone or both adjectives. -/
inductive Utterance where
  | sufficient
  | redundant
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- The continuous meaning gives the sufficient adjective the semantic value `xs` and the
redundant one `xr`. The Boolean extension of the sufficient adjective is the target alone, and
that of the redundant adjective is the target and the competitor. -/
def meaning (xs xr : ℝ) : Utterance → Object → ℝ
  | .sufficient, o => noisy xs (o = .target)
  | .redundant, o => noisy xs (o = .target) * noisy xr (o = .target ∨ o = .competitor)

section Model

variable {xs xr xr' α : ℝ} {C : Utterance → ℝ}

theorem meaning_nonneg (hs0 : 0 ≤ xs) (hs1 : xs ≤ 1) (hr0 : 0 ≤ xr) (hr1 : xr ≤ 1)
    (u : Utterance) (o : Object) : 0 ≤ meaning xs xr u o := by
  cases u
  · exact noisy_nonneg hs0 hs1 _
  · exact mul_nonneg (noisy_nonneg hs0 hs1 _) (noisy_nonneg hr0 hr1 _)

private theorem sum_object (f : Object → ℝ) :
    ∑ o, f o = f .target + f .competitor + f .distractor₁ + f .distractor₂ := by
  rw [show (Finset.univ : Finset Object) =
      {.target, .competitor, .distractor₁, .distractor₂} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The speaker's probability of the redundant expression for the target is a logistic function
of the log of the gain of the redundant adjective, less the extra cost. -/
theorem redundant_eq_sigmoid (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hr0 : 0 < xr)
    (hr1 : xr ≤ 1) :
    (S1 α C (meaning xs xr) .target).real {.redundant} =
      Real.sigmoid (α * (Real.log (gain 2 xs xr) - (C .redundant - C .sufficient))) := by
  have hden : 0 < xr + 2 * (1 - xs) * (1 - xr) := by nlinarith
  have hr : meaning xs xr .redundant .target = xs * xr := by simp [meaning, noisy]
  have hs : meaning xs xr .sufficient .target = xs := by simp [meaning, noisy]
  have hrow : ∑ o, meaning xs xr .redundant o = xr + 2 * (1 - xs) * (1 - xr) := by
    rw [sum_object]; simp [meaning, noisy]; ring
  have hrow' : ∑ o, meaning xs xr .sufficient o = 3 - 2 * xs := by
    rw [sum_object]; simp [meaning, noisy]; ring
  rw [S1_real_of_pair hα (u' := .sufficient) (by decide) (meaning_nonneg hs0.le hs1 hr0.le hr1)
      (by rw [hr]; positivity) (by rwa [hs]) (fun v _ ↦ by cases v <;> simp),
    hr, hs, hrow, hrow', sub_sub_sub_comm,
    ← Real.log_div (by positivity) (div_pos hs0 (by linarith)).ne', gain, Nat.cast_ofNat]
  congr 4
  field_simp
  ring

theorem redundant_of_boolean_sufficient (hα : 0 < α) (hr0 : 0 < xr) (hr1 : xr ≤ 1) :
    (S1 α C (meaning 1 xr) .target).real {.redundant} =
      Real.sigmoid (-(α * (C .redundant - C .sufficient))) := by
  rw [redundant_eq_sigmoid hα one_pos le_rfl hr0 hr1, gain_one_left hr0.ne', Real.log_one,
    zero_sub, mul_neg]

theorem redundant_lt_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs < 1) (hr0 : 0 < xr)
    (hr1 : xr ≤ 1) (hr0' : 0 < xr') (hr1' : xr' ≤ 1) :
    (S1 α C (meaning xs xr) .target).real {.redundant} <
      (S1 α C (meaning xs xr') .target).real {.redundant} ↔ xr < xr' := by
  rw [redundant_eq_sigmoid hα hs0 hs1.le hr0 hr1, redundant_eq_sigmoid hα hs0 hs1.le hr0' hr1',
    Real.sigmoid_lt_iff, mul_lt_mul_iff_right₀ hα, sub_lt_sub_iff_right,
    Real.log_lt_log_iff (gain_pos hs0 hs1.le hr0 hr1) (gain_pos hs0 hs1.le hr0' hr1'),
    gain_lt_gain_iff two_pos hs0 hs1 hr0 hr1 hr0' hr1']

theorem redundant_swap_lt_iff {x₁ x₂ : ℝ} (hα : 0 < α) (h₁0 : 0 < x₁) (h₁1 : x₁ ≤ 1)
    (h₂0 : 0 < x₂) (h₂1 : x₂ ≤ 1) :
    (S1 α C (meaning x₂ x₁) .target).real {.redundant} <
      (S1 α C (meaning x₁ x₂) .target).real {.redundant} ↔ x₁ < x₂ := by
  rw [redundant_eq_sigmoid hα h₂0 h₂1 h₁0 h₁1, redundant_eq_sigmoid hα h₁0 h₁1 h₂0 h₂1,
    Real.sigmoid_lt_iff, mul_lt_mul_iff_right₀ hα, sub_lt_sub_iff_right,
    Real.log_lt_log_iff (gain_pos h₂0 h₂1 h₁0 h₁1) (gain_pos h₁0 h₁1 h₂0 h₂1),
    gain_swap_lt_iff two_pos h₁0 h₁1 h₂0 h₂1]

end Model

/-! ### The hypothesis

The semantic value of an adjective is a strictly decreasing function `x` of the difficulty of
verifying its property, with values strictly between zero and one. -/

section Hypothesis

variable {D : Type*} [LinearOrder D] {x : D → ℝ} {α : ℝ} {C : Utterance → ℝ}

/-- Of two properties that trade the sufficient and the redundant role, the harder to verify is
mentioned redundantly less. -/
theorem harder_property_less_redundant (hx : StrictAnti x) (hx01 : ∀ d, x d ∈ Set.Ioo 0 1)
    (hα : 0 < α) (d d' : D) :
    (S1 α C (meaning (x d) (x d')) .target).real {.redundant} <
      (S1 α C (meaning (x d') (x d)) .target).real {.redundant} ↔ d < d' :=
  (redundant_swap_lt_iff hα (hx01 d').1 (hx01 d').2.le (hx01 d).1 (hx01 d).2.le).trans
    hx.lt_iff_gt

/-- Beside one sufficient property, the harder of two redundant properties is mentioned
redundantly less. This is the strong version of the hypothesis, on which difficulty predicts
redundancy within a property type. -/
theorem harder_item_less_redundant (hx : StrictAnti x) (hx01 : ∀ d, x d ∈ Set.Ioo 0 1)
    (hα : 0 < α) (s d d' : D) :
    (S1 α C (meaning (x s) (x d')) .target).real {.redundant} <
      (S1 α C (meaning (x s) (x d)) .target).real {.redundant} ↔ d < d' :=
  (redundant_lt_iff hα (hx01 s).1 (hx01 s).2 (hx01 d').1 (hx01 d').2.le (hx01 d).1
    (hx01 d).2.le).trans hx.lt_iff_gt

end Hypothesis

/-! ### The findings -/

/-- Material was harder to verify than colour. In both norming experiments it raised the error
rate and the response time. -/
theorem material_harder (e : Norming) (m : DifficultyMeasure) :
    0 < (verification e m).beta.toRat ∧
      (verification e m).p.Significant (1 / 20) := by
  revert e m; decide +kernel

/-- Colour was mentioned redundantly more often than material. -/
theorem color_more_redundant :
    0 < (redundantUse .redundantProperty).beta.toRat ∧
      (redundantUse .redundantProperty).p.Significant (1 / 20) := by
  decide +kernel

/-- No measure of difficulty within a property type predicted redundant mention, so the strong
version of the hypothesis found no support. -/
theorem no_within_property_effect :
    ∀ r ∈ [Predictor.difficulty, .interaction, .logRatio],
      ¬ (redundantUse r).p.Significant (1 / 20) := by
  decide +kernel

end KursatDegen2021
