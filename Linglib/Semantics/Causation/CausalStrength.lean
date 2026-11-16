module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
public import Linglib.Core.Probability.Independence.Basic
public import Linglib.Core.Probability.Independence.Pi

/-!
# Actual causal strength

Icard, Kominsky and Knobe measure how strongly a cause brought about an outcome by its
[score](##CausalStrength.score), its [sufficiency](##CausalStrength.sufficiency) weighted by the
probability of the cause plus its [necessity](##CausalStrength.necessity) weighted by the
probability of its absence. Worlds are draws `ι → Bool` of binary variables under a probability
measure, and a [cause](##CausalStrength.cause) is a set of variables showing the draws of an actual
round, as Konuk, Quillien and Mascarenhas extend the measure to plural causes. Under a product
measure a single cause [scores](##CausalStrength.score_singleton) its probability times its
sufficiency, plus its absence's probability when flipping it removes the outcome.

## Implementation notes

The three quantities are real numbers, mathlib's `Measure.real` of a conditional probability, since
the sources state them by equations and inequalities between probabilities.

## References

* [icard-et-al-2017]
* [konuk-et-al-2026]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalStrength

section Defs

variable {ι : Type*} {w₀ w : ι → Bool} {S T : Finset ι}

/-- The plural cause `S` in the actual round `w₀` is the event that every urn of `S` shows its
actual draw. -/
def cause (w₀ : ι → Bool) (S : Finset ι) : Set (ι → Bool) := (S : Set ι).pi fun i ↦ {w₀ i}

theorem mem_cause : w ∈ cause w₀ S ↔ ∀ i ∈ S, w i = w₀ i := by simp [cause]

instance : DecidablePred (· ∈ cause w₀ S) := fun _ ↦ decidable_of_iff _ mem_cause.symm

/-- A plurality of causes is a stronger event than any part of it. -/
theorem cause_subset_cause (h : S ⊆ T) : cause w₀ T ⊆ cause w₀ S :=
  fun _ hw ↦ mem_cause.2 fun i hi ↦ mem_cause.1 hw i (h hi)

theorem dependsOn_cause : DependsOn (· ∈ cause w₀ S) S := by
  intro w w' h
  simp only [mem_cause, eq_iff_iff]
  exact forall₂_congr fun i hi ↦ by rw [h i hi]

theorem dependsOn_compl_cause : DependsOn (· ∈ (cause w₀ S)ᶜ) S := fun _ _ h ↦ by
  simp only [mem_compl_iff, dependsOn_cause h]

variable [DecidableEq ι]

theorem cause_inter_cause_sdiff (h : S ⊆ T) : cause w₀ S ∩ cause w₀ (T \ S) = cause w₀ T := by
  ext w
  simp only [mem_inter_iff, mem_cause, Finset.mem_sdiff]
  exact ⟨fun ⟨h₁, h₂⟩ i hi ↦ if hiS : i ∈ S then h₁ i hiS else h₂ i ⟨hi, hiS⟩,
    fun hw ↦ ⟨fun i hi ↦ hw i (h hi), fun i hi ↦ hw i hi.1⟩⟩

omit [DecidableEq ι] in
theorem compl_cause_singleton (X : ι) : (cause w₀ {X})ᶜ = cause (fun _ ↦ !w₀ X) {X} := by
  ext w; simp only [mem_compl_iff, mem_cause, Finset.mem_singleton, forall_eq]
  cases w X <;> cases w₀ X <;> simp

theorem piecewise_mem_cause : S.piecewise w w₀ ∈ cause w₀ T ↔ w ∈ cause w₀ (S ∩ T) := by
  simp only [mem_cause, Finset.mem_inter]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : i ∈ S <;> simp [hi]

theorem piecewise_self_mem_cause : S.piecewise w₀ w ∈ cause w₀ T ↔ w ∈ cause w₀ (T \ S) := by
  simp only [mem_cause, Finset.mem_sdiff]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : i ∈ S <;> simp [hi]

variable [Fintype ι] {μ : Measure (ι → Bool)} {E : Set (ι → Bool)}

/-- The necessity of the plural cause `S` for the outcome `E` is the probability that the outcome
fails when the urns of `S` are redrawn from `μ`, short of all showing their actual draws, and every
other urn keeps its actual draw. -/
noncomputable def necessity (μ : Measure (ι → Bool)) (w₀ : ι → Bool) (E : Set (ι → Bool))
    (S : Finset ι) : ℝ :=
  μ[|(cause w₀ S)ᶜ].real {w | S.piecewise w w₀ ∉ E}

/-- The sufficiency of the plural cause `S` for the outcome `E` is the probability, over the
worlds of `μ` where neither the cause nor the outcome holds, that forcing the cause on produces the
outcome. -/
noncomputable def sufficiency (μ : Measure (ι → Bool)) (w₀ : ι → Bool) (E : Set (ι → Bool))
    (S : Finset ι) : ℝ :=
  μ[|(cause w₀ S)ᶜ ∩ Eᶜ].real {w | S.piecewise w₀ w ∈ E}

/-- The score of the plural cause `S` for the outcome `E` weights its sufficiency by its
probability and its necessity by the probability of its absence. -/
noncomputable def score (μ : Measure (ι → Bool)) (w₀ : ι → Bool) (E : Set (ι → Bool))
    (S : Finset ι) : ℝ :=
  μ.real (cause w₀ S) * sufficiency μ w₀ E S + μ.real (cause w₀ S)ᶜ * necessity μ w₀ E S

omit [Fintype ι] in
theorem necessity_nonneg : 0 ≤ necessity μ w₀ E S := measureReal_nonneg

omit [Fintype ι] in
theorem sufficiency_nonneg : 0 ≤ sufficiency μ w₀ E S := measureReal_nonneg

omit [Fintype ι] in
theorem necessity_le_one : necessity μ w₀ E S ≤ 1 := measureReal_le_one

omit [Fintype ι] in
theorem sufficiency_le_one : sufficiency μ w₀ E S ≤ 1 := measureReal_le_one

omit [Fintype ι] in
theorem necessity_eq_zero (h : ∀ w, S.piecewise w w₀ ∈ E) : necessity μ w₀ E S = 0 := by
  simp [necessity, h]

theorem necessity_eq_one [IsFiniteMeasure μ] (h : ∀ w ∉ cause w₀ S, S.piecewise w w₀ ∉ E)
    (hc : μ (cause w₀ S)ᶜ ≠ 0) : necessity μ w₀ E S = 1 := by
  have : (cause w₀ S)ᶜ ∩ {w | S.piecewise w w₀ ∉ E} = (cause w₀ S)ᶜ :=
    inter_eq_left.2 fun w hw ↦ h w hw
  rw [necessity, measureReal_def, cond_apply .of_discrete, this,
    ENNReal.inv_mul_cancel hc (measure_ne_top _ _), ENNReal.toReal_one]

omit [Fintype ι] in
theorem sufficiency_eq_one [IsFiniteMeasure μ] (h : ∀ w, S.piecewise w₀ w ∈ E)
    (hc : μ ((cause w₀ S)ᶜ ∩ Eᶜ) ≠ 0) : sufficiency μ w₀ E S = 1 := by
  have := cond_isProbabilityMeasure (μ := μ) hc
  simp [sufficiency, h]

theorem mul_necessity [IsFiniteMeasure μ] :
    μ.real (cause w₀ S)ᶜ * necessity μ w₀ E S =
      μ.real ((cause w₀ S)ᶜ ∩ {w | S.piecewise w w₀ ∉ E}) := by
  rw [necessity, measureReal_def, measureReal_def, ← ENNReal.toReal_mul, mul_comm,
    cond_mul_eq_inter .of_discrete _ μ, measureReal_def]

omit [Fintype ι] in
theorem score_nonneg : 0 ≤ score μ w₀ E S :=
  add_nonneg (mul_nonneg measureReal_nonneg sufficiency_nonneg)
    (mul_nonneg measureReal_nonneg necessity_nonneg)

theorem score_le_one [IsProbabilityMeasure μ] : score μ w₀ E S ≤ 1 := by
  have h := probReal_compl_eq_one_sub (μ := μ) (s := cause w₀ S) .of_discrete
  have h₁ := mul_le_of_le_one_right (measureReal_nonneg (μ := μ) (s := cause w₀ S))
    (sufficiency_le_one (μ := μ) (w₀ := w₀) (E := E) (S := S))
  have h₂ := mul_le_of_le_one_right (measureReal_nonneg (μ := μ) (s := (cause w₀ S)ᶜ))
    (necessity_le_one (μ := μ) (w₀ := w₀) (E := E) (S := S))
  rw [score]
  linarith

theorem score_eq_one [IsProbabilityMeasure μ] (hsuf : ∀ w, S.piecewise w₀ w ∈ E)
    (hnec : ∀ w ∉ cause w₀ S, S.piecewise w w₀ ∉ E) (hc : μ ((cause w₀ S)ᶜ ∩ Eᶜ) ≠ 0) :
    score μ w₀ E S = 1 := by
  have hc' : μ (cause w₀ S)ᶜ ≠ 0 := fun h ↦ hc (measure_mono_null inter_subset_left h)
  rw [score, sufficiency_eq_one hsuf hc, necessity_eq_one hnec hc', mul_one, mul_one,
    probReal_compl_eq_one_sub .of_discrete, add_sub_cancel]

theorem necessity_singleton [IsFiniteMeasure μ] [DecidablePred (· ∈ E)] {X : ι}
    (hc : μ (cause w₀ {X})ᶜ ≠ 0) :
    necessity μ w₀ E {X} = if Function.update w₀ X (!w₀ X) ∈ E then 0 else 1 := by
  have key : ∀ w ∉ cause w₀ {X},
      ({X} : Finset ι).piecewise w w₀ = Function.update w₀ X (!w₀ X) := fun w hw ↦ by
    rw [Finset.piecewise_singleton]
    congr 1
    cases h : w X <;> cases h₀ : w₀ X <;> simp_all [mem_cause]
  split_ifs with h
  · have : (cause w₀ {X})ᶜ ∩ {w | ({X} : Finset ι).piecewise w w₀ ∉ E} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun w ⟨hw, hn⟩ ↦ hn (by rw [key w hw]; exact h)
    rw [necessity, measureReal_def, cond_apply .of_discrete, this, measure_empty, mul_zero,
      ENNReal.toReal_zero]
  · exact necessity_eq_one (fun w hw ↦ by rw [key w hw]; exact h) hc

end Defs

section Product

variable {ι : Type*} [Fintype ι] {ν : ι → Measure Bool} [∀ i, IsProbabilityMeasure (ν i)]
  {w₀ v : ι → Bool} {S T : Finset ι} {E : Set (ι → Bool)}

theorem measure_pi_cause : Measure.pi ν (cause v S) = ∏ i ∈ S, ν i {v i} :=
  Measure.pi_pi_finset _ _ _

theorem measureReal_pi_cause : (Measure.pi ν).real (cause v S) = ∏ i ∈ S, (ν i).real {v i} := by
  rw [measureReal_def, measure_pi_cause, ENNReal.toReal_prod]; rfl

theorem measure_pi_compl_cause_singleton (X : ι) :
    Measure.pi ν (cause v {X})ᶜ = ν X {!v X} := by
  rw [compl_cause_singleton, measure_pi_cause, Finset.prod_singleton]

variable [DecidableEq ι]

theorem indepSet_pi_cause_singleton {X : ι} {B : Set (ι → Bool)}
    (hB : ∀ w b, Function.update w X b ∈ B ↔ w ∈ B) :
    IndepSet (cause v {X}) B (Measure.pi ν) := by
  refine indepSet_pi_of_dependsOn (T := {X}ᶜ) dependsOn_cause (fun w w' h ↦ ?_)
    (Finset.disjoint_singleton_left.2 (by simp))
  have : w' = Function.update w X (w' X) := by
    funext i
    by_cases hi : i = X
    · subst hi; simp
    · rw [Function.update_of_ne hi]; exact (h i (by simpa using hi)).symm
  show (w ∈ B) = (w' ∈ B)
  rw [this]
  exact propext (hB w _).symm

theorem measure_pi_cause_singleton_inter {X : ι} {B : Set (ι → Bool)}
    (hB : ∀ w b, Function.update w X b ∈ B ↔ w ∈ B) :
    Measure.pi ν (cause v {X} ∩ B) = ν X {v X} * Measure.pi ν B := by
  rw [(indepSet_pi_cause_singleton hB).measure_inter_eq_mul, measure_pi_cause,
    Finset.prod_singleton]

omit [Fintype ι] in
theorem update_mem_cause_iff {X : ι} (hX : X ∉ S) (w : ι → Bool) (b : Bool) :
    Function.update w X b ∈ cause v S ↔ w ∈ cause v S := by
  simp only [mem_cause]
  exact forall₂_congr fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hX)]

theorem sufficiency_singleton {X : ι} (hX : ν X {!w₀ X} ≠ 0) :
    sufficiency (Measure.pi ν) w₀ E {X} =
      (Measure.pi ν).real
          ((Function.update · X (w₀ X)) ⁻¹' E \ (Function.update · X (!w₀ X)) ⁻¹' E) /
        (Measure.pi ν).real ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ := by
  have h₁ : cause (fun _ ↦ !w₀ X) {X} ∩ Eᶜ =
      cause (fun _ ↦ !w₀ X) {X} ∩ ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ := by
    ext w
    simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_cause, Finset.mem_singleton,
      forall_eq]
    exact and_congr_right fun h ↦ by rw [← h, Function.update_eq_self]
  have h₂ : {w | ({X} : Finset ι).piecewise w₀ w ∈ E} = (Function.update · X (w₀ X)) ⁻¹' E := by
    ext w; simp [Finset.piecewise_singleton]
  have hden : Measure.pi ν (cause (fun _ ↦ !w₀ X) {X} ∩ ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ) =
      ν X {!w₀ X} * Measure.pi ν ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ :=
    measure_pi_cause_singleton_inter fun w b ↦ by simp
  have hnum : Measure.pi ν (cause (fun _ ↦ !w₀ X) {X} ∩ ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ ∩
      (Function.update · X (w₀ X)) ⁻¹' E) = ν X {!w₀ X} * Measure.pi ν
        ((Function.update · X (w₀ X)) ⁻¹' E \ (Function.update · X (!w₀ X)) ⁻¹' E) := by
    rw [inter_assoc, inter_comm _ (_ ⁻¹' E), ← sdiff_eq]
    exact measure_pi_cause_singleton_inter fun w b ↦ by simp
  rw [sufficiency, measureReal_def, compl_cause_singleton, h₁, cond_apply .of_discrete, h₂, hnum,
    hden, ← ENNReal.div_eq_inv_mul, ENNReal.mul_div_mul_left _ _ hX (measure_ne_top _ _),
    ENNReal.toReal_div, measureReal_def, measureReal_def]

/-- The score of a single cause is its probability times its sufficiency, plus the probability of
its absence when flipping it in the actual round removes the outcome. -/
theorem score_singleton [DecidablePred (· ∈ E)] {X : ι} (hX : ν X {!w₀ X} ≠ 0) :
    score (Measure.pi ν) w₀ E {X} = (ν X).real {w₀ X} * sufficiency (Measure.pi ν) w₀ E {X} +
      if Function.update w₀ X (!w₀ X) ∈ E then 0 else (ν X).real {!w₀ X} := by
  rw [score, necessity_singleton (measure_pi_compl_cause_singleton (ν := ν) X ▸ hX),
    measureReal_pi_cause, Finset.prod_singleton, measureReal_def (s := (cause w₀ {X})ᶜ),
    measure_pi_compl_cause_singleton, ← measureReal_def]
  split_ifs <;> simp

/-- When the outcome is that the urns `T` all show their actual draws, the score of a part `S` of
`T` is the probability that `S` is absent plus the probability of the outcome. -/
theorem score_pi_cause (hST : S ⊆ T) (hc : Measure.pi ν (cause w₀ S)ᶜ ≠ 0) :
    score (Measure.pi ν) w₀ (cause w₀ T) S =
      (Measure.pi ν).real (cause w₀ S)ᶜ + (Measure.pi ν).real (cause w₀ T) := by
  have hnec : (cause w₀ S)ᶜ ∩ {w | S.piecewise w w₀ ∉ cause w₀ T} = (cause w₀ S)ᶜ :=
    inter_eq_left.2 fun w hw ↦ by
      rw [mem_ofPred_eq, piecewise_mem_cause, Finset.inter_eq_left.2 hST]; exact hw
  have hsuf : {w | S.piecewise w₀ w ∈ cause w₀ T} = cause w₀ (T \ S) := by
    ext w; exact piecewise_self_mem_cause
  have hcond : (cause w₀ S)ᶜ ∩ (cause w₀ T)ᶜ = (cause w₀ S)ᶜ :=
    inter_eq_left.2 (compl_subset_compl.2 (cause_subset_cause hST))
  rw [score, mul_necessity, hnec, sufficiency, hcond, hsuf,
    (indepSet_pi_of_dependsOn dependsOn_compl_cause dependsOn_cause
      Finset.disjoint_sdiff).cond_real_apply .of_discrete hc,
    ← (indepSet_pi_of_dependsOn dependsOn_cause dependsOn_cause
      Finset.disjoint_sdiff).measureReal_inter_eq_mul, cause_inter_cause_sdiff hST, add_comm]

theorem score_pi_cause_lt_iff {S' : Finset ι} (hS : S ⊆ T) (hS' : S' ⊆ T)
    (hc : Measure.pi ν (cause w₀ S)ᶜ ≠ 0) (hc' : Measure.pi ν (cause w₀ S')ᶜ ≠ 0) :
    score (Measure.pi ν) w₀ (cause w₀ T) S < score (Measure.pi ν) w₀ (cause w₀ T) S' ↔
      (Measure.pi ν).real (cause w₀ S') < (Measure.pi ν).real (cause w₀ S) := by
  rw [score_pi_cause hS hc, score_pi_cause hS' hc', probReal_compl_eq_one_sub .of_discrete,
    probReal_compl_eq_one_sub .of_discrete]
  constructor <;> intro h <;> linarith

end Product

end CausalStrength
