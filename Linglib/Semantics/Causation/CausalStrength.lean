module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
public import Linglib.Core.Probability.Independence.Basic
public import Linglib.Core.Probability.Independence.Pi

/-!
# Actual causal strength

Icard, Kominsky and Knobe measure how strongly a cause brought about an outcome by its
[score](##causalStrength), its [sufficiency](##sufficiencyStrength) weighted by the
probability of the cause plus its [necessity](##necessityStrength) weighted by the
probability of its absence. Worlds are draws `ι → Bool` of binary variables under a probability
measure, and a [cause](##pluralCause) is a set of variables showing the draws of an actual
round, as Konuk, Quillien and Mascarenhas extend the measure to plural causes. Under a product
measure a single cause [scores](##causalStrength_singleton) its probability times its
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

section Defs

variable {ι : Type*} {w₀ w : ι → Bool} {S T : Finset ι}

/-- The plural cause `S` in the actual round `w₀` is the event that every urn of `S` shows its
actual draw. -/
def pluralCause (w₀ : ι → Bool) (S : Finset ι) : Set (ι → Bool) := (S : Set ι).pi fun i ↦ {w₀ i}

theorem mem_pluralCause : w ∈ pluralCause w₀ S ↔ ∀ i ∈ S, w i = w₀ i := by simp [pluralCause]

instance : DecidablePred (· ∈ pluralCause w₀ S) := fun _ ↦ decidable_of_iff _ mem_pluralCause.symm

/-- A plurality of causes is a stronger event than any part of it. -/
theorem pluralCause_subset_pluralCause (h : S ⊆ T) : pluralCause w₀ T ⊆ pluralCause w₀ S :=
  fun _ hw ↦ mem_pluralCause.2 fun i hi ↦ mem_pluralCause.1 hw i (h hi)

theorem dependsOn_pluralCause : DependsOn (· ∈ pluralCause w₀ S) S := by
  intro w w' h
  simp only [mem_pluralCause, eq_iff_iff]
  exact forall₂_congr fun i hi ↦ by rw [h i hi]

theorem dependsOn_compl_pluralCause : DependsOn (· ∈ (pluralCause w₀ S)ᶜ) S := fun _ _ h ↦ by
  simp only [mem_compl_iff, dependsOn_pluralCause h]

variable [DecidableEq ι]

theorem pluralCause_inter_pluralCause_sdiff (h : S ⊆ T) : pluralCause w₀ S ∩
    pluralCause w₀ (T \ S) = pluralCause w₀ T := by
  ext w
  simp only [mem_inter_iff, mem_pluralCause, Finset.mem_sdiff]
  exact ⟨fun ⟨h₁, h₂⟩ i hi ↦ if hiS : i ∈ S then h₁ i hiS else h₂ i ⟨hi, hiS⟩,
    fun hw ↦ ⟨fun i hi ↦ hw i (h hi), fun i hi ↦ hw i hi.1⟩⟩

omit [DecidableEq ι] in
theorem compl_pluralCause_singleton (X : ι) : (pluralCause w₀ {X})ᶜ =
    pluralCause (fun _ ↦ !w₀ X) {X} := by
  ext w; simp only [mem_compl_iff, mem_pluralCause, Finset.mem_singleton, forall_eq]
  cases w X <;> cases w₀ X <;> simp

theorem piecewise_mem_pluralCause : S.piecewise w w₀ ∈ pluralCause w₀ T ↔
    w ∈ pluralCause w₀ (S ∩ T) := by
  simp only [mem_pluralCause, Finset.mem_inter]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : i ∈ S <;> simp [hi]

theorem piecewise_self_mem_pluralCause : S.piecewise w₀ w ∈ pluralCause w₀ T ↔
    w ∈ pluralCause w₀ (T \ S) := by
  simp only [mem_pluralCause, Finset.mem_sdiff]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : i ∈ S <;> simp [hi]

variable [Fintype ι] {μ : Measure (ι → Bool)} {E : Set (ι → Bool)}

/-- The necessity of the plural cause `S` for the outcome `E` is the probability that the outcome
fails when the urns of `S` are redrawn from `μ`, short of all showing their actual draws, and every
other urn keeps its actual draw. -/
noncomputable def necessityStrength (μ : Measure (ι → Bool)) (w₀ : ι → Bool) (E : Set (ι → Bool))
    (S : Finset ι) : ℝ :=
  μ[|(pluralCause w₀ S)ᶜ].real {w | S.piecewise w w₀ ∉ E}

/-- The sufficiency of the plural cause `S` for the outcome `E` is the probability, over the
worlds of `μ` where neither the cause nor the outcome holds, that forcing the cause on produces the
outcome. -/
noncomputable def sufficiencyStrength (μ : Measure (ι → Bool)) (w₀ : ι → Bool) (E : Set (ι → Bool))
    (S : Finset ι) : ℝ :=
  μ[|(pluralCause w₀ S)ᶜ ∩ Eᶜ].real {w | S.piecewise w₀ w ∈ E}

/-- The score of the plural cause `S` for the outcome `E` weights its sufficiency by its
probability and its necessity by the probability of its absence. -/
noncomputable def causalStrength (μ : Measure (ι → Bool)) (w₀ : ι → Bool) (E : Set (ι → Bool))
    (S : Finset ι) : ℝ :=
  μ.real (pluralCause w₀ S) * sufficiencyStrength μ w₀ E S + μ.real (pluralCause w₀ S)ᶜ *
  necessityStrength μ w₀ E S

omit [Fintype ι] in
theorem necessityStrength_nonneg : 0 ≤ necessityStrength μ w₀ E S := measureReal_nonneg

omit [Fintype ι] in
theorem sufficiencyStrength_nonneg : 0 ≤ sufficiencyStrength μ w₀ E S := measureReal_nonneg

omit [Fintype ι] in
theorem necessityStrength_le_one : necessityStrength μ w₀ E S ≤ 1 := measureReal_le_one

omit [Fintype ι] in
theorem sufficiencyStrength_le_one : sufficiencyStrength μ w₀ E S ≤ 1 := measureReal_le_one

omit [Fintype ι] in
theorem necessityStrength_eq_zero (h : ∀ w,
    S.piecewise w w₀ ∈ E) : necessityStrength μ w₀ E S = 0 := by
  simp [necessityStrength, h]

theorem necessityStrength_eq_one [IsFiniteMeasure μ] (h : ∀ w ∉ pluralCause w₀ S,
    S.piecewise w w₀ ∉ E)
    (hc : μ (pluralCause w₀ S)ᶜ ≠ 0) : necessityStrength μ w₀ E S = 1 := by
  have : (pluralCause w₀ S)ᶜ ∩ {w | S.piecewise w w₀ ∉ E} = (pluralCause w₀ S)ᶜ :=
    inter_eq_left.2 fun w hw ↦ h w hw
  rw [necessityStrength, measureReal_def, cond_apply .of_discrete, this,
    ENNReal.inv_mul_cancel hc (measure_ne_top _ _), ENNReal.toReal_one]

omit [Fintype ι] in
theorem sufficiencyStrength_eq_one [IsFiniteMeasure μ] (h : ∀ w, S.piecewise w₀ w ∈ E)
    (hc : μ ((pluralCause w₀ S)ᶜ ∩ Eᶜ) ≠ 0) : sufficiencyStrength μ w₀ E S = 1 := by
  have := cond_isProbabilityMeasure (μ := μ) hc
  simp [sufficiencyStrength, h]

theorem mul_necessityStrength [IsFiniteMeasure μ] :
    μ.real (pluralCause w₀ S)ᶜ * necessityStrength μ w₀ E S =
      μ.real ((pluralCause w₀ S)ᶜ ∩ {w | S.piecewise w w₀ ∉ E}) := by
  rw [necessityStrength, measureReal_def, measureReal_def, ← ENNReal.toReal_mul, mul_comm,
    cond_mul_eq_inter .of_discrete _ μ, measureReal_def]

omit [Fintype ι] in
theorem causalStrength_nonneg : 0 ≤ causalStrength μ w₀ E S :=
  add_nonneg (mul_nonneg measureReal_nonneg sufficiencyStrength_nonneg)
    (mul_nonneg measureReal_nonneg necessityStrength_nonneg)

theorem causalStrength_le_one [IsProbabilityMeasure μ] : causalStrength μ w₀ E S ≤ 1 := by
  have h := probReal_compl_eq_one_sub (μ := μ) (s := pluralCause w₀ S) .of_discrete
  have h₁ := mul_le_of_le_one_right (measureReal_nonneg (μ := μ) (s := pluralCause w₀ S))
    (sufficiencyStrength_le_one (μ := μ) (w₀ := w₀) (E := E) (S := S))
  have h₂ := mul_le_of_le_one_right (measureReal_nonneg (μ := μ) (s := (pluralCause w₀ S)ᶜ))
    (necessityStrength_le_one (μ := μ) (w₀ := w₀) (E := E) (S := S))
  rw [causalStrength]
  linarith

theorem causalStrength_eq_one [IsProbabilityMeasure μ] (hsuf : ∀ w, S.piecewise w₀ w ∈ E)
    (hnec : ∀ w ∉ pluralCause w₀ S, S.piecewise w w₀ ∉ E) (hc : μ ((pluralCause w₀ S)ᶜ ∩ Eᶜ) ≠ 0) :
    causalStrength μ w₀ E S = 1 := by
  have hc' : μ (pluralCause w₀ S)ᶜ ≠ 0 := fun h ↦ hc (measure_mono_null inter_subset_left h)
  rw [causalStrength, sufficiencyStrength_eq_one hsuf hc,
      necessityStrength_eq_one hnec hc', mul_one, mul_one,
    probReal_compl_eq_one_sub .of_discrete, add_sub_cancel]

theorem necessityStrength_singleton [IsFiniteMeasure μ] [DecidablePred (· ∈ E)] {X : ι}
    (hc : μ (pluralCause w₀ {X})ᶜ ≠ 0) :
    necessityStrength μ w₀ E {X} = if Function.update w₀ X (!w₀ X) ∈ E then 0 else 1 := by
  have key : ∀ w ∉ pluralCause w₀ {X},
      ({X} : Finset ι).piecewise w w₀ = Function.update w₀ X (!w₀ X) := fun w hw ↦ by
    rw [Finset.piecewise_singleton]
    congr 1
    cases h : w X <;> cases h₀ : w₀ X <;> simp_all [mem_pluralCause]
  split_ifs with h
  · have : (pluralCause w₀ {X})ᶜ ∩ {w | ({X} : Finset ι).piecewise w w₀ ∉ E} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun w ⟨hw, hn⟩ ↦ hn (by rw [key w hw]; exact h)
    rw [necessityStrength, measureReal_def, cond_apply .of_discrete, this, measure_empty, mul_zero,
      ENNReal.toReal_zero]
  · exact necessityStrength_eq_one (fun w hw ↦ by rw [key w hw]; exact h) hc

end Defs

section Product

variable {ι : Type*} [Fintype ι] {ν : ι → Measure Bool} [∀ i, IsProbabilityMeasure (ν i)]
  {w₀ v : ι → Bool} {S T : Finset ι} {E : Set (ι → Bool)}

theorem measure_pi_pluralCause : Measure.pi ν (pluralCause v S) = ∏ i ∈ S, ν i {v i} :=
  Measure.pi_pi_finset _ _ _

theorem measureReal_pi_pluralCause : (Measure.pi ν).real (pluralCause v S) =
    ∏ i ∈ S, (ν i).real {v i} := by
  rw [measureReal_def, measure_pi_pluralCause, ENNReal.toReal_prod]; rfl

theorem measure_pi_compl_pluralCause_singleton (X : ι) :
    Measure.pi ν (pluralCause v {X})ᶜ = ν X {!v X} := by
  rw [compl_pluralCause_singleton, measure_pi_pluralCause, Finset.prod_singleton]

variable [DecidableEq ι]

theorem indepSet_pi_pluralCause_singleton {X : ι} {B : Set (ι → Bool)}
    (hB : ∀ w b, Function.update w X b ∈ B ↔ w ∈ B) :
    IndepSet (pluralCause v {X}) B (Measure.pi ν) := by
  refine indepSet_pi_of_dependsOn (T := {X}ᶜ) dependsOn_pluralCause (fun w w' h ↦ ?_)
    (Finset.disjoint_singleton_left.2 (by simp))
  have : w' = Function.update w X (w' X) := by
    funext i
    by_cases hi : i = X
    · subst hi; simp
    · rw [Function.update_of_ne hi]; exact (h i (by simpa using hi)).symm
  show (w ∈ B) = (w' ∈ B)
  rw [this]
  exact propext (hB w _).symm

theorem measure_pi_pluralCause_singleton_inter {X : ι} {B : Set (ι → Bool)}
    (hB : ∀ w b, Function.update w X b ∈ B ↔ w ∈ B) :
    Measure.pi ν (pluralCause v {X} ∩ B) = ν X {v X} * Measure.pi ν B := by
  rw [(indepSet_pi_pluralCause_singleton hB).measure_inter_eq_mul, measure_pi_pluralCause,
    Finset.prod_singleton]

omit [Fintype ι] in
theorem update_mem_pluralCause_iff {X : ι} (hX : X ∉ S) (w : ι → Bool) (b : Bool) :
    Function.update w X b ∈ pluralCause v S ↔ w ∈ pluralCause v S := by
  simp only [mem_pluralCause]
  exact forall₂_congr fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hX)]

theorem sufficiencyStrength_singleton {X : ι} (hX : ν X {!w₀ X} ≠ 0) :
    sufficiencyStrength (Measure.pi ν) w₀ E {X} =
      (Measure.pi ν).real
          ((Function.update · X (w₀ X)) ⁻¹' E \ (Function.update · X (!w₀ X)) ⁻¹' E) /
        (Measure.pi ν).real ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ := by
  have h₁ : pluralCause (fun _ ↦ !w₀ X) {X} ∩ Eᶜ =
      pluralCause (fun _ ↦ !w₀ X) {X} ∩ ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ := by
    ext w
    simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_pluralCause, Finset.mem_singleton,
      forall_eq]
    exact and_congr_right fun h ↦ by rw [← h, Function.update_eq_self]
  have h₂ : {w | ({X} : Finset ι).piecewise w₀ w ∈ E} = (Function.update · X (w₀ X)) ⁻¹' E := by
    ext w; simp [Finset.piecewise_singleton]
  have hden : Measure.pi ν
      (pluralCause (fun _ ↦ !w₀ X) {X} ∩ ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ) =
      ν X {!w₀ X} * Measure.pi ν ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ :=
    measure_pi_pluralCause_singleton_inter fun w b ↦ by simp
  have hnum : Measure.pi ν
      (pluralCause (fun _ ↦ !w₀ X) {X} ∩ ((Function.update · X (!w₀ X)) ⁻¹' E)ᶜ ∩
      (Function.update · X (w₀ X)) ⁻¹' E) = ν X {!w₀ X} * Measure.pi ν
        ((Function.update · X (w₀ X)) ⁻¹' E \ (Function.update · X (!w₀ X)) ⁻¹' E) := by
    rw [inter_assoc, inter_comm _ (_ ⁻¹' E), ← sdiff_eq]
    exact measure_pi_pluralCause_singleton_inter fun w b ↦ by simp
  rw [sufficiencyStrength, measureReal_def, compl_pluralCause_singleton, h₁,
      cond_apply .of_discrete, h₂, hnum,
    hden, ← ENNReal.div_eq_inv_mul, ENNReal.mul_div_mul_left _ _ hX (measure_ne_top _ _),
    ENNReal.toReal_div, measureReal_def, measureReal_def]

/-- The score of a single cause is its probability times its sufficiency, plus the probability of
its absence when flipping it in the actual round removes the outcome. -/
theorem causalStrength_singleton [DecidablePred (· ∈ E)] {X : ι} (hX : ν X {!w₀ X} ≠ 0) :
    causalStrength (Measure.pi ν) w₀ E {X} = (ν X).real {w₀ X} *
    sufficiencyStrength (Measure.pi ν) w₀ E {X} +
      if Function.update w₀ X (!w₀ X) ∈ E then 0 else (ν X).real {!w₀ X} := by
  rw [causalStrength, necessityStrength_singleton
      (measure_pi_compl_pluralCause_singleton (ν := ν) X ▸ hX),
    measureReal_pi_pluralCause, Finset.prod_singleton, measureReal_def (s := (pluralCause w₀ {X})ᶜ),
    measure_pi_compl_pluralCause_singleton, ← measureReal_def]
  split_ifs <;> simp

/-- When the outcome is that the urns `T` all show their actual draws, the score of a part `S` of
`T` is the probability that `S` is absent plus the probability of the outcome. -/
theorem causalStrength_pi_pluralCause (hST : S ⊆ T) (hc : Measure.pi ν (pluralCause w₀ S)ᶜ ≠ 0) :
    causalStrength (Measure.pi ν) w₀ (pluralCause w₀ T) S =
      (Measure.pi ν).real (pluralCause w₀ S)ᶜ + (Measure.pi ν).real (pluralCause w₀ T) := by
  have hnec : (pluralCause w₀ S)ᶜ ∩
      {w | S.piecewise w w₀ ∉ pluralCause w₀ T} = (pluralCause w₀ S)ᶜ :=
    inter_eq_left.2 fun w hw ↦ by
      rw [mem_ofPred_eq, piecewise_mem_pluralCause, Finset.inter_eq_left.2 hST]; exact hw
  have hsuf : {w | S.piecewise w₀ w ∈ pluralCause w₀ T} = pluralCause w₀ (T \ S) := by
    ext w; exact piecewise_self_mem_pluralCause
  have hcond : (pluralCause w₀ S)ᶜ ∩ (pluralCause w₀ T)ᶜ = (pluralCause w₀ S)ᶜ :=
    inter_eq_left.2 (compl_subset_compl.2 (pluralCause_subset_pluralCause hST))
  rw [causalStrength, mul_necessityStrength, hnec, sufficiencyStrength, hcond, hsuf,
    (indepSet_pi_of_dependsOn dependsOn_compl_pluralCause dependsOn_pluralCause
      Finset.disjoint_sdiff).cond_real_apply .of_discrete hc,
    ← (indepSet_pi_of_dependsOn dependsOn_pluralCause dependsOn_pluralCause
      Finset.disjoint_sdiff).measureReal_inter_eq_mul,
      pluralCause_inter_pluralCause_sdiff hST, add_comm]

theorem causalStrength_pi_pluralCause_lt_iff {S' : Finset ι} (hS : S ⊆ T) (hS' : S' ⊆ T)
    (hc : Measure.pi ν (pluralCause w₀ S)ᶜ ≠ 0) (hc' : Measure.pi ν (pluralCause w₀ S')ᶜ ≠ 0) :
    causalStrength (Measure.pi ν) w₀ (pluralCause w₀ T) S <
    causalStrength (Measure.pi ν) w₀ (pluralCause w₀ T) S' ↔
      (Measure.pi ν).real (pluralCause w₀ S') < (Measure.pi ν).real (pluralCause w₀ S) := by
  rw [causalStrength_pi_pluralCause hS hc, causalStrength_pi_pluralCause hS' hc',
      probReal_compl_eq_one_sub .of_discrete,
    probReal_compl_eq_one_sub .of_discrete]
  constructor <;> intro h <;> linarith

end Product
