module

public import Linglib.Data.Experiments.IcardEtAl2017
public import Linglib.Semantics.Causation.CausalStrength
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.StrongLaw

/-!
# Icard, Kominsky and Knobe (2017): Normality and actual causal strength

Icard, Kominsky and Knobe explain the influence of normality on judgments of actual causation by a
measure that weights a cause's sufficiency by its probability and its necessity by the probability
of its absence, the probabilities being sampling propensities that rise with normality. On the
collider C → E ← A, with E the conjunction or the disjunction of its causes, the measure is
`P(C) P(A) - P(C) + 1` or `P(C)`, so a less normal C counts as more causal when the causes are
conjoined and as less causal when they are disjoined. None of the measures in the literature
predicts the second effect, abnormal deflation, which the paper's two experiments find.

## Main statements

* `abnormal_inflation`, `supersession`, `no_supersession`, `abnormal_deflation`: the four effects
  of the measure on the collider (§3.2, §5, Table 5).
* `table1_conjunctive`, `table1_disjunctive`, `no_abnormal_deflation`: the values of SP, ΔP,
  power-PC and PNS on the collider (Table 1), none of which rises with P(C) when the causes are
  disjoined.
* `PNS_eq_deltaP`: under a product measure PNS is ΔP when the outcome is monotone in the cause
  (§3.3).
* `ae_tendsto_hits`: the sampling algorithm of §4.4 converges almost surely to the measure.

## Implementation notes

* Worlds are the draws of C and A under independent Bernoulli priors, the paper's sampling
  propensities, and each causal structure's effect is an event; the measure is the substrate's
  `CausalStrength.score` in the round C = A = E = 1.
* The paper names two candidates for sufficiency (§4.3); the substrate takes Cheng and Pearl's,
  conditioned on the absence of cause and effect, and `resampleSufficiency_eq_sufficiency` shows
  the other agrees on the collider. As `cond` of a null event is the zero measure, the theorems
  assume priors below one.
* Locators are sections, equations and tables of the accepted preprint.

## References

* [icard-et-al-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology unitInterval CausalStrength
open scoped ENNReal

namespace IcardEtAl2017

/-! ### The unshielded collider -/

/-- The collider has a focal cause `c` and an alternative cause `a` (§3.2). -/
inductive Cause | c | a
  deriving DecidableEq, Fintype

open Cause

/-- The prior draws each cause independently, `c` with probability `p c` and `a` with `p a`. -/
noncomputable abbrev prior (p : Cause → I) : Measure (Cause → Bool) :=
  Measure.pi fun i ↦ Ber(true, false, p i)

/-- The effect of a causal structure is the minimum of the two causes if they are conjoined and
their maximum if they are disjoined (§3.2). -/
def effect : CausalStructure → Set (Cause → Bool)
  | .conjunctive => {w | min (w c) (w a) = true}
  | .disjunctive => {w | max (w c) (w a) = true}

instance : ∀ s, DecidablePred (· ∈ effect s)
  | .conjunctive => fun w ↦ inferInstanceAs (Decidable (min (w c) (w a) = true))
  | .disjunctive => fun w ↦ inferInstanceAs (Decidable (max (w c) (w a) = true))

/-- `strength p s` is the actual causal strength of `C = 1` for `E = 1` when `C = A = E = 1`,
eq. (1). -/
noncomputable def strength (p : Cause → I) (s : CausalStructure) : ℝ≥0∞ :=
  score (prior p) (fun _ ↦ true) (effect s) {c}

variable {p p₁ p₂ : Cause → I} {s : CausalStructure}

theorem strength_ne_top : strength p s ≠ ∞ := score_ne_top

private theorem ber_real_true (q : I) : Ber(true, false, q).real {true} = q := by
  simp

private theorem ber_real_false (q : I) : Ber(true, false, q).real {false} = 1 - q := by
  simp

private theorem ber_true_ne_zero {q : I} (h : 0 < q) : Ber(true, false, q) {true} ≠ 0 :=
  (ENNReal.toReal_pos_iff.1 (by rw [← measureReal_def, ber_real_true]; exact h)).1.ne'

private theorem ber_false_ne_zero {q : I} (h : q < 1) : Ber(true, false, q) {false} ≠ 0 :=
  (ENNReal.toReal_pos_iff.1 (by
    rw [← measureReal_def, ber_real_false]; exact sub_pos.2 (show (q : ℝ) < 1 from h))).1.ne'

private theorem preimage_update_c (s : CausalStructure) (b : Bool) :
    (Function.update · c b) ⁻¹' effect s =
      match s, b with
      | .conjunctive, true => cause (fun _ ↦ true) {a}
      | .conjunctive, false => ∅
      | .disjunctive, true => univ
      | .disjunctive, false => cause (fun _ ↦ true) {a} := by
  cases s <;> cases b <;> ext w <;> simp [effect, mem_cause]

/-! ### Necessity, sufficiency and the measure (Table 2, eqs. (2) and (3)) -/

-- Table 2
theorem necessity_disjunctive (μ : Measure (Cause → Bool)) :
    necessity μ (fun _ ↦ true) (effect .disjunctive) {c} = 0 :=
  necessity_eq_zero (by decide)

-- Table 2
theorem necessity_conjunctive (hc : p c < 1) :
    necessity (prior p) (fun _ ↦ true) (effect .conjunctive) {c} = 1 :=
  necessity_eq_one (by decide)
    (by rw [measure_pi_compl_cause_singleton]; exact ber_false_ne_zero hc)

-- Table 2
theorem sufficiency_collider (hc : p c < 1) (ha : p a < 1) :
    sufficiency (prior p) (fun _ ↦ true) (effect .conjunctive) {c} = Ber(true, false, p a) {true} ∧
      sufficiency (prior p) (fun _ ↦ true) (effect .disjunctive) {c} = 1 := by
  have ha' : Measure.pi (fun i ↦ Ber(true, false, p i)) (cause (fun _ ↦ true) {a})ᶜ ≠ 0 := by
    rw [measure_pi_compl_cause_singleton]; exact ber_false_ne_zero ha
  rw [sufficiency_singleton (X := c) (by exact ber_false_ne_zero hc),
    sufficiency_singleton (X := c) (by exact ber_false_ne_zero hc)]
  simp only [Bool.not_true, preimage_update_c]
  refine ⟨by simp [measure_pi_cause], ?_⟩
  rw [← compl_eq_univ_sdiff, ENNReal.div_self ha' (measure_ne_top _ _)]

-- (3), (2)
theorem strength_collider (hc : p c < 1) (ha : p a < 1) :
    strength p .conjunctive = Ber(true, false, p c) {true} * Ber(true, false, p a) {true} +
        Ber(true, false, p c) {false} ∧
      strength p .disjunctive = Ber(true, false, p c) {true} := by
  obtain ⟨h₁, h₂⟩ := sufficiency_collider hc ha
  unfold strength at *
  rw [score_singleton (X := c) (by exact ber_false_ne_zero hc),
    score_singleton (X := c) (by exact ber_false_ne_zero hc), h₁, h₂]
  simp only [Bool.not_true]
  rw [ite_eq_right (show Function.update (fun _ : Cause ↦ true) c false ∉ effect .conjunctive
      by decide),
    ite_eq_left (show Function.update (fun _ : Cause ↦ true) c false ∈ effect .disjunctive
      by decide)]
  simp

private theorem strength_toReal (hc : p c < 1) (ha : p a < 1) :
    (strength p .conjunctive).toReal = p c * p a - p c + 1 ∧
      (strength p .disjunctive).toReal = p c := by
  obtain ⟨h₁, h₂⟩ := strength_collider hc ha
  rw [h₁, h₂, ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (measure_ne_top _ _), ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
    ← measureReal_def]
  simp only [ber_real_true, ber_real_false, and_true]
  ring

/-! ### The four effects (§3.2, §5, Table 5) -/

/-- When the causes are conjoined a less normal focal cause is more causal, provided `P(A) < 1`
(abnormal inflation). -/
theorem abnormal_inflation (h : p₂ c < p₁ c) (hc : p₁ c < 1) (ha : p₁ a = p₂ a) (ha' : p₁ a < 1) :
    strength p₁ .conjunctive < strength p₂ .conjunctive := by
  rw [← ENNReal.toReal_lt_toReal strength_ne_top strength_ne_top, (strength_toReal hc ha').1,
    (strength_toReal (h.trans hc) (ha ▸ ha')).1, ← ha]
  have : (p₂ c : ℝ) < p₁ c := h
  have : (p₁ a : ℝ) < 1 := ha'
  nlinarith

/-- When the causes are conjoined a less normal alternative makes the focal cause less causal,
provided `0 < P(C)` (supersession). -/
theorem supersession (h : p₂ a < p₁ a) (ha : p₁ a < 1) (hc : p₁ c = p₂ c) (hc₀ : 0 < p₁ c)
    (hc₁ : p₁ c < 1) : strength p₂ .conjunctive < strength p₁ .conjunctive := by
  rw [← ENNReal.toReal_lt_toReal strength_ne_top strength_ne_top, (strength_toReal hc₁ ha).1,
    (strength_toReal (hc ▸ hc₁) (h.trans ha)).1, ← hc]
  have : (p₂ a : ℝ) < p₁ a := h
  have : (0 : ℝ) < p₁ c := hc₀
  nlinarith

/-- When the causes are disjoined the alternative's normality does not affect the focal cause (no
supersession with disjunction). -/
theorem no_supersession (hc : p₁ c = p₂ c) (hc₁ : p₁ c < 1) (ha₁ : p₁ a < 1) (ha₂ : p₂ a < 1) :
    strength p₁ .disjunctive = strength p₂ .disjunctive := by
  rw [(strength_collider hc₁ ha₁).2, (strength_collider (hc ▸ hc₁) ha₂).2, hc]

/-- When the causes are disjoined a less normal focal cause is less causal (abnormal deflation,
§5). -/
theorem abnormal_deflation (h : p₂ c < p₁ c) (hc : p₁ c < 1) (ha₁ : p₁ a < 1) (ha₂ : p₂ a < 1) :
    strength p₂ .disjunctive < strength p₁ .disjunctive := by
  rw [← ENNReal.toReal_lt_toReal strength_ne_top strength_ne_top, (strength_toReal hc ha₁).2,
    (strength_toReal (h.trans hc) ha₂).2]
  exact h

/-! ### The other candidate for sufficiency (§4.3) -/

/-- The sufficiency that forces the cause on and redraws every other variable,
`P(E | do(C = 1))`. -/
noncomputable def resampleSufficiency {ι : Type*} [DecidableEq ι] (μ : Measure (ι → Bool))
    (w₀ : ι → Bool) (E : Set (ι → Bool)) (S : Finset ι) : ℝ≥0∞ :=
  μ {w | S.piecewise w₀ w ∈ E}

theorem resampleSufficiency_eq_sufficiency (s : CausalStructure) (hc : p c < 1) (ha : p a < 1) :
    resampleSufficiency (prior p) (fun _ ↦ true) (effect s) {c} =
      sufficiency (prior p) (fun _ ↦ true) (effect s) {c} := by
  have h (s : CausalStructure) : {w : Cause → Bool | ({c} : Finset Cause).piecewise
      (fun _ ↦ true) w ∈ effect s} = (Function.update · c true) ⁻¹' effect s := by
    ext w; simp [Finset.piecewise_singleton]
  obtain ⟨h₁, h₂⟩ := sufficiency_collider hc ha
  unfold resampleSufficiency
  cases s
  · rw [h₁, h, preimage_update_c, measure_pi_cause, Finset.prod_singleton]
  · rw [h₂, h, preimage_update_c, measure_univ]

/-! ### The measures in the literature (§3.3, Table 1) -/

section Measures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `SP` is how far the cause raises the probability of the effect over its unconditional
value. -/
noncomputable def SP (μ : Measure Ω) (C E : Set Ω) : ℝ := (μ[|C]).real E - μ.real E

/-- `ΔP` is the difference of the effect's probability with and without the cause. -/
noncomputable def deltaP (μ : Measure Ω) (C E : Set Ω) : ℝ := (μ[|C]).real E - (μ[|Cᶜ]).real E

/-- Cheng's power-PC divides `ΔP` by the probability that the effect fails without the cause. -/
noncomputable def powerPC (μ : Measure Ω) (C E : Set Ω) : ℝ := deltaP μ C E / (μ[|Cᶜ]).real Eᶜ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pearl's probability of necessity and sufficiency of `X` for `E` weights the probability that
removing the cause removes the outcome, where both hold, and the probability that adding the cause
produces the outcome, where neither holds, by the probabilities of the two cases. -/
noncomputable def PNS (μ : Measure (ι → Bool)) (X : ι) (E : Set (ι → Bool)) : ℝ :=
  μ.real (cause (fun _ ↦ true) {X} ∩ E) *
      (μ[|cause (fun _ ↦ true) {X} ∩ E]).real {w | Function.update w X false ∉ E} +
    μ.real (cause (fun _ ↦ false) {X} ∩ Eᶜ) *
      (μ[|cause (fun _ ↦ false) {X} ∩ Eᶜ]).real {w | Function.update w X true ∈ E}

variable {ν : ι → Measure Bool} [∀ i, IsProbabilityMeasure (ν i)] {X : ι} {E : Set (ι → Bool)}

private theorem cond_real_pi_cause_singleton {b : Bool} {B : Set (ι → Bool)} (hb : ν X {b} ≠ 0) :
    ((Measure.pi ν)[|cause (fun _ ↦ b) {X}]).real B =
      (Measure.pi ν).real ((Function.update · X b) ⁻¹' B) := by
  have h : cause (fun _ ↦ b) {X} ∩ B = cause (fun _ ↦ b) {X} ∩ (Function.update · X b) ⁻¹' B := by
    ext w; simp only [mem_inter_iff, mem_cause, Finset.mem_singleton, forall_eq, mem_preimage]
    exact and_congr_right fun h ↦ by rw [← h, Function.update_eq_self]
  rw [measureReal_def, cond_apply .of_discrete, h, measure_pi_cause_singleton_inter
    (fun w b' ↦ by simp), measure_pi_cause, Finset.prod_singleton, ← mul_assoc,
    ENNReal.inv_mul_cancel hb (measure_ne_top _ _), one_mul, measureReal_def]

private theorem deltaP_pi (h₁ : ν X {true} ≠ 0) (h₀ : ν X {false} ≠ 0) :
    deltaP (Measure.pi ν) (cause (fun _ ↦ true) {X}) E =
      (Measure.pi ν).real ((Function.update · X true) ⁻¹' E) -
        (Measure.pi ν).real ((Function.update · X false) ⁻¹' E) := by
  rw [deltaP, cond_real_pi_cause_singleton h₁, compl_cause_singleton, Bool.not_true,
    cond_real_pi_cause_singleton h₀]

omit [DecidableEq ι] in
private theorem measureReal_mul_cond_real {μ : Measure (ι → Bool)} [IsFiniteMeasure μ]
    {s t : Set (ι → Bool)} : μ.real s * (μ[|s]).real t = μ.real (s ∩ t) := by
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul, mul_comm,
    cond_mul_eq_inter .of_discrete]

private theorem PNS_eq {μ : Measure (ι → Bool)} [IsFiniteMeasure μ] :
    PNS μ X E = μ.real (cause (fun _ ↦ true) {X} ∩ ((Function.update · X true) ⁻¹' E \
        (Function.update · X false) ⁻¹' E)) +
      μ.real (cause (fun _ ↦ false) {X} ∩ ((Function.update · X true) ⁻¹' E \
        (Function.update · X false) ⁻¹' E)) := by
  rw [PNS, measureReal_mul_cond_real, measureReal_mul_cond_real]
  congr 2 <;> ext w <;>
    simp only [mem_inter_iff, mem_cause, Finset.mem_singleton, forall_eq, mem_compl_iff,
      mem_ofPred_eq, Set.mem_sdiff, mem_preimage]
  · constructor
    · rintro ⟨⟨h, hE⟩, h'⟩; exact ⟨h, ⟨by rwa [← h, Function.update_eq_self], h'⟩⟩
    · rintro ⟨h, h₁, h₀⟩; exact ⟨⟨h, by rwa [← h, Function.update_eq_self] at h₁⟩, h₀⟩
  · constructor
    · rintro ⟨⟨h, hE⟩, h'⟩; exact ⟨h, ⟨h', by rwa [← h, Function.update_eq_self]⟩⟩
    · rintro ⟨h, h₁, h₀⟩; exact ⟨⟨h, by rwa [← h, Function.update_eq_self] at h₀⟩, h₁⟩

/-- Under a product measure, PNS is ΔP for an outcome monotone in the cause, the "certain
assumptions" under which §3.3 says the two agree. -/
theorem PNS_eq_deltaP (h₁ : ν X {true} ≠ 0) (h₀ : ν X {false} ≠ 0)
    (hmono : (Function.update · X false) ⁻¹' E ⊆ (Function.update · X true) ⁻¹' E) :
    PNS (Measure.pi ν) X E = deltaP (Measure.pi ν) (cause (fun _ ↦ true) {X}) E := by
  rw [PNS_eq, measureReal_def, measureReal_def,
    measure_pi_cause_singleton_inter (fun w b ↦ by simp),
    measure_pi_cause_singleton_inter (fun w b ↦ by simp), ← ENNReal.toReal_add
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ← add_mul,
    ← measure_union (Set.disjoint_singleton.2 (by decide)) .of_discrete,
    show ({true} : Set Bool) ∪ {false} = univ by ext b; cases b <;> simp, measure_univ, one_mul,
    ← measureReal_def, deltaP_pi h₁ h₀, measureReal_sdiff hmono .of_discrete]

end Measures

section Table1

private theorem real_cause_true (X : Cause) : (prior p).real (cause (fun _ ↦ true) {X}) = p X := by
  rw [measureReal_pi_cause, Finset.prod_singleton, ber_real_true]

private theorem real_cause_false (X : Cause) :
    (prior p).real (cause (fun _ ↦ false) {X}) = 1 - p X := by
  rw [measureReal_pi_cause, Finset.prod_singleton, ber_real_false]

private theorem monotone_effect (s : CausalStructure) :
    (Function.update · c false) ⁻¹' effect s ⊆ (Function.update · c true) ⁻¹' effect s := by
  cases s <;> simp [preimage_update_c]

/-- On conjoined causes SP is `(1 - P(C)) P(A)`, and ΔP, power-PC and PNS are `P(A)` (Table 1). -/
theorem table1_conjunctive (hc₀ : 0 < p c) (hc₁ : p c < 1) :
    SP (prior p) (cause (fun _ ↦ true) {c}) (effect .conjunctive) = (1 - p c) * p a ∧
      deltaP (prior p) (cause (fun _ ↦ true) {c}) (effect .conjunctive) = p a ∧
      powerPC (prior p) (cause (fun _ ↦ true) {c}) (effect .conjunctive) = p a ∧
      PNS (prior p) c (effect .conjunctive) = p a := by
  have hΔ : deltaP (prior p) (cause (fun _ ↦ true) {c}) (effect .conjunctive) = p a := by
    rw [deltaP_pi (X := c) (ber_true_ne_zero hc₀) (ber_false_ne_zero hc₁), preimage_update_c,
      preimage_update_c, measureReal_empty, sub_zero, real_cause_true]
  have hE : effect .conjunctive = cause (fun _ ↦ true) {c, a} := by ext w; simp [effect, mem_cause]
  refine ⟨?_, hΔ, ?_, ?_⟩
  · rw [SP, cond_real_pi_cause_singleton (X := c) (ber_true_ne_zero hc₀), preimage_update_c,
      real_cause_true, hE, measureReal_pi_cause, Finset.prod_pair (by decide), ber_real_true,
      ber_real_true]
    ring
  · rw [powerPC, hΔ, compl_cause_singleton, Bool.not_true,
      cond_real_pi_cause_singleton (X := c) (ber_false_ne_zero hc₁), preimage_compl,
      preimage_update_c, compl_empty, probReal_univ, div_one]
  · rw [PNS_eq_deltaP (X := c) (ber_true_ne_zero hc₀) (ber_false_ne_zero hc₁) (monotone_effect _),
      hΔ]

/-- On disjoined causes SP is `(1 - P(C)) (1 - P(A))`, ΔP and PNS are `1 - P(A)`, and power-PC
is one (Table 1). -/
theorem table1_disjunctive (hc₀ : 0 < p c) (hc₁ : p c < 1) (ha : p a < 1) :
    SP (prior p) (cause (fun _ ↦ true) {c}) (effect .disjunctive) = (1 - p c) * (1 - p a) ∧
      deltaP (prior p) (cause (fun _ ↦ true) {c}) (effect .disjunctive) = 1 - p a ∧
      powerPC (prior p) (cause (fun _ ↦ true) {c}) (effect .disjunctive) = 1 ∧
      PNS (prior p) c (effect .disjunctive) = 1 - p a := by
  have hΔ : deltaP (prior p) (cause (fun _ ↦ true) {c}) (effect .disjunctive) = 1 - p a := by
    rw [deltaP_pi (X := c) (ber_true_ne_zero hc₀) (ber_false_ne_zero hc₁), preimage_update_c,
      preimage_update_c, probReal_univ, real_cause_true]
  have hE : (effect .disjunctive)ᶜ = cause (fun _ ↦ false) {c, a} := by
    ext w; simp [effect, mem_cause]
  refine ⟨?_, hΔ, ?_, ?_⟩
  · rw [SP, cond_real_pi_cause_singleton (X := c) (ber_true_ne_zero hc₀), preimage_update_c,
      probReal_univ, ← compl_compl (effect .disjunctive), probReal_compl_eq_one_sub .of_discrete,
      hE, measureReal_pi_cause, Finset.prod_pair (by decide), ber_real_false, ber_real_false]
    ring
  · rw [powerPC, hΔ, compl_cause_singleton, Bool.not_true,
      cond_real_pi_cause_singleton (X := c) (ber_false_ne_zero hc₁), preimage_compl,
      preimage_update_c, compl_cause_singleton, Bool.not_true, real_cause_false]
    exact div_self (sub_pos.2 (show (p a : ℝ) < 1 from ha)).ne'
  · rw [PNS_eq_deltaP (X := c) (ber_true_ne_zero hc₀) (ber_false_ne_zero hc₁) (monotone_effect _),
      hΔ]

/-- No measure in the literature predicts abnormal deflation, since SP rises while ΔP, PNS and
power-PC stay put (§3.4). -/
theorem no_abnormal_deflation (h : p₂ c < p₁ c) (hc₀ : 0 < p₂ c) (hc₁ : p₁ c < 1)
    (ha : p₁ a = p₂ a) (ha' : p₁ a < 1) :
    SP (prior p₁) (cause (fun _ ↦ true) {c}) (effect .disjunctive) <
        SP (prior p₂) (cause (fun _ ↦ true) {c}) (effect .disjunctive) ∧
      deltaP (prior p₁) (cause (fun _ ↦ true) {c}) (effect .disjunctive) =
        deltaP (prior p₂) (cause (fun _ ↦ true) {c}) (effect .disjunctive) ∧
      PNS (prior p₁) c (effect .disjunctive) = PNS (prior p₂) c (effect .disjunctive) ∧
      powerPC (prior p₁) (cause (fun _ ↦ true) {c}) (effect .disjunctive) =
        powerPC (prior p₂) (cause (fun _ ↦ true) {c}) (effect .disjunctive) := by
  obtain ⟨s₁, d₁, w₁, n₁⟩ := table1_disjunctive (hc₀.trans h) hc₁ ha'
  obtain ⟨s₂, d₂, w₂, n₂⟩ := table1_disjunctive hc₀ (h.trans hc₁) (ha ▸ ha')
  refine ⟨?_, by rw [d₁, d₂, ha], by rw [n₁, n₂, ha], by rw [w₁, w₂]⟩
  rw [s₁, s₂, ← ha]
  have : (p₂ c : ℝ) < p₁ c := h
  have : (p₁ a : ℝ) < 1 := ha'
  nlinarith

end Table1

/-! ### The sampling algorithm (§4.4) -/

section Algorithm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure (ι → Bool)) (w₀ : ι → Bool)
  (E : Set (ι → Bool)) (S : Finset ι)

/-- A step's test draws a world given the cause's absence when the cause is absent, a necessity
test, and given the absence of cause and outcome when it is present, a sufficiency test. -/
noncomputable def test : Kernel Bool (ι → Bool) :=
  Kernel.ofFunOfCountable fun x ↦ if x then μ[|(cause w₀ S)ᶜ ∩ Eᶜ] else μ[|(cause w₀ S)ᶜ]

/-- A step of the algorithm draws whether the cause holds, then a test world. -/
noncomputable def step : Measure (Bool × (ι → Bool)) :=
  (μ.map fun w ↦ decide (w ∈ cause w₀ S)) ⊗ₘ test μ w₀ E S

/-- A step hits when its necessity test removes the outcome or its sufficiency test produces it. -/
noncomputable def hit (z : Bool × (ι → Bool)) : ℝ :=
  if z.1 then {w | S.piecewise w₀ w ∈ E}.indicator 1 z.2
  else {w | S.piecewise w w₀ ∉ E}.indicator 1 z.2

omit [Fintype ι] [DecidableEq ι] in
private theorem test_apply (x : Bool) :
    test μ w₀ E S x = if x then μ[|(cause w₀ S)ᶜ ∩ Eᶜ] else μ[|(cause w₀ S)ᶜ] := rfl

instance : IsFiniteKernel (test μ w₀ E S) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x ↦ by cases x <;> simp [test_apply, prob_le_one]⟩⟩

instance [IsFiniteMeasure μ] : IsFiniteMeasure (step μ w₀ E S) := by unfold step; infer_instance

omit [Fintype ι] [DecidableEq ι] in
theorem isProbabilityMeasure_step [IsProbabilityMeasure μ] (h₀ : μ (cause w₀ S)ᶜ ≠ 0)
    (h₁ : μ ((cause w₀ S)ᶜ ∩ Eᶜ) ≠ 0) : IsProbabilityMeasure (step μ w₀ E S) := by
  have : IsMarkovKernel (test μ w₀ E S) := ⟨fun x ↦ by
    cases x <;> simp only [test_apply, Bool.false_eq_true, ↓reduceIte] <;>
      exact cond_isProbabilityMeasure (by assumption)⟩
  unfold step; infer_instance

-- (1)
theorem integral_hit_step [IsFiniteMeasure μ] :
    ∫ z, hit w₀ E S z ∂(step μ w₀ E S) = (score μ w₀ E S).toReal := by
  have h (b : Bool) : (fun w ↦ decide (w ∈ cause w₀ S)) ⁻¹' {b} =
      if b then cause w₀ S else (cause w₀ S)ᶜ := by cases b <;> ext <;> simp
  rw [step, Measure.integral_compProd Integrable.of_finite, integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_bool, hit, test_apply, ↓reduceIte, Bool.false_eq_true]
  rw [integral_indicator_one .of_discrete, integral_indicator_one .of_discrete,
    map_measureReal_apply (by fun_prop) .of_discrete,
    map_measureReal_apply (by fun_prop) .of_discrete, h, h, score,
    ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) sufficiency_ne_top)
      (ENNReal.mul_ne_top (measure_ne_top _ _) necessity_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp [sufficiency, necessity, measureReal_def, smul_eq_mul]

/-- The sampling algorithm converges, in that on almost every run of independent steps the
proportion of hits tends to the actual causal strength, eq. (1). -/
theorem ae_tendsto_hits [IsFiniteMeasure μ] [IsProbabilityMeasure (step μ w₀ E S)] :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ ↦ step μ w₀ E S),
      Tendsto (fun K : ℕ ↦ (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, hit w₀ E S (ω k)) atTop
        (𝓝 (score μ w₀ E S).toReal) := by
  set P := Measure.infinitePi fun _ : ℕ ↦ step μ w₀ E S
  have hmeas : Measurable (hit w₀ E S) := measurable_of_countable _
  have hlaw (n : ℕ) : P.map (· n) = step μ w₀ E S := Measure.infinitePi_map_eval _ n
  have hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ hit w₀ E S (ω i)) (fun ω ↦ hit w₀ E S (ω j)) P :=
    fun i j hij ↦ ((iIndepFun_infinitePi (P := fun _ : ℕ ↦ step μ w₀ E S) (X := fun _ ↦ id)
      fun _ ↦ measurable_id).indepFun hij).comp hmeas hmeas
  have hident (n : ℕ) : IdentDistrib (fun ω ↦ hit w₀ E S (ω n)) (fun ω ↦ hit w₀ E S (ω 0)) P P :=
    (IdentDistrib.mk (measurable_pi_apply n).aemeasurable (measurable_pi_apply 0).aemeasurable
      ((hlaw n).trans (hlaw 0).symm)).comp hmeas
  have hint : Integrable (fun ω ↦ hit w₀ E S (ω 0)) P :=
    (show Integrable (hit w₀ E S) (P.map (· 0)) by rw [hlaw 0]; exact .of_finite).comp_measurable
      (measurable_pi_apply 0)
  filter_upwards [strong_law_ae _ hint hind hident] with ω hω
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hmeas.aestronglyMeasurable, hlaw 0,
    integral_hit_step] at hω
  simpa [smul_eq_mul] using hω

end Algorithm

/-! ### The experiments (§5)

In both experiments, with prescriptive norms and with statistical ones, a norm-violating cause was
rated more causal than a normative one when the causes were conjoined and less causal when they
were disjoined, as `abnormal_inflation` and `abnormal_deflation` predict when norm violation
lowers the sampling propensity (§4.2); the interaction is significant in both. -/

example : ∀ e, (ratings e .conjunctive .normative).mean.toRat <
      (ratings e .conjunctive .violation).mean.toRat ∧
    (ratings e .disjunctive .violation).mean.toRat <
      (ratings e .disjunctive .normative).mean.toRat := by
  decide +kernel

end IcardEtAl2017
