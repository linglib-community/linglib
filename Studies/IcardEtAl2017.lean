module

public import Linglib.Data.Statistics.IcardEtAl2017
public import Linglib.Semantics.Causation.CausalStrength
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.StrongLaw

/-!
# Icard, Kominsky and Knobe (2017): Normality and actual causal strength

Icard, Kominsky and Knobe measure actual causal strength by a cause's sufficiency weighted by its
probability plus its necessity weighted by the probability of its absence, the probabilities being
sampling propensities that rise with normality and the measure the limit of a
[sampling algorithm](##ae_tendsto_hits). On the collider $C \to E \leftarrow A$ it is
$P(C)P(A) - P(C) + 1$ for conjoined causes and $P(C)$ for disjoined ones, so it
[meets](##strength_desiderata) the three desiderata drawn from earlier findings and a fourth,
abnormal deflation (with disjoined causes, a less normal $C$ is less causal), which
[no existing measure meets](##not_abnormalDeflation) and both experiments'
[mean ratings](##strength_lt_iff_ratings) bear out.

## Implementation notes

* Worlds are the draws of C and A under independent Bernoulli priors, the paper's sampling
  propensities, and each causal structure's effect is an event; the measure is the substrate's
  `CausalStrength.score` in the round C = A = E = 1.
* The paper names two candidates for sufficiency (§4.3); the substrate takes Cheng and Pearl's,
  conditioned on the absence of cause and effect, and `resampleSufficiency_eq_sufficiency` shows
  the other agrees on the collider. As `cond` of a null event is the zero measure, the closed forms
  assume priors below one, and the desiderata compare priors strictly between zero and one, where
  every existing measure is defined.

## References

* [icard-et-al-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology unitInterval CausalStrength
open scoped ENNReal

namespace IcardEtAl2017

/-! ### The unshielded collider (§3.2) -/

/-- The collider has a focal cause `c` and an alternative cause `a`. -/
inductive Cause | c | a
  deriving DecidableEq, Fintype

open Cause

/-- The prior draws the causes independently, `c` with probability `x` and `a` with
probability `y`. -/
noncomputable abbrev prior (x y : I) : Measure (Cause → Bool) :=
  Measure.pi fun i ↦ Ber(true, false, if i = c then x else y)

/-- The effect of a causal structure is the minimum of the two causes if they are conjoined and
their maximum if they are disjoined. -/
def effect : CausalStructure → Set (Cause → Bool)
  | .conjunctive => {w | min (w c) (w a) = true}
  | .disjunctive => {w | max (w c) (w a) = true}

instance : ∀ s, DecidablePred (· ∈ effect s)
  | .conjunctive => fun w ↦ inferInstanceAs (Decidable (min (w c) (w a) = true))
  | .disjunctive => fun w ↦ inferInstanceAs (Decidable (max (w c) (w a) = true))

/-- `strength x y s` is the actual causal strength of `C = 1` for `E = 1` when `C = A = E = 1`,
under the priors `x` of `C` and `y` of `A`, eq. (1). -/
noncomputable def strength (x y : I) (s : CausalStructure) : ℝ≥0∞ :=
  score (prior x y) (fun _ ↦ true) (effect s) {c}

variable {x y : I}

theorem strength_ne_top {s : CausalStructure} : strength x y s ≠ ∞ := score_ne_top

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

/-! ### The desiderata (§3.2, §5, Table 5)

A measure of the strength of `C = 1` for `E = 1` is a function of the priors of `C` and `A` and of
the causal structure. Each desideratum is a cell of Table 5: how the measure changes with one
prior, both priors strictly between zero and one. -/

section Desiderata

variable {β : Type*} [Preorder β] (κ : I → I → CausalStructure → β)

/-- Abnormal inflation: when the causes are conjoined, a less normal `C` is more causal. -/
def AbnormalInflation : Prop :=
  ∀ y ∈ Ioo 0 1, StrictAntiOn (κ · y .conjunctive) (Ioo 0 1)

/-- Supersession: when the causes are conjoined, a less normal `A` makes `C` less causal. -/
def Supersession : Prop :=
  ∀ x ∈ Ioo 0 1, StrictMonoOn (κ x · .conjunctive) (Ioo 0 1)

/-- No supersession with disjunction: when the causes are disjoined, the normality of `A` leaves
the strength of `C` unchanged. -/
def NoSupersessionWithDisjunction : Prop :=
  ∀ x ∈ Ioo 0 1, ∀ y₁ ∈ Ioo 0 1, ∀ y₂ ∈ Ioo 0 1, κ x y₁ .disjunctive = κ x y₂ .disjunctive

/-- Abnormal deflation: when the causes are disjoined, a less normal `C` is less causal. -/
def AbnormalDeflation : Prop :=
  ∀ y ∈ Ioo 0 1, StrictMonoOn (κ · y .disjunctive) (Ioo 0 1)

end Desiderata

private theorem exists_lt_mem : ∃ u v : I, u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 ∧ u < v :=
  ⟨⟨1 / 3, by norm_num, by norm_num⟩, ⟨2 / 3, by norm_num, by norm_num⟩,
    ⟨show (0 : ℝ) < 1 / 3 by norm_num, show (1 / 3 : ℝ) < 1 by norm_num⟩,
    ⟨show (0 : ℝ) < 2 / 3 by norm_num, show (2 / 3 : ℝ) < 1 by norm_num⟩,
    show (1 / 3 : ℝ) < 2 / 3 by norm_num⟩

/-! ### The existing measures (§3.3, §3.4, Table 1) -/

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
  rw [measureReal_def, cond_apply .of_discrete, h, ← cond_apply .of_discrete, ← measureReal_def,
    (indepSet_pi_cause_singleton fun w b' ↦ by simp).cond_real_apply .of_discrete
      (by rwa [measure_pi_cause, Finset.prod_singleton])]

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

-- §3.3: under a product measure, PNS is ΔP for an outcome monotone in the cause
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

/-- The existing measures of Table 1. -/
inductive ExistingMeasure | sp | deltaP | powerPC | pns
  deriving DecidableEq, Fintype

/-- The strength of `C = 1` for `E = 1` that an existing measure assigns on the collider. -/
noncomputable def ExistingMeasure.strength : ExistingMeasure → I → I → CausalStructure → ℝ
  | .sp, x, y, s => SP (prior x y) (cause (fun _ ↦ true) {c}) (effect s)
  | .deltaP, x, y, s => IcardEtAl2017.deltaP (prior x y) (cause (fun _ ↦ true) {c}) (effect s)
  | .powerPC, x, y, s => IcardEtAl2017.powerPC (prior x y) (cause (fun _ ↦ true) {c}) (effect s)
  | .pns, x, y, s => PNS (prior x y) c (effect s)

private theorem real_cause_a_true : (prior x y).real (cause (fun _ ↦ true) {a}) = y := by
  rw [measureReal_pi_cause, Finset.prod_singleton, ber_real_true, ite_eq_right (by decide)]

private theorem real_cause_a_false : (prior x y).real (cause (fun _ ↦ false) {a}) = 1 - y := by
  rw [measureReal_pi_cause, Finset.prod_singleton, ber_real_false, ite_eq_right (by decide)]

private theorem monotone_effect (s : CausalStructure) :
    (Function.update · c false) ⁻¹' effect s ⊆ (Function.update · c true) ⁻¹' effect s := by
  cases s <;> simp [preimage_update_c]

-- Table 1
theorem table1_conjunctive (hx : x ∈ Ioo 0 1) (m : ExistingMeasure) :
    m.strength x y .conjunctive = match m with
      | .sp => (1 - x) * y
      | .deltaP | .powerPC | .pns => y := by
  have hΔ : deltaP (prior x y) (cause (fun _ ↦ true) {c}) (effect .conjunctive) = y := by
    rw [deltaP_pi (X := c) (ber_true_ne_zero hx.1) (ber_false_ne_zero hx.2), preimage_update_c,
      preimage_update_c, measureReal_empty, sub_zero, real_cause_a_true]
  have hE : effect .conjunctive = cause (fun _ ↦ true) {c, a} := by ext w; simp [effect, mem_cause]
  cases m <;> dsimp only [ExistingMeasure.strength]
  · rw [SP, cond_real_pi_cause_singleton (X := c) (ber_true_ne_zero hx.1), preimage_update_c,
      real_cause_a_true, hE, measureReal_pi_cause, Finset.prod_pair (by decide), ber_real_true,
      ber_real_true, ite_eq_left rfl, ite_eq_right (by decide)]
    ring
  · exact hΔ
  · rw [powerPC, hΔ, compl_cause_singleton, Bool.not_true,
      cond_real_pi_cause_singleton (X := c) (ber_false_ne_zero hx.2), preimage_compl,
      preimage_update_c, compl_empty, probReal_univ, div_one]
  · rw [PNS_eq_deltaP (X := c) (ber_true_ne_zero hx.1) (ber_false_ne_zero hx.2)
      (monotone_effect _), hΔ]

-- Table 1
theorem table1_disjunctive (hx : x ∈ Ioo 0 1) (hy : y < 1) (m : ExistingMeasure) :
    m.strength x y .disjunctive = match m with
      | .sp => (1 - x) * (1 - y)
      | .deltaP | .pns => 1 - y
      | .powerPC => 1 := by
  have hΔ : deltaP (prior x y) (cause (fun _ ↦ true) {c}) (effect .disjunctive) = 1 - y := by
    rw [deltaP_pi (X := c) (ber_true_ne_zero hx.1) (ber_false_ne_zero hx.2), preimage_update_c,
      preimage_update_c, probReal_univ, real_cause_a_true]
  have hE : (effect .disjunctive)ᶜ = cause (fun _ ↦ false) {c, a} := by
    ext w; simp [effect, mem_cause]
  cases m <;> dsimp only [ExistingMeasure.strength]
  · rw [SP, cond_real_pi_cause_singleton (X := c) (ber_true_ne_zero hx.1), preimage_update_c,
      probReal_univ, ← compl_compl (effect .disjunctive), probReal_compl_eq_one_sub .of_discrete,
      hE, measureReal_pi_cause, Finset.prod_pair (by decide), ber_real_false, ber_real_false,
      ite_eq_left rfl, ite_eq_right (by decide)]
    ring
  · exact hΔ
  · rw [powerPC, hΔ, compl_cause_singleton, Bool.not_true,
      cond_real_pi_cause_singleton (X := c) (ber_false_ne_zero hx.2), preimage_compl,
      preimage_update_c, compl_cause_singleton, Bool.not_true, real_cause_a_false]
    exact div_self (sub_pos.2 (show (y : ℝ) < 1 from hy)).ne'
  · rw [PNS_eq_deltaP (X := c) (ber_true_ne_zero hx.1) (ber_false_ne_zero hx.2)
      (monotone_effect _), hΔ]

namespace ExistingMeasure

variable (m : ExistingMeasure)

-- §3.4: every existing measure shows supersession
theorem supersession : Supersession m.strength := by
  intro x hx y₁ _ y₂ _ hy
  dsimp only
  rw [table1_conjunctive hx, table1_conjunctive hx]
  cases m
  · exact mul_lt_mul_of_pos_left hy (sub_pos.2 (show (x : ℝ) < 1 from hx.2))
  all_goals exact hy

-- §3.4: only SP shows abnormal inflation
theorem abnormalInflation_iff : AbnormalInflation m.strength ↔ m = .sp := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv⟩ := exists_lt_mem
    have := h u hu hu hv huv
    dsimp only at this
    rw [table1_conjunctive hu, table1_conjunctive hv] at this
    cases m
    · rfl
    all_goals exact absurd this (lt_irrefl _)
  · rintro rfl y hy x₁ hx₁ x₂ hx₂ hx
    dsimp only
    rw [table1_conjunctive hx₁, table1_conjunctive hx₂]
    exact mul_lt_mul_of_pos_right (sub_lt_sub_left (show (x₁ : ℝ) < x₂ from hx) 1) hy.1

-- §3.4: only power-PC shows no supersession with disjunction
theorem noSupersessionWithDisjunction_iff :
    NoSupersessionWithDisjunction m.strength ↔ m = .powerPC := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv⟩ := exists_lt_mem
    have := h u hu u hu v hv
    rw [table1_disjunctive hu hu.2, table1_disjunctive hu hv.2] at this
    have huv' : (u : ℝ) < v := huv
    cases m
    · exact absurd (mul_left_cancel₀ (sub_pos.2 (show (u : ℝ) < 1 from hu.2)).ne' this)
        (by linarith)
    · exact absurd this (by dsimp only; linarith)
    · rfl
    · exact absurd this (by dsimp only; linarith)
  · rintro rfl x hx y₁ hy₁ y₂ hy₂
    rw [table1_disjunctive hx hy₁.2, table1_disjunctive hx hy₂.2]

/-- No existing measure predicts abnormal deflation (§3.4). -/
theorem not_abnormalDeflation : ¬AbnormalDeflation m.strength := by
  intro h
  obtain ⟨u, v, hu, hv, huv⟩ := exists_lt_mem
  have := h u hu hu hv huv
  dsimp only at this
  rw [table1_disjunctive hu hu.2, table1_disjunctive hv hu.2] at this
  have huv' : (u : ℝ) < v := huv
  have hu' : (0 : ℝ) < 1 - u := sub_pos.2 hu.2
  cases m
  · exact absurd this (not_lt.2 (mul_le_mul_of_nonneg_right (by linarith) hu'.le))
  all_goals exact absurd this (lt_irrefl _)

end ExistingMeasure

/-! ### Necessity and sufficiency (§4.3, Table 2) -/

-- Table 2
theorem necessity_disjunctive (μ : Measure (Cause → Bool)) :
    necessity μ (fun _ ↦ true) (effect .disjunctive) {c} = 0 :=
  necessity_eq_zero (by decide)

-- Table 2
theorem necessity_conjunctive (hx : x < 1) :
    necessity (prior x y) (fun _ ↦ true) (effect .conjunctive) {c} = 1 :=
  necessity_eq_one (by decide)
    (by rw [measure_pi_compl_cause_singleton]; exact ber_false_ne_zero hx)

-- Table 2
theorem sufficiency_conjunctive (hx : x < 1) :
    sufficiency (prior x y) (fun _ ↦ true) (effect .conjunctive) {c} =
      Ber(true, false, y) {true} := by
  rw [sufficiency_singleton (X := c) (by exact ber_false_ne_zero hx)]
  simp [preimage_update_c, measure_pi_cause]

-- Table 2
theorem sufficiency_disjunctive (hx : x < 1) (hy : y < 1) :
    sufficiency (prior x y) (fun _ ↦ true) (effect .disjunctive) {c} = 1 := by
  have hy' : prior x y (cause (fun _ ↦ true) {a})ᶜ ≠ 0 := by
    rw [measure_pi_compl_cause_singleton]; exact ber_false_ne_zero hy
  rw [sufficiency_singleton (X := c) (by exact ber_false_ne_zero hx)]
  simp only [Bool.not_true, preimage_update_c]
  rw [← compl_eq_univ_sdiff, ENNReal.div_self hy' (measure_ne_top _ _)]

/-- The sufficiency that forces the cause on and redraws every other variable,
`P(E | do(C = 1))`. -/
noncomputable def resampleSufficiency {ι : Type*} [DecidableEq ι] (μ : Measure (ι → Bool))
    (w₀ : ι → Bool) (E : Set (ι → Bool)) (S : Finset ι) : ℝ≥0∞ :=
  μ {w | S.piecewise w₀ w ∈ E}

-- §4.3
theorem resampleSufficiency_eq_sufficiency (s : CausalStructure) (hx : x < 1) (hy : y < 1) :
    resampleSufficiency (prior x y) (fun _ ↦ true) (effect s) {c} =
      sufficiency (prior x y) (fun _ ↦ true) (effect s) {c} := by
  have h (s : CausalStructure) : {w : Cause → Bool | ({c} : Finset Cause).piecewise
      (fun _ ↦ true) w ∈ effect s} = (Function.update · c true) ⁻¹' effect s := by
    ext w; simp [Finset.piecewise_singleton]
  unfold resampleSufficiency
  cases s
  · rw [sufficiency_conjunctive hx, h, preimage_update_c, measure_pi_cause, Finset.prod_singleton,
      ite_eq_right (by decide)]
  · rw [sufficiency_disjunctive hx hy, h, preimage_update_c, measure_univ]

/-! ### The measure (§4.4) -/

-- (3)
theorem toReal_strength_conjunctive (hx : x < 1) :
    (strength x y .conjunctive).toReal = x * y - x + 1 := by
  rw [strength, score_singleton (X := c) (by exact ber_false_ne_zero hx),
    sufficiency_conjunctive hx]
  simp only [Bool.not_true, ↓reduceIte]
  rw [ite_eq_right (show Function.update (fun _ : Cause ↦ true) c false ∉ effect .conjunctive
      by decide), ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (measure_ne_top _ _), ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
    ← measureReal_def, ber_real_true, ber_real_true, ber_real_false]
  ring

-- (2)
theorem toReal_strength_disjunctive (hx : x < 1) (hy : y < 1) :
    (strength x y .disjunctive).toReal = x := by
  rw [strength, score_singleton (X := c) (by exact ber_false_ne_zero hx),
    sufficiency_disjunctive hx hy]
  simp only [Bool.not_true, ↓reduceIte]
  rw [ite_eq_left (show Function.update (fun _ : Cause ↦ true) c false ∈ effect .disjunctive
      by decide), mul_one, add_zero, ← measureReal_def, ber_real_true]

/-- The measure meets all four desiderata (§4.4, §5). -/
theorem strength_desiderata : AbnormalInflation strength ∧ Supersession strength ∧
    NoSupersessionWithDisjunction strength ∧ AbnormalDeflation strength := by
  refine ⟨fun y hy x₁ hx₁ x₂ hx₂ hx ↦ ?_, fun x hx y₁ _ y₂ _ hy ↦ ?_,
    fun x hx y₁ hy₁ y₂ hy₂ ↦ ?_, fun y hy x₁ hx₁ x₂ hx₂ hx ↦ ?_⟩
  · rw [← ENNReal.toReal_lt_toReal strength_ne_top strength_ne_top,
      toReal_strength_conjunctive hx₁.2, toReal_strength_conjunctive hx₂.2]
    have : (x₁ : ℝ) < x₂ := hx
    have : (y : ℝ) < 1 := hy.2
    nlinarith
  · rw [← ENNReal.toReal_lt_toReal strength_ne_top strength_ne_top,
      toReal_strength_conjunctive hx.2, toReal_strength_conjunctive hx.2]
    have : (y₁ : ℝ) < y₂ := hy
    have : (0 : ℝ) < x := hx.1
    nlinarith
  · rw [← ENNReal.toReal_eq_toReal_iff' strength_ne_top strength_ne_top,
      toReal_strength_disjunctive hx.2 hy₁.2, toReal_strength_disjunctive hx.2 hy₂.2]
  · rw [← ENNReal.toReal_lt_toReal strength_ne_top strength_ne_top,
      toReal_strength_disjunctive hx₁.2 hy.2, toReal_strength_disjunctive hx₂.2 hy.2]
    exact hx

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

/-! ### The experiments (§5) -/

/-- The measure orders the mean ratings of both experiments: if norm violation lowers the varied
agent's sampling propensity (§4.2), the measure ranks the violating agent above the normative one
exactly where participants did, in the conjunctive vignettes. -/
theorem strength_lt_iff_ratings (e : Experiment) (s : CausalStructure) {xN xV y : I}
    (hN : xN ∈ Ioo 0 1) (hV : xV ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) (hx : xV < xN) :
    strength xN y s < strength xV y s ↔
      (ratings e s .normative).mean.toRat < (ratings e s .violation).mean.toRat := by
  obtain ⟨hinf, -, -, hdef⟩ := strength_desiderata
  cases s
  · exact iff_of_true (hinf y hy hV hN hx) (by cases e <;> decide +kernel)
  · exact iff_of_false (hdef y hy hV hN hx).asymm (by cases e <;> decide +kernel)

end IcardEtAl2017
