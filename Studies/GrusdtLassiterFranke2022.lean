/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Probability.UniformOn

/-!
# Grusdt, Lassiter, and Franke (2022): Rational Communication with Conditionals

This file formalizes the toy example of section 2.3 of Grusdt, Lassiter and Franke, "Probabilistic
modeling of rational communication with conditionals", together with the two arguments of section 5
that rest on its assertability conditions alone. A state is a probability measure on the four worlds
that fix the truth of `A` and `C`; an utterance is assertable in a state by the conditions of Table
1, `P(A ∧ C) ≥ θ` for the conjunction, `P(C) ≥ θ` for the literal, `P(C | A) ≥ θ` for the
conditional, and `P(C) > 1/2` for *likely C* (`Assertable`); and the vanilla Rational Speech Act
model of section 2.1, the library's `RSA.speaker` and its posterior at `α = 1` without
costs, runs over the three states of Table 2. Its predictions are derived: the extensions of Table
2(b), the speaker shares of Table 2(d), and the listener posteriors of Table 2(e), on which hearing
*if A then C* favors the state where the conditional is the most informative assertable utterance
over the one where the literal was available (`l1_conditional_prefers_s2`). Section 5's observations
hold for every state: when antecedent and consequent are independent the conditional is assertable
only where the literal is, so a speaker never prefers it, which is what lies behind the infelicity
of missing-link conditionals (`assertable_C_of_indep`), and a speaker who can assert both *if A then
C* and *if not A then C* could have asserted *C* outright (`assertable_C_of_conditionals`).

## Implementation notes

States are measures built from the cells of Table 2(a); the threshold is the paper's `θ = 0.9`.
Section 5.3's argument takes `P(A) = 1/2`, but the theorem needs only that the antecedent and
its negation both have positive probability. The causal Bayes-net prior of sections 2.4 to 3
and the simulation results over it, including the strength of conditional perfection in
Figure 8, are not formalized; `perfection_not_semantic` records only that in the toy example
the conditional is assertable at `s2` while `P(¬C | ¬A)` falls short of the threshold, so any
perfection reading there is pragmatic.

## References

* [grusdt-lassiter-franke-2022]
-/

@[expose] public section

namespace GrusdtLassiterFranke2022

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

/-! ### World states, utterances and assertability, section 2.2 -/

/-- The event that `A` holds, on worlds `(A, C) : Bool × Bool`. -/
def A : Set (Bool × Bool) := {w | w.1}

/-- The event that `C` holds. -/
def C : Set (Bool × Bool) := {w | w.2}

theorem A_eq : A = ↑({(true, true), (true, false)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A]

theorem C_eq : C = ↑({(true, true), (false, true)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [C]

theorem A_inter_C_eq : A ∩ C = ↑({(true, true)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A, C]

theorem Ac_eq : Aᶜ = ↑({(false, true), (false, false)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A]

theorem Ac_inter_Cc_eq : Aᶜ ∩ Cᶜ = ↑({(false, false)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A, C]

/-- The toy example's utterances, in Table 1's order of informativity, are the conjunction
*A and C*, the literal *C*, the conditional *if A then C*, and *likely C*. -/
inductive Utt
  | conjAC
  | C
  | conditional
  | likelyC
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utt := ⊤
instance : DiscreteMeasurableSpace Utt := ⟨fun _ => trivial⟩
instance : Nonempty Utt := ⟨.likelyC⟩

private theorem sum_Utt {M : Type*} [AddCommMonoid M] (f : Utt → M) :
    ∑ u, f u = f .conjAC + (f .C + (f .conditional + f .likelyC)) := by
  rw [show (Finset.univ : Finset Utt) = {.conjAC, .C, .conditional, .likelyC} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- The assertability threshold of Table 2, `θ = 0.9`. -/
noncomputable def θ : ℝ := 9 / 10

/-- By Table 1, an utterance is assertable in a state `μ` when the probability it conveys
reaches the threshold, `P(A ∧ C) ≥ θ`, `P(C) ≥ θ`, `P(C | A) ≥ θ`, and *likely C* when
`P(C) > 1/2`. -/
def Assertable (θ : ℝ) : Utt → Measure (Bool × Bool) → Prop
  | .conjAC, μ => θ ≤ μ.real (A ∩ C)
  | .C, μ => θ ≤ μ.real C
  | .conditional, μ => θ ≤ (μ[|A]).real C
  | .likelyC, μ => 1 / 2 < μ.real C

theorem real_cond (μ : Measure (Bool × Bool)) (S T : Set (Bool × Bool)) :
    (μ[|S]).real T = μ.real (S ∩ T) / μ.real S := by
  rw [measureReal_def, cond_apply .of_discrete, ENNReal.toReal_mul, ENNReal.toReal_inv,
    measureReal_def, measureReal_def, div_eq_inv_mul]

/-! ### Two consequences of the assertability conditions, section 5

Section 5.1: when antecedent and consequent are independent, the conditional is assertable
only where the literal is, so an informative speaker never chooses it, and a listener who
takes the two to be independent is surprised by it, the source of the infelicity of
missing-link conditionals. Section 5.3: a speaker who can assert both *if A then C* and *if
not A then C* could have asserted *C* outright. -/

theorem assertable_C_of_indep {μ : Measure (Bool × Bool)} {t : ℝ} (hA : 0 < μ.real A)
    (hind : μ.real (A ∩ C) = μ.real A * μ.real C) (h : Assertable t .conditional μ) :
    Assertable t .C μ := by
  simp only [Assertable, real_cond] at h ⊢
  rwa [hind, mul_div_cancel_left₀ _ hA.ne'] at h

theorem assertable_C_of_conditionals {μ : Measure (Bool × Bool)} [IsProbabilityMeasure μ] {t : ℝ}
    (hA : 0 < μ.real A) (hAc : 0 < μ.real Aᶜ) (h₁ : t ≤ (μ[|A]).real C)
    (h₂ : t ≤ (μ[|Aᶜ]).real C) : Assertable t .C μ := by
  simp only [Assertable]
  rw [real_cond, le_div_iff₀ hA] at h₁
  rw [real_cond, le_div_iff₀ hAc] at h₂
  have htot : μ.real (A ∩ C) + μ.real (Aᶜ ∩ C) = μ.real C := by
    have := measureReal_inter_add_sdiff (μ := μ) (s := C) (MeasurableSet.of_discrete (s := A))
    rwa [Set.inter_comm, Set.sdiff_eq_compl_inter] at this
  have hsum : μ.real A + μ.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl .of_discrete]
    simp [measureReal_def]
  calc t = t * (μ.real A + μ.real Aᶜ) := by rw [hsum, mul_one]
    _ = t * μ.real A + t * μ.real Aᶜ := mul_add ..
    _ ≤ μ.real (A ∩ C) + μ.real (Aᶜ ∩ C) := add_le_add h₁ h₂
    _ = μ.real C := htot

/-! ### The toy example, section 2.3 and Table 2 -/

/-- In the three states of Table 2(a), Alex and Chris come to the party independently in `s1`
and `s3`, and in `s2` "usually not without each other". -/
inductive State
  | s1
  | s2
  | s3
  deriving DecidableEq, Fintype

instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩
instance : Nonempty State := ⟨.s1⟩

private theorem sum_State {M : Type*} [AddCommMonoid M] (f : State → M) :
    ∑ s, f s = f .s1 + (f .s2 + f .s3) := by
  rw [show (Finset.univ : Finset State) = {.s1, .s2, .s3} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Table 2(a) gives the probability of each world `(A, C)` in each state. -/
noncomputable def State.cell : State → Bool × Bool → ℝ≥0
  | .s1, (true, true) => 81 / 100
  | .s1, (true, false) => 9 / 100
  | .s1, (false, true) => 9 / 100
  | .s1, (false, false) => 1 / 100
  | .s2, (true, true) => 3 / 5
  | .s2, (true, false) => 1 / 20
  | .s2, (false, true) => 1 / 20
  | .s2, (false, false) => 3 / 10
  | .s3, (true, true) => 9 / 25
  | .s3, (true, false) => 6 / 25
  | .s3, (false, true) => 6 / 25
  | .s3, (false, false) => 4 / 25

/-- A state as a probability measure on worlds. -/
noncomputable def State.dist (s : State) : Measure (Bool × Bool) :=
  Measure.sum fun w => (s.cell w : ℝ≥0∞) • Measure.dirac w

theorem State.dist_finset (s : State) (E : Finset (Bool × Bool)) :
    s.dist ↑E = ∑ w ∈ E, (s.cell w : ℝ≥0∞) := by
  rw [← sum_measure_singleton]
  exact Finset.sum_congr rfl fun w _ => Measure.sum_smul_dirac_singleton

theorem State.dist_real_finset (s : State) (E : Finset (Bool × Bool)) :
    s.dist.real ↑E = ∑ w ∈ E, (s.cell w : ℝ) := by
  rw [measureReal_def, State.dist_finset, ENNReal.toReal_sum fun _ _ => ENNReal.coe_ne_top]
  simp only [ENNReal.coe_toReal]

theorem State.sum_cell (s : State) : ∑ w, s.cell w = 1 := by
  cases s <;> simp [Fintype.sum_prod_type, State.cell] <;> norm_num

instance (s : State) : IsProbabilityMeasure s.dist :=
  (s.sum_cell ▸ hasSum_fintype s.cell).isProbabilityMeasure_sum_dirac_nnreal

theorem real_A (s : State) : s.dist.real A = s.cell (true, true) + s.cell (true, false) := by
  rw [A_eq, State.dist_real_finset, Finset.sum_pair (by decide)]

theorem real_C (s : State) : s.dist.real C = s.cell (true, true) + s.cell (false, true) := by
  rw [C_eq, State.dist_real_finset, Finset.sum_pair (by decide)]

theorem real_A_inter_C (s : State) : s.dist.real (A ∩ C) = s.cell (true, true) := by
  rw [A_inter_C_eq, State.dist_real_finset, Finset.sum_singleton]

theorem real_Ac (s : State) : s.dist.real Aᶜ = s.cell (false, true) + s.cell (false, false) := by
  rw [Ac_eq, State.dist_real_finset, Finset.sum_pair (by decide)]

theorem real_Ac_inter_Cc (s : State) : s.dist.real (Aᶜ ∩ Cᶜ) = s.cell (false, false) := by
  rw [Ac_inter_Cc_eq, State.dist_real_finset, Finset.sum_singleton]

/-- The assertability extension of an utterance at the threshold `θ`. -/
def ext (u : Utt) : Set State := {s | Assertable θ u s.dist}

/-- *Likely C* is assertable everywhere (Table 2(b)). -/
theorem ext_likelyC : ext .likelyC = Set.univ := by
  ext s; cases s <;> simp [ext, Assertable, real_C, State.cell] <;> norm_num

/-- The conditional is assertable in `s1` and `s2` but not in `s3` (Table 2(b)). -/
theorem ext_conditional : ext .conditional = ↑({State.s1, .s2} : Finset State) := by
  ext s; cases s <;> simp [ext, Assertable, real_cond, real_A, real_A_inter_C, State.cell, θ] <;>
    norm_num

/-- *C* is assertable in `s1` only (Table 2(b)). -/
theorem ext_C : ext .C = ↑({State.s1} : Finset State) := by
  ext s; cases s <;> simp [ext, Assertable, real_C, State.cell, θ] <;> norm_num

/-- *A and C* is assertable nowhere (Table 2(b)). -/
theorem ext_conjAC : ext .conjAC = ∅ := by
  ext s; cases s <;> simp [ext, Assertable, real_A_inter_C, State.cell, θ] <;> norm_num

/-! ### Literal listener and speaker, Table 2(c) and (d)

The vanilla model at `α = 1` without costs, against the uniform prior over the three states:
the literal listener conditions the prior on the extension, the speaker is `RSA.speaker`, and
the pragmatic listener is the posterior of the speaker against the prior. *A and C*, assertable
in no state, has the zero measure as its literal listener and drops out of the competition. -/

/-- The uniform prior over the three states. -/
noncomputable def prior : Measure State := uniformOn Set.univ

instance : IsProbabilityMeasure prior :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

theorem prior_singleton (s : State) : prior {s} = 3⁻¹ := by
  rw [prior, uniformOn_univ_apply_singleton, show Fintype.card State = 3 from rfl]; simp

theorem prior_real_singleton (s : State) : prior.real {s} = 1 / 3 := by
  rw [measureReal_def, prior_singleton, ENNReal.toReal_inv, one_div]; simp

/-- The literal listener conditions the prior on the utterance's extension. -/
noncomputable def L0 : Kernel Utt State := listener prior (truthful ext)

instance : IsFiniteKernel L0 := inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

theorem L0_apply (u : Utt) : L0 u = uniformOn (ext u) := by
  rw [L0, listener_truthful_apply, prior, uniformOn,
    cond_cond_eq_cond_inter MeasurableSet.univ .of_discrete, Set.univ_inter]
  rfl

theorem L0_real_likelyC (s : State) : (L0 .likelyC).real {s} = 1 / 3 := by
  rw [L0_apply, ext_likelyC, ← prior, prior_real_singleton]

theorem L0_real_conjAC (s : State) : (L0 .conjAC).real {s} = 0 := by
  rw [L0_apply, ext_conjAC, uniformOn_empty_meas]; rfl

theorem L0_real_conditional_s1 : (L0 .conditional).real {.s1} = 1 / 2 := by
  rw [L0_apply, ext_conditional, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_conditional_s2 : (L0 .conditional).real {.s2} = 1 / 2 := by
  rw [L0_apply, ext_conditional, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_conditional_s3 : (L0 .conditional).real {.s3} = 0 := by
  rw [L0_apply, ext_conditional, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_C_s1 : (L0 .C).real {.s1} = 1 := by
  rw [L0_apply, ext_C, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_C_s2 : (L0 .C).real {.s2} = 0 := by
  rw [L0_apply, ext_C, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_C_s3 : (L0 .C).real {.s3} = 0 := by
  rw [L0_apply, ext_C, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_ne_top (u : Utt) (s : State) : L0 u {s} ≠ ⊤ := by
  rw [L0_apply]; exact measure_ne_top _ _

/-- The speaker of Table 2(d) is `RSA.speaker` at `α = 1` without costs. -/
noncomputable def S1 : Kernel State Utt := speaker 1 0 L0 Measure.dirac

instance : IsFiniteKernel S1 := inferInstanceAs (IsFiniteKernel (speaker _ _ _ Measure.dirac))

theorem S1_real (s : State) (u : Utt) :
    (S1 s).real {u} = (L0 u).real {s} / ∑ u', (L0 u').real {s} := by
  simp only [S1, measureReal_def, speaker_dirac_zero_apply_singleton, ENNReal.rpow_one]
  rw [ENNReal.toReal_div, ENNReal.toReal_sum fun u' _ => L0_ne_top u' s]

/-- In `s1` the speaker says `C` with share `6/11`, the conditional `3/11`, and *likely C*
`2/11` (Table 2(d)). -/
theorem S1_s1_C : (S1 .s1).real {.C} = 6 / 11 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s1, L0_real_conditional_s1, L0_real_likelyC]
  norm_num

theorem S1_s1_conditional : (S1 .s1).real {.conditional} = 3 / 11 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s1, L0_real_conditional_s1, L0_real_likelyC]
  norm_num

theorem S1_s1_likelyC : (S1 .s1).real {.likelyC} = 2 / 11 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s1, L0_real_conditional_s1, L0_real_likelyC]
  norm_num

/-- In `s2` the speaker says the conditional with share `3/5`, *likely C* `2/5`, and `C` never
(Table 2(d)). -/
theorem S1_s2_conditional : (S1 .s2).real {.conditional} = 3 / 5 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s2, L0_real_conditional_s2, L0_real_likelyC]
  norm_num

theorem S1_s2_likelyC : (S1 .s2).real {.likelyC} = 2 / 5 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s2, L0_real_conditional_s2, L0_real_likelyC]
  norm_num

theorem S1_s2_C : (S1 .s2).real {.C} = 0 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s2, L0_real_conditional_s2, L0_real_likelyC]
  norm_num

/-- In `s3` the speaker says *likely C* with certainty (Table 2(d)). -/
theorem S1_s3_likelyC : (S1 .s3).real {.likelyC} = 1 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s3, L0_real_conditional_s3, L0_real_likelyC]
  norm_num

theorem S1_s3_conditional : (S1 .s3).real {.conditional} = 0 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s3, L0_real_conditional_s3, L0_real_likelyC]
  norm_num

theorem S1_s3_C : (S1 .s3).real {.C} = 0 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s3, L0_real_conditional_s3, L0_real_likelyC]
  norm_num

/-! ### The pragmatic listener, Table 2(e) -/

/-- The pragmatic listener of Table 2(e) inverts `S1` against the uniform prior. -/
noncomputable def L1 : Kernel Utt State := listener prior S1

theorem L1_real (u : Utt) (s : State) :
    (L1 u).real {s} = (S1 s).real {u} / ∑ s', (S1 s').real {u} := by
  rw [L1, listener_real_singleton, prior_real_singleton]
  simp_rw [prior_real_singleton, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (by norm_num)]

/-- Hearing the conditional, the listener puts `11/16` on `s2`, `5/16` on `s1` and nothing on
`s3` (Table 2(e)). -/
theorem L1_conditional_s2 : (L1 .conditional).real {.s2} = 11 / 16 := by
  rw [L1_real, sum_State, S1_s1_conditional, S1_s2_conditional,
    S1_s3_conditional]
  norm_num

theorem L1_conditional_s1 : (L1 .conditional).real {.s1} = 5 / 16 := by
  rw [L1_real, sum_State, S1_s1_conditional, S1_s2_conditional,
    S1_s3_conditional]
  norm_num

theorem L1_conditional_s3 : (L1 .conditional).real {.s3} = 0 := by
  rw [L1_real, sum_State, S1_s1_conditional, S1_s2_conditional,
    S1_s3_conditional]
  norm_num

/-- Hearing `C`, the listener identifies `s1` (Table 2(e)). -/
theorem L1_C_s1 : (L1 .C).real {.s1} = 1 := by
  rw [L1_real, sum_State, S1_s1_C, S1_s2_C, S1_s3_C]
  norm_num

/-- Hearing *likely C*, the listener puts `55/87` on `s3`, `22/87` on `s2` and `10/87` on `s1`
(Table 2(e)). -/
theorem L1_likelyC_s3 : (L1 .likelyC).real {.s3} = 55 / 87 := by
  rw [L1_real, sum_State, S1_s1_likelyC, S1_s2_likelyC, S1_s3_likelyC]
  norm_num

theorem L1_likelyC_s2 : (L1 .likelyC).real {.s2} = 22 / 87 := by
  rw [L1_real, sum_State, S1_s1_likelyC, S1_s2_likelyC, S1_s3_likelyC]
  norm_num

theorem L1_likelyC_s1 : (L1 .likelyC).real {.s1} = 10 / 87 := by
  rw [L1_real, sum_State, S1_s1_likelyC, S1_s2_likelyC, S1_s3_likelyC]
  norm_num

/-- Hearing *if A then C*, the listener prefers `s2` to `s1`. The speaker in `s1` would have
said *C* (`S1_s1_C`), so the conditional signals the state where it is the most informative
assertable utterance. -/
theorem l1_conditional_prefers_s2 :
    (L1 .conditional).real {.s1} < (L1 .conditional).real {.s2} := by
  rw [L1_conditional_s1, L1_conditional_s2]; norm_num

/-- Hearing *likely C*, the listener prefers `s3` to `s1`, since in `s1` and `s2` a stronger
utterance was available. -/
theorem l1_likelyC_prefers_s3 : (L1 .likelyC).real {.s1} < (L1 .likelyC).real {.s3} := by
  rw [L1_likelyC_s1, L1_likelyC_s3]; norm_num

/-! ### Conditional perfection

The paper derives conditional perfection, hearing *if A then C* as *if not A then not C*, as a
pragmatic inference, section 3. It is absent from the assertability semantics: at `s2` the
conditional is assertable while `P(¬C | ¬A) = 6/7` falls short of `θ`. -/

theorem perfection_not_semantic :
    Assertable θ .conditional State.s2.dist ∧ ¬ θ ≤ (State.s2.dist[|Aᶜ]).real Cᶜ := by
  simp only [Assertable, real_cond, real_A, real_A_inter_C, real_Ac, real_Ac_inter_Cc, State.cell,
    θ]
  norm_num

end GrusdtLassiterFranke2022
