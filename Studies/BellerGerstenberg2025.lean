module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Causation.CausalModel.Defs
public import Linglib.Core.Relation.ReflTransGen

/-!
# Beller and Gerstenberg (2025): Causation, Meaning, and Communication

Beller and Gerstenberg model causal language by counterfactual simulation. A causal knowledge
module computes three aspects of causation, namely whether-causation (counterfactual necessity),
how-causation (a difference to the fine-grained outcome) and sufficient-causation
(whether-causation with the alternative causes removed). A semantics module defines "affected",
"enabled", "caused" and "made no difference" as logical combinations of the aspects, and a
pragmatics module chooses among the true expressions by informativity, as a rational speech act
speaker and listener after Frank and Goodman.

## Main results

* `caused_implies_enabled`, `enabled_implies_affected`: the expressions are ordered by
  specificity, the hierarchy behind the scale `causalScale`.
* `speaker_prefers_caused`, `speaker_prefers_enabled`: the speaker prefers the most informative
  true expression at every positive rationality.
* `listener_enabled_implicature`: hearing "enabled", the pragmatic listener favours the scenario
  where "caused" is false.
* `launch_ofModel`: Michottean launching, as a two-variable structural model, has the aspect
  profile of the first sample scenario.

## Implementation notes

* The speaker is the paper's first-level pragmatic speaker over Boolean aspects. The fitted
  model uses a second-level speaker over graded aspects from noisy simulations, with fitted
  noise, softening and optimality parameters.
* `listener_affected_prefers_howOnly` is the model's prediction for "affected", which the
  listener experiment did not bear out.

## References

* [beller-gerstenberg-2025]
* [gerstenberg-goodman-lagnado-tenenbaum-2021]
* [frank-goodman-2012]
* [halpern-pearl-2005]
-/

@[expose] public section

namespace BellerGerstenberg2025

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### Expressions and aspects -/

/-- The four causal expressions offered to participants. -/
inductive CausalExpression
  | caused
  | enabled
  | affected
  | madeNoDifference
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty CausalExpression := ⟨.caused⟩
instance : MeasurableSpace CausalExpression := ⊤
instance : DiscreteMeasurableSpace CausalExpression := ⟨fun _ ↦ trivial⟩

/-- An aspect profile records whether-causation `W` (1), how-causation `H` (2) and
sufficient-causation `S` (3), at Boolean values. -/
structure CausalWorld where
  whether : Bool
  how : Bool
  sufficient : Bool
  deriving DecidableEq, Repr

/-! ### Semantics -/

/-- The Boolean core of the semantics is `affected = W ∨ H ∨ S` (4), `enabled = W ∨ S` (5),
`caused = H ∧ (W ∨ S)` (6) without the softened movement and uniqueness conjuncts, and
`made no difference = ¬W ∧ ¬H ∧ ¬S` (7) with a hard negation. -/
def expressionMeaning (cw : CausalWorld) : CausalExpression → Prop
  | .affected => cw.whether ∨ cw.how ∨ cw.sufficient
  | .enabled => cw.whether ∨ cw.sufficient
  | .caused => cw.how ∧ (cw.whether ∨ cw.sufficient)
  | .madeNoDifference => ¬ cw.whether ∧ ¬ cw.how ∧ ¬ cw.sufficient

instance (cw : CausalWorld) : ∀ u, Decidable (expressionMeaning cw u)
  | .affected => inferInstanceAs (Decidable (_ ∨ _))
  | .enabled => inferInstanceAs (Decidable (_ ∨ _))
  | .caused => inferInstanceAs (Decidable (_ ∧ _))
  | .madeNoDifference => inferInstanceAs (Decidable (_ ∧ _))

theorem caused_implies_enabled (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .enabled :=
  And.right

theorem enabled_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .enabled → expressionMeaning cw .affected :=
  Or.imp_right Or.inr

theorem caused_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .affected :=
  enabled_implies_affected cw ∘ caused_implies_enabled cw

theorem madeNoDifference_iff_not_affected (cw : CausalWorld) :
    expressionMeaning cw .madeNoDifference ↔ ¬ expressionMeaning cw .affected := by
  simp only [expressionMeaning, not_or]

/-- The graded semantics softens the negation of how-causation in "made no difference", which a
how-cause that is neither a whether- nor a sufficient-cause satisfies to degree `ν` (7). -/
def gradedMeaning (cw : CausalWorld) (ν : ℚ) : CausalExpression → ℚ
  | .affected => if cw.whether || cw.how || cw.sufficient then 1 else 0
  | .enabled => if cw.whether || cw.sufficient then 1 else 0
  | .caused => if cw.how && (cw.whether || cw.sufficient) then 1 else 0
  | .madeNoDifference =>
    (if cw.whether then 0 else 1) * (if cw.how then ν else 1) * (if cw.sufficient then 0 else 1)

theorem gradedMeaning_zero (cw : CausalWorld) (u : CausalExpression) :
    gradedMeaning cw 0 u = if expressionMeaning cw u then 1 else 0 := by
  obtain ⟨w, h, s⟩ := cw
  cases u <;> cases w <;> cases h <;> cases s <;> simp [gradedMeaning, expressionMeaning]

/-! ### The sample scenarios -/

/-- The paper's four sample scenarios are Michottean launching, double prevention, a how-cause
pushing a ball already headed for the gate, and no interaction. -/
inductive Scenario
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Scenario := ⟨.s1⟩
instance : MeasurableSpace Scenario := ⊤
instance : DiscreteMeasurableSpace Scenario := ⟨fun _ ↦ trivial⟩

/-- The aspect values of the sample scenarios (Table 1a). -/
def Scenario.aspects : Scenario → CausalWorld
  | .s1 => ⟨true, true, true⟩
  | .s2 => ⟨true, false, true⟩
  | .s3 => ⟨false, true, false⟩
  | .s4 => ⟨false, false, false⟩

/-- Each expression's extension over the sample scenarios under the Boolean core. -/
def sem (u : CausalExpression) : Finset Scenario :=
  Finset.univ.filter fun s => expressionMeaning s.aspects u

-- Table 1b, Boolean columns: the extensions.
example :
    sem .caused = {.s1} ∧ sem .enabled = {.s1, .s2} ∧ sem .affected = {.s1, .s2, .s3} ∧
      sem .madeNoDifference = {.s4} := by
  decide

-- Table 1b, the softened cell: at ν = 0.2 the how-cause-only scenario weakly satisfies
-- "made no difference".
example : gradedMeaning Scenario.s3.aspects (1 / 5) .madeNoDifference = 1 / 5 := by
  norm_num [gradedMeaning, Scenario.aspects]

/-! ### The pragmatics module -/

/-- The literal listener is uniform on the scenarios an expression is true of. -/
noncomputable abbrev literal : Kernel CausalExpression Scenario :=
  RSA.listener (uniformOn Set.univ) (truthful fun u ↦ (sem u : Set Scenario))

/-- The first-level speaker knows the scenario and addresses the literal listener at
rationality `α`. -/
noncomputable abbrev speaker (α : ℝ) : Kernel Scenario CausalExpression :=
  RSA.speaker α 0 literal Measure.dirac

/-- The pragmatic listener inverts the speaker at a uniform prior over the scenarios. -/
noncomputable abbrev listener (α : ℝ) : Kernel CausalExpression Scenario :=
  RSA.listener (uniformOn Set.univ) (speaker α)

/-- Hearing "enabled", the literal listener finds the two enabling scenarios equally likely
(Table 1c). -/
theorem literal_enabled : literal .enabled {.s1} = 2⁻¹ ∧ literal .enabled {.s3} = 0 := by
  rw [listener_uniformOn_truthful_apply_singleton, listener_uniformOn_truthful_apply_singleton,
    ite_eq_left (by decide), ite_eq_right (by decide), show (sem .enabled).card = 2 from by decide]
  norm_num

/-- At Michottean launching the first-level speaker says "caused" with probability 6/11,
"enabled" with 3/11 and "affected" with 2/11 (Table 1d). -/
theorem speaker_s1 :
    (speaker 1 .s1).real {.caused} = 6 / 11 ∧ (speaker 1 .s1).real {.enabled} = 3 / 11 ∧
      (speaker 1 .s1).real {.affected} = 2 / 11 := by
  have h (u : CausalExpression) := speaker_uniformOn_dirac_real_singleton_divPowSum sem (k := 1)
    (D := 6) (w := .s1) (by decide +kernel) u
  simp only [Nat.cast_one] at h
  rw [h, h, h, show (profile sem Finset.univ .s1).divPowSum 6 1 = 11 from by decide +kernel,
    show (if Scenario.s1 ∈ sem .caused then (6 / (sem .caused).card) ^ 1 else 0) = 6 by decide,
    show (if Scenario.s1 ∈ sem .enabled then (6 / (sem .enabled).card) ^ 1 else 0) = 3 by decide,
    show (if Scenario.s1 ∈ sem .affected then (6 / (sem .affected).card) ^ 1 else 0) = 2 by decide]
  norm_num

/-- At double prevention the first-level speaker says "enabled" with probability 3/5 and
"affected" with 2/5, and never "caused" (Table 1d). -/
theorem speaker_s2 :
    (speaker 1 .s2).real {.enabled} = 3 / 5 ∧ (speaker 1 .s2).real {.affected} = 2 / 5 ∧
      (speaker 1 .s2).real {.caused} = 0 := by
  have h (u : CausalExpression) := speaker_uniformOn_dirac_real_singleton_divPowSum sem (k := 1)
    (D := 6) (w := .s2) (by decide +kernel) u
  simp only [Nat.cast_one] at h
  rw [h, h, h, show (profile sem Finset.univ .s2).divPowSum 6 1 = 5 from by decide +kernel,
    show (if Scenario.s2 ∈ sem .enabled then (6 / (sem .enabled).card) ^ 1 else 0) = 3 by decide,
    show (if Scenario.s2 ∈ sem .affected then (6 / (sem .affected).card) ^ 1 else 0) = 2 by decide,
    show (if Scenario.s2 ∈ sem .caused then (6 / (sem .caused).card) ^ 1 else 0) = 0 by decide]
  norm_num

/-! ### Informativity and implicature -/

/-- At Michottean launching the speaker prefers "caused" to "enabled" and "enabled" to
"affected", at every positive rationality. -/
theorem speaker_prefers_caused {α : ℝ} (hα : 0 < α) :
    (speaker α .s1).real {.enabled} < (speaker α .s1).real {.caused} ∧
      (speaker α .s1).real {.affected} < (speaker α .s1).real {.enabled} :=
  ⟨speaker_uniformOn_dirac_real_singleton_lt_of_card_lt sem hα (by decide) (by decide) (by decide),
    speaker_uniformOn_dirac_real_singleton_lt_of_card_lt sem hα (by decide) (by decide)
      (by decide)⟩

/-- At double prevention, where "caused" is false, the speaker prefers "enabled" to
"affected" at every positive rationality. -/
theorem speaker_prefers_enabled {α : ℝ} (hα : 0 < α) :
    (speaker α .s2).real {.affected} < (speaker α .s2).real {.enabled} :=
  speaker_uniformOn_dirac_real_singleton_lt_of_card_lt sem hα (by decide) (by decide) (by decide)

theorem listener_caused_identifies {α : ℝ} (hα : 0 < α) :
    (listener α .caused).real {.s2} < (listener α .caused).real {.s1} :=
  listener_speaker_uniformOn_real_singleton_lt_of_strictDominates sem hα (by decide +kernel)

theorem listener_enabled_implicature {α : ℝ} (hα : 0 < α) :
    (listener α .enabled).real {.s1} < (listener α .enabled).real {.s2} :=
  listener_speaker_uniformOn_real_singleton_lt_of_strictDominates sem hα (by decide +kernel)

/-- Hearing "affected", the pragmatic listener favours the how-cause-only scenario, where
no stronger expression is true, over Michottean launching. The listener experiment found
the opposite preference for the analogous pair, the case the paper singles out as the
model's failure. -/
theorem listener_affected_prefers_howOnly {α : ℝ} (hα : 0 < α) :
    (listener α .affected).real {.s1} < (listener α .affected).real {.s3} :=
  listener_speaker_uniformOn_real_singleton_lt_of_strictDominates sem hα (by decide +kernel)

theorem listener_noDifference_identifies {α : ℝ} (hα : 0 < α) :
    (listener α .madeNoDifference).real {.s3} < (listener α .madeNoDifference).real {.s4} :=
  listener_speaker_uniformOn_real_singleton_lt_of_strictDominates sem hα (by decide +kernel)

/-! ### The Horn scale -/

/-- The scale ⟨affected, enabled, caused⟩, weakest to strongest. -/
def causalScale : Fin 3 → CausalExpression := ![.affected, .enabled, .caused]

/-- The scale is a Horn scale. Its meanings are strictly antitone in scale position, each member
entailing the weaker ones and not conversely, the specificity hierarchy
`caused_implies_enabled` and `enabled_implies_affected`. -/
theorem causalScale_strictAnti :
    StrictAnti λ i => {cw | expressionMeaning cw (causalScale i)} := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i
  · show ({cw | expressionMeaning cw .enabled} : Set CausalWorld) <
      {cw | expressionMeaning cw .affected}
    exact LE.le.ssubset_of_not_superset (λ cw h => enabled_implies_affected cw h)
      (Set.not_subset.2 ⟨⟨false, true, false⟩, by decide, by decide⟩)
  · show ({cw | expressionMeaning cw .caused} : Set CausalWorld) <
      {cw | expressionMeaning cw .enabled}
    exact LE.le.ssubset_of_not_superset (λ cw h => caused_implies_enabled cw h)
      (Set.not_subset.2 ⟨⟨true, false, false⟩, by decide, by decide⟩)

/-! ### Aspects from a structural model -/

section Structural

/-- The variables of a two-event structural model are the candidate cause and the outcome. -/
inductive Var
  | cause
  | effect
  deriving DecidableEq, Fintype, Repr

/-- The outcome depends on the candidate cause alone. -/
def launchEdges : Finset (Var × Var) := {(.cause, .effect)}

/-- The context settles whether the candidate cause occurs. -/
structure LaunchContext where
  cause : Bool

/-- In Michottean launching the outcome takes the candidate cause's value. -/
def launch : CausalModel LaunchContext Var fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ launchEdges⟩
  eqn
    | .cause => fun u _ ↦ u.cause
    | .effect => fun _ x ↦ x .cause

instance : DecidableRel launch.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ launchEdges))

instance : launch.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

open CausalModel

variable {U V : Type*} [Fintype V] [DecidableEq V]

/-- The aspect profile of `cause → effect` in the context `u` of a deterministic model. `W` is
whether-causation (1), that had the cause been absent the effect would not have been present. `H` is
a direct law, and `S` is sufficient-causation (3), whether-causation under the intervention
`removed` that takes the alternative causes away. -/
noncomputable def CausalWorld.ofModel (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
    [DecidableRel M.graph.Adj] (removed : V → Flat Bool) (u : U) (cause effect : V) :
    CausalWorld where
  whether := decide (M.solve [cause ← false] u effect ≠ true)
  how := decide (M.graph.Adj cause effect)
  sufficient := decide (M.solve (Function.update removed cause ↑false) u effect ≠ true)

theorem launch_ofModel :
    CausalWorld.ofModel launch ⊥ ⟨true⟩ .cause .effect = Scenario.s1.aspects := by
  decide

end Structural

end BellerGerstenberg2025
