module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Pragmatics.Probabilistic.Literal
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Core.Relation.ReflTransGen

/-!
# Beller and Gerstenberg (2025): Causation, Meaning, and Communication

Beller and Gerstenberg model causal language by counterfactual simulation. A candidate cause is a
whether-cause when the outcome would have been different without it, a how-cause when the
fine-grained outcome would have been different had it been changed, and a sufficient-cause when
it is a whether-cause once the alternative causes are removed, so that a preempting ball [counts
as a cause](##BellerGerstenberg2025.caused_preemption). "Affected", "enabled" and "caused" are
increasingly specific combinations of the aspects, and "made no difference" denies all three,
the denial of how-causation holding to a degree $\nu$. A speaker who saw the scenario [prefers
the most specific true expression](##BellerGerstenberg2025.speaker_s1_lt), and her listener
[takes "enabled" to mean that "caused" is false](##BellerGerstenberg2025.listener_enabled_lt).

## Implementation notes

* The aspects of the sample scenarios are Boolean and the speaker is the first-level speaker. The
  fitted model has graded whether- and sufficient-causation from noisy simulations, a second-level
  speaker, and softened movement and uniqueness conjuncts in "caused", which are left out.
* Sufficient-causation is whether-causation under an intervention that removes the alternative
  causes. The search for the alternatives and the requirement that the events of the contingency
  match the actual ones are left out.
* The two structural models are the launching and preemption scenarios as the paper describes
  them, with one equation for the ball's passage; the paper computes its aspects by physical
  simulation.

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

/-! ### Aspects and expressions -/

/-- The three aspects of causation. -/
inductive Aspect
  | whether
  | how
  | sufficient
  deriving DecidableEq, Repr, Fintype

/-- The four causal expressions offered to participants. -/
inductive Expression
  | noDifference
  | affected
  | enabled
  | caused
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Expression := ⊤
instance : DiscreteMeasurableSpace Expression := ⟨fun _ ↦ trivial⟩

variable {p : Aspect → Prop}

/-- An expression holds of the aspects `p` of a candidate cause: "affected" is `W ∨ H ∨ S` (4),
"enabled" is `W ∨ S` (5), "caused" is `H ∧ (W ∨ S)` (6), and "made no difference" is
`¬W ∧ ¬H ∧ ¬S` (7). -/
def Expression.Holds (p : Aspect → Prop) : Expression → Prop
  | .noDifference => ¬ p .whether ∧ ¬ p .how ∧ ¬ p .sufficient
  | .affected => p .whether ∨ p .how ∨ p .sufficient
  | .enabled => p .whether ∨ p .sufficient
  | .caused => p .how ∧ (p .whether ∨ p .sufficient)

instance [DecidablePred p] : DecidablePred (Expression.Holds p)
  | .noDifference => inferInstanceAs (Decidable (_ ∧ _))
  | .affected => inferInstanceAs (Decidable (_ ∨ _))
  | .enabled => inferInstanceAs (Decidable (_ ∨ _))
  | .caused => inferInstanceAs (Decidable (_ ∧ _))

-- the scale of implication: "caused" implies "enabled", which implies "affected"
theorem Expression.Holds.enabled (h : Expression.caused.Holds p) : Expression.enabled.Holds p :=
  h.2

theorem Expression.Holds.affected (h : Expression.enabled.Holds p) :
    Expression.affected.Holds p :=
  h.imp_right Or.inr

theorem holds_noDifference_iff :
    Expression.noDifference.Holds p ↔ ¬ Expression.affected.Holds p := by
  simp only [Expression.Holds, not_or]

-- each expression of the scale is true of strictly fewer aspect profiles than the one below it
theorem setOf_holds_ssubset :
    {p | Expression.caused.Holds p} ⊂ {p | Expression.enabled.Holds p} ∧
      {p | Expression.enabled.Holds p} ⊂ {p | Expression.affected.Holds p} :=
  ⟨Set.ssubset_iff_exists.2 ⟨fun _ h ↦ h.enabled, (· = .whether), by simp [Expression.Holds]⟩,
    Set.ssubset_iff_exists.2 ⟨fun _ h ↦ h.affected, (· = .how), by simp [Expression.Holds]⟩⟩

/-- The semantic value of an expression at the aspects `p`. The denial of how-causation in "made
no difference" is soft (7): a how-cause satisfies it to the degree `ν`. -/
def meaning (ν : ℝ) (p : Aspect → Prop) [DecidablePred p] : Expression → ℝ
  | .noDifference =>
    (if p .whether then 0 else 1) * (if p .how then ν else 1) * (if p .sufficient then 0 else 1)
  | u => if u.Holds p then 1 else 0

theorem meaning_zero [DecidablePred p] (u : Expression) :
    meaning 0 p u = if u.Holds p then 1 else 0 := by
  cases u <;> try rfl
  by_cases hw : p .whether <;> by_cases hh : p .how <;> by_cases hs : p .sufficient <;>
    simp [meaning, Expression.Holds, hw, hh, hs]

/-! ### The sample scenarios -/

/-- The paper's four sample scenarios: Michottean launching (1), double prevention (2), a ball
pushed along that was already headed for the gate (3), and a candidate that plays no part (4). -/
inductive Scenario
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Scenario := ⟨.s1⟩
instance : MeasurableSpace Scenario := ⊤
instance : DiscreteMeasurableSpace Scenario := ⟨fun _ ↦ trivial⟩

/-- The aspects the simulations compute for the candidate cause of each scenario (Table 1a). -/
def Scenario.aspects : Scenario → Finset Aspect
  | .s1 => {.whether, .how, .sufficient}
  | .s2 => {.whether, .sufficient}
  | .s3 => {.how}
  | .s4 => ∅

/-- The semantic value of an expression in a sample scenario (Table 1b). -/
def value (ν : ℝ) (u : Expression) (s : Scenario) : ℝ :=
  meaning ν (· ∈ s.aspects) u

-- Table 1b: "caused" is true of the first scenario alone, "enabled" of the first two, "affected"
-- of the first three, and the third satisfies "made no difference" to the degree ν.
example :
    (∀ s : Scenario, Expression.caused.Holds (· ∈ s.aspects) ↔ s = .s1) ∧
      (∀ s : Scenario, Expression.enabled.Holds (· ∈ s.aspects) ↔ s = .s1 ∨ s = .s2) ∧
      (∀ s : Scenario, Expression.affected.Holds (· ∈ s.aspects) ↔ s ≠ .s4) ∧
      ∀ s : Scenario, Expression.noDifference.Holds (· ∈ s.aspects) ↔ s = .s4 := by
  decide

example (ν : ℝ) : value ν .noDifference .s3 = ν ∧ value ν .noDifference .s4 = 1 := by
  simp [value, meaning, Scenario.aspects]

variable {ν α : ℝ}

private theorem sum_scenario (f : Scenario → ℝ) : ∑ s, f s = f .s1 + f .s2 + f .s3 + f .s4 := by
  rw [show (Finset.univ : Finset Scenario) = {.s1, .s2, .s3, .s4} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sum_expression (f : Expression → ℝ) :
    ∑ u, f u = f .noDifference + f .affected + f .enabled + f .caused := by
  rw [show (Finset.univ : Finset Expression) = {.noDifference, .affected, .enabled, .caused}
      from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem value_nonneg (hν : 0 ≤ ν) (u : Expression) (s : Scenario) : 0 ≤ value ν u s := by
  cases u <;> cases s <;> simp [value, meaning, Expression.Holds, Scenario.aspects, hν]

/-- The total semantic value of an expression over the sample scenarios. -/
def mass (ν : ℝ) : Expression → ℝ
  | .noDifference => ν + 1
  | .affected => 3
  | .enabled => 2
  | .caused => 1

theorem sum_value (ν : ℝ) (u : Expression) : ∑ s, value ν u s = mass ν u := by
  rw [sum_scenario]
  cases u <;> norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass]

theorem mass_pos (hν : 0 ≤ ν) (u : Expression) : 0 < mass ν u := by
  cases u <;> simp only [mass] <;> linarith

/-! ### The pragmatics module -/

/-- The literal listener (8) normalizes the semantic values of an expression over the
scenarios. -/
noncomputable abbrev literal (ν : ℝ) : Kernel Expression Scenario :=
  gradedListener (uniformOn Set.univ) (value ν)

/-- The first-level speaker (9) saw the scenario and chooses an expression in proportion to the
literal listener's probability of that scenario to the power `α`. -/
noncomputable abbrev speaker (ν α : ℝ) : Kernel Scenario Expression :=
  RSA.speaker α 0 (literal ν) Measure.dirac

/-- The pragmatic listener inverts the speaker at a uniform prior over the scenarios. -/
noncomputable abbrev listener (ν α : ℝ) : Kernel Expression Scenario :=
  RSA.listener (uniformOn Set.univ) (speaker ν α)

-- without the softening the literal listener is the one of the Boolean semantics
theorem literal_zero :
    literal 0 = literalListener (uniformOn Set.univ)
      fun u ↦ {s : Scenario | u.Holds (· ∈ s.aspects)} := by
  have h : value 0 = fun u ↦ {s : Scenario | u.Holds (· ∈ s.aspects)}.indicator 1 := by
    funext u s
    rw [value, meaning_zero]
    by_cases h : u.Holds (· ∈ s.aspects) <;> simp [h]
  rw [literal, h, gradedListener_indicator]

theorem literal_real (hν : 0 ≤ ν) (u : Expression) (s : Scenario) :
    (literal ν u).real {s} = value ν u s / mass ν u := by
  rw [← sum_value]
  exact gradedListener_uniformOn_real_singleton (value_nonneg hν u)
    (sum_value ν u ▸ mass_pos hν u) s

theorem speaker_real (hν : 0 ≤ ν) (hα : 0 ≤ α) (s : Scenario) (u : Expression) :
    (speaker ν α s).real {u} =
      (value ν u s / mass ν u) ^ α / ∑ u', (value ν u' s / mass ν u') ^ α := by
  rw [speaker_dirac_zero_real_singleton hα]
  simp_rw [← ENNReal.toReal_rpow, ← measureReal_def, literal_real hν]

-- at a fixed scenario the speaker ranks expressions by the literal listener's probability
theorem speaker_real_lt_iff (hν : 0 ≤ ν) (hα : 0 < α) (s : Scenario) (u u' : Expression) :
    (speaker ν α s).real {u} < (speaker ν α s).real {u'} ↔
      value ν u s / mass ν u < value ν u' s / mass ν u' := by
  have h (v : Expression) : 0 ≤ value ν v s / mass ν v :=
    div_nonneg (value_nonneg hν v s) (mass_pos hν v).le
  rw [speaker_dirac_real_singleton_lt_iff hα.le]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [ENNReal.rpow_lt_rpow_iff hα, ← ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    (measure_ne_top _ _), ← measureReal_def, ← measureReal_def, literal_real hν, literal_real hν]

theorem listener_real_lt_iff (u : Expression) (s s' : Scenario) :
    (listener ν α u).real {s} < (listener ν α u).real {s'} ↔
      (speaker ν α s).real {u} < (speaker ν α s').real {u} :=
  listener_uniformOn_real_lt_iff _ u s s'

/-! ### Table 1 -/

-- Table 1c at ν = 0.2: hearing "made no difference" the literal listener mostly infers the fourth
-- scenario and keeps some probability on the third.
theorem literal_noDifference :
    (literal (1 / 5) .noDifference).real {.s3} = 1 / 6 ∧
      (literal (1 / 5) .noDifference).real {.s4} = 5 / 6 := by
  rw [literal_real (by norm_num), literal_real (by norm_num)]
  norm_num [value, meaning, Scenario.aspects, mass]

-- Table 1c
theorem literal_enabled (hν : 0 ≤ ν) :
    (literal ν .enabled).real {.s1} = 1 / 2 ∧ (literal ν .enabled).real {.s3} = 0 := by
  rw [literal_real hν, literal_real hν]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass]

-- Table 1d, the first scenario
theorem speaker_s1 (hν : 0 ≤ ν) :
    (speaker ν 1 .s1).real {.caused} = 6 / 11 ∧ (speaker ν 1 .s1).real {.enabled} = 3 / 11 ∧
      (speaker ν 1 .s1).real {.affected} = 2 / 11 := by
  simp only [speaker_real hν zero_le_one, sum_expression, Real.rpow_one]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass]

-- Table 1d, the third scenario at ν = 0.2
theorem speaker_s3 :
    (speaker (1 / 5) 1 .s3).real {.affected} = 2 / 3 ∧
      (speaker (1 / 5) 1 .s3).real {.noDifference} = 1 / 3 := by
  simp only [speaker_real (ν := 1 / 5) (by norm_num) zero_le_one, sum_expression, Real.rpow_one]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass]

/-! ### Informativity and implicature -/

/-- At Michottean launching, where "caused", "enabled" and "affected" are all true, the speaker
prefers "caused" to "enabled" and "enabled" to "affected", at every positive rationality. -/
theorem speaker_s1_lt (hν : 0 ≤ ν) (hα : 0 < α) :
    (speaker ν α .s1).real {.enabled} < (speaker ν α .s1).real {.caused} ∧
      (speaker ν α .s1).real {.affected} < (speaker ν α .s1).real {.enabled} := by
  rw [speaker_real_lt_iff hν hα, speaker_real_lt_iff hν hα]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass]

/-- The softening is what lets the speaker call a how-cause that is neither a whether-cause nor a
sufficient-cause one that "made no difference". -/
theorem speaker_s3_noDifference_pos_iff (hν : 0 ≤ ν) (hα : 0 < α) :
    0 < (speaker ν α .s3).real {.noDifference} ↔ 0 < ν := by
  simp only [speaker_real hν hα.le, sum_expression]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass, Real.zero_rpow hα.ne']
  refine ⟨fun h ↦ hν.lt_of_ne fun h0 ↦ ?_, fun h ↦ ?_⟩
  · simp [← h0, Real.zero_rpow hα.ne'] at h
  · have hx := Real.rpow_pos_of_pos (div_pos h (by linarith : 0 < ν + 1)) α
    exact div_pos hx (add_pos hx (Real.rpow_pos_of_pos (by norm_num) α))

/-- Hearing "enabled", the pragmatic listener favours double prevention over Michottean
launching, where the speaker would have said "caused": the scalar implicature. -/
theorem listener_enabled_lt (hν : 0 ≤ ν) (hα : 0 < α) :
    (listener ν α .enabled).real {.s1} < (listener ν α .enabled).real {.s2} := by
  rw [listener_real_lt_iff]
  simp only [speaker_real hν hα.le, sum_expression]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass, Real.zero_rpow hα.ne']
  have h3 : (0 : ℝ) < (1 / 3) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have h2 : (0 : ℝ) < (1 / 2) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  exact div_lt_div_of_pos_left h2 (add_pos h3 h2) (by linarith)

/-- Hearing "affected", the pragmatic listener favours the scenario of which no stronger
expression is true. In the listener experiment participants favoured instead a scenario of which
"enabled" and "caused" were also true. -/
theorem listener_affected_lt (hν : 0 ≤ ν) (hν1 : ν < 1) (hα : 0 < α) :
    (listener ν α .affected).real {.s1} < (listener ν α .affected).real {.s3} ∧
      (listener ν α .affected).real {.s2} < (listener ν α .affected).real {.s3} := by
  simp only [listener_real_lt_iff, speaker_real hν hα.le, sum_expression]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass, Real.zero_rpow hα.ne']
  have h3 : (0 : ℝ) < (1 / 3) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have h2 : (0 : ℝ) < (1 / 2) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have h0 : 0 ≤ ν / (ν + 1) := div_nonneg hν (by linarith)
  have hlt : ν / (ν + 1) < 1 / 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have hx : (ν / (ν + 1)) ^ α < (1 / 2) ^ α := Real.rpow_lt_rpow h0 hlt hα
  have hpos := add_pos_of_nonneg_of_pos (Real.rpow_nonneg h0 α) h3
  exact ⟨div_lt_div_of_pos_left h3 hpos (by linarith),
    div_lt_div_of_pos_left h3 hpos (by linarith)⟩

theorem listener_caused_lt (hν : 0 ≤ ν) (hα : 0 < α) :
    (listener ν α .caused).real {.s2} < (listener ν α .caused).real {.s1} := by
  rw [listener_real_lt_iff]
  simp only [speaker_real hν hα.le, sum_expression]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass, Real.zero_rpow hα.ne']
  positivity

theorem listener_noDifference_lt (hν : 0 ≤ ν) (hα : 0 < α) :
    (listener ν α .noDifference).real {.s3} < (listener ν α .noDifference).real {.s4} := by
  rw [listener_real_lt_iff]
  simp only [speaker_real hν hα.le, sum_expression]
  norm_num [value, meaning, Expression.Holds, Scenario.aspects, mass, Real.zero_rpow hα.ne']
  have h3 : (0 : ℝ) < (1 / 3) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have hx : 0 ≤ (ν / (ν + 1)) ^ α := Real.rpow_nonneg (div_nonneg hν (by linarith)) α
  rw [div_self (Real.rpow_pos_of_pos (inv_pos.2 (by linarith)) α).ne', div_lt_one (by linarith)]
  linarith

/-! ### Aspects in a structural model -/

section Structural

open CausalModel

section Aspects

variable {U V β : Type*} [DecidableEq V] {γ : V → Type*} [∀ v, Nonempty (γ v)]
  (M : CausalModel U V γ) [M.IsAcyclic] (R : Finset V) (r : ∀ v : R, γ v) (u : U) (c : V)
  (removed changed : γ c) (e : V) (outcome : γ e → β)

/-- The cause `c` is a whether-cause of the outcome at `e` (1) when holding it at its `removed`
value gives a different outcome. -/
def IsWhetherCause : Prop :=
  outcome (M[c ← removed].solve u e) ≠ outcome (M.solve u e)

/-- The cause `c` is a how-cause (2) when holding it at a `changed` value gives `e` a different
value, the fine-grained outcome. -/
def IsHowCause : Prop :=
  M[c ← changed].solve u e ≠ M.solve u e

/-- The cause `c` is a sufficient-cause (3) when it is a whether-cause in the contingency that
holds the alternative causes `R` at the values `r` that remove them. -/
def IsSufficientCause : Prop :=
  IsWhetherCause (M.intervene R r) u c removed e outcome

-- with no alternative causes to remove, sufficient-causation is whether-causation
theorem isSufficientCause_empty (r : ∀ v : (∅ : Finset V), γ v) :
    IsSufficientCause M ∅ r u c removed e outcome ↔ IsWhetherCause M u c removed e outcome := by
  simp only [IsSufficientCause, intervene_empty]

/-- The aspects of `c` as a cause of the outcome at `e`. -/
def aspects : Aspect → Prop
  | .whether => IsWhetherCause M u c removed e outcome
  | .how => IsHowCause M u c changed e
  | .sufficient => IsSufficientCause M R r u c removed e outcome

end Aspects

/-- A ball of the scene as it was, removed from the scene, or changed by a small perturbation of
its initial position. -/
inductive Ball
  | actual
  | removed
  | changed
  deriving DecidableEq, Repr, Inhabited

/-- The scene holds the candidate cause, Ball A, a blue ball that may also reach the target, and
the target, Ball B. -/
inductive Object
  | ballA
  | blueBall
  | ballB
  deriving DecidableEq, Fintype, Repr

/-- The fine-grained outcome for Ball B: it misses the gate, passes through as it actually did, or
passes through at another place or time. -/
inductive Passage
  | misses
  | asActual
  | otherwise
  deriving DecidableEq, Repr, Inhabited

/-- The cause balls take a state and the target a passage. -/
abbrev Outcome : Object → Type
  | .ballA => Ball
  | .blueBall => Ball
  | .ballB => Passage

instance : ∀ v, Inhabited (Outcome v)
  | .ballA => inferInstanceAs (Inhabited Ball)
  | .blueBall => inferInstanceAs (Inhabited Ball)
  | .ballB => inferInstanceAs (Inhabited Passage)

instance : ∀ v, DecidableEq (Outcome v)
  | .ballA => inferInstanceAs (DecidableEq Ball)
  | .blueBall => inferInstanceAs (DecidableEq Ball)
  | .ballB => inferInstanceAs (DecidableEq Passage)

/-- Ball A knocks Ball B through the gate, at a slightly different place and time if it is
perturbed. Without Ball A the blue ball knocks Ball B through shortly afterwards, and without
either Ball B stays where it is. -/
def passage : Ball → Ball → Passage
  | .actual, _ => .asActual
  | .changed, _ => .otherwise
  | .removed, .removed => .misses
  | .removed, _ => .otherwise

/-- Ball B's passage depends on both balls. -/
def sceneEdges : Finset (Object × Object) := {(.ballA, .ballB), (.blueBall, .ballB)}

/-- The scene of the launching and preemption scenarios. The context settles whether the blue
ball is there. -/
def scene : CausalModel Ball Object Outcome where
  graph := ⟨fun w v ↦ (w, v) ∈ sceneEdges⟩
  eqn
    | .ballA => fun _ _ ↦ .actual
    | .blueBall => fun u _ ↦ u
    | .ballB => fun _ x ↦ passage (x .ballA) (x .blueBall)

instance : DecidableRel scene.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ sceneEdges))

instance : scene.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The aspects of Ball A as a cause of Ball B's going through the gate when the blue ball is in
the state `u`, the alternative cause to remove being the blue ball. -/
abbrev sceneAspects (u : Ball) : Aspect → Prop :=
  aspects scene {.blueBall} (uniqueElim Ball.removed) u .ballA .removed .changed .ballB
    (· = Passage.misses)

private theorem solve_scene (u : Ball) : scene.solve u .ballB = passage .actual u := by
  cases u <;> decide

private theorem solve_scene_ballA (a u : Ball) :
    scene[.ballA ← a].solve u .ballB = passage a u := by
  cases a <;> cases u <;> decide

private theorem solve_contingency (u : Ball) :
    scene[.blueBall ← Ball.removed].solve u .ballB = passage .actual .removed := by
  cases u <;> decide

private theorem solve_contingency_ballA (a u : Ball) :
    scene[.blueBall ← Ball.removed, .ballA ← a].solve u .ballB = passage a .removed := by
  cases a <;> cases u <;> decide

-- without the blue ball the scene is Michottean launching, with the aspects of Table 1a
theorem sceneAspects_removed (a : Aspect) : sceneAspects .removed a ↔ a ∈ Scenario.s1.aspects := by
  cases a <;>
    simp only [sceneAspects, aspects, IsWhetherCause, IsHowCause, IsSufficientCause, solve_scene,
      solve_scene_ballA, solve_contingency, solve_contingency_ballA, ne_eq, eq_iff_iff] <;>
    decide

/-- Under preemption Ball A is not a whether-cause, since the blue ball would have knocked Ball B
through the gate, but it is a how-cause and a sufficient-cause, so it "caused" Ball B to go
through the gate. -/
theorem caused_preemption :
    ¬ sceneAspects .actual .whether ∧ Expression.caused.Holds (sceneAspects .actual) := by
  simp only [Expression.Holds, sceneAspects, aspects, IsWhetherCause, IsHowCause,
    IsSufficientCause, solve_scene, solve_scene_ballA, solve_contingency, solve_contingency_ballA,
    ne_eq, eq_iff_iff]
  decide

end Structural

end BellerGerstenberg2025
