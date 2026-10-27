/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Distributions.PolyaUrn
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Core.Probability.UniformOn
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Erk and Herbelot (2024): How to Marry a Star: Probabilistic Constraints for Meaning in Context

This file formalizes [erk-herbelot-2024]'s situation description systems, which model utterance
understanding as Bayesian inference over the concepts underlying the words of a sentence,
constrained locally by selectional preferences and globally by scenarios. In the graphical model
(§5.1, Figure 5; the sampling process in Appendix A) a scenario mix is drawn from a symmetric
Dirichlet with concentration `α`, one scenario per concept node is drawn from the mix, one
concept per node is drawn from its scenario's concept distribution, for a role filler from the
Product of Experts of that distribution with the role's selectional constraint (p. 570), and
each node emits its condition label deterministically. `SDS.nodePosterior` is the posterior over
the concept at one node given the labels of all nodes, mathlib's posterior kernel `κ†μ` of the
deterministic label kernel against the joint, pushed forward to the node, and
`SDS.nodePosterior_apply` is the closed form the paper estimates by WebPPL sampling, a ratio of
sums over scenario assignments of per-node fibre masses. The paper's two sentences follow with
their posteriors as functions of `α`. In *a player was holding a bat* (§5.1, Table 1) the
*stick* sense of *bat* has posterior `(α + 1) / (2α + 1)`, which strengthens as `α` decreases
(p. 571); in *an astronomer married a star* (§5.2, Table 2) the *person* sense has posterior
`105α / (115α + 8)`, so the *sun* sense strengthens as `α` decreases (p. 572); and on the *star*
node the selectional constraint prefers STAR-PERSON while the STARGAZING scenario prefers
STAR-SUN, the conflict of Figure 6.

## Implementation notes

* The Dirichlet prior on the scenario mix is integrated out into the Pólya-urn law of the
  per-node scenario draws, `polyaUrn`.
* Ingredients the paper leaves unspecified are set as follows: HOLD-AGENT and MARRY-AGENT get
  the same constraint as the corresponding theme role, and both cancel since the agent concept
  is observed; MARRY-THEME gives MARRY itself weight `0`, the three stated values already summing
  to `1`.

## TODO

* The exact posteriors against the paper's WebPPL estimates from 2000 samples: the astronomer
  rows, `105/131 ≈ 0.80` and `7/13 ≈ 0.54` against `0.82` and `0.57`, are within sampling
  error; the bat rows, `3/4` and `11/12` against `0.82` and `0.96`, are not, and the paper does
  not describe its WebPPL model in enough detail to locate the difference.

## References

* [erk-herbelot-2024]
-/

@[expose] public section

namespace ErkHerbelot2024

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A situation description system: the Dirichlet prior on the scenario mix (as a Pólya urn
over scenarios), the per-scenario concept distributions, and the per-role selectional
constraints. -/
structure SDS (S C R : Type*) [MeasurableSpace C] where
  /-- The parameters of the scenario-mix prior `Dirichlet(α, …, α)`, the weights of the Pólya urn
  it integrates out to. -/
  prior : S → ℝ
  /-- The Dirichlet parameters are positive. -/
  prior_pos : ∀ s, 0 < prior s
  /-- `P(c | s)`: the concepts a scenario makes available. -/
  scenario : S → Measure C
  /-- `P(c | r)`: the selectional constraint of a semantic role. -/
  selectional : R → Measure C

namespace SDS

section Node

variable {S C R : Type*} [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace R]
  [Countable S] [MeasurableSingletonClass S] [Countable R] [MeasurableSingletonClass R]
  [Fintype C] [MeasurableSingletonClass C] (m : SDS S C R)

/-- Product of Experts (p. 570): the role-filler distribution for scenario `s` and role `r` is
the normalized pointwise product of `scenario s` and `selectional r`. When the two share no
concept (fn 10) the row is the zero measure. -/
noncomputable def poe : Kernel (S × R) C :=
  Kernel.ofWeights λ p c => m.scenario p.1 {c} * m.selectional p.2 {c}

instance : IsFiniteKernel m.poe := inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The concept distribution at one node: a top-level concept (no role) draws from its scenario
alone; a role filler draws from the Product of Experts (Appendix A). -/
noncomputable def emission (s : S) : Option R → Measure C
  | none => m.scenario s
  | some r => m.poe (s, r)

instance [∀ s, IsProbabilityMeasure (m.scenario s)] (s : S) :
    ∀ o : Option R, IsFiniteMeasure (m.emission s o)
  | none => inferInstanceAs (IsFiniteMeasure (m.scenario s))
  | some r => inferInstanceAs (IsFiniteMeasure (m.poe (s, r)))

omit [MeasurableSingletonClass C] in
theorem emission_univ_le_one [∀ s, IsProbabilityMeasure (m.scenario s)] (s : S) :
    ∀ o : Option R, m.emission s o Set.univ ≤ 1
  | none => (measure_univ (μ := m.scenario s)).le
  | some _ => Kernel.ofWeights_apply_univ_le_one _ _

end Node

section Sentence

variable {S C R L : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [MeasurableSpace R] [Countable R] [MeasurableSingletonClass R]
  [MeasurableSpace L] [MeasurableSingletonClass L]
  (m : SDS S C R) [∀ s, IsProbabilityMeasure (m.scenario s)] {n : ℕ}

omit [Nonempty C] [Fintype C] [MeasurableSingletonClass C]
  [∀ s, IsProbabilityMeasure (m.scenario s)] in
instance (n : ℕ) : IsProbabilityMeasure (polyaUrn m.prior n) :=
  isProbabilityMeasure_polyaUrn m.prior_pos n

omit [DecidableEq S] [Nonempty S] [Nonempty C] in
/-- The concept nodes of an `n`-node sentence with roles `ρ`, conditionally independent given
their scenarios. -/
noncomputable def emissions (ρ : Fin n → Option R) : Kernel (Fin n → S) (Fin n → C) :=
  Kernel.ofFunOfCountable λ s => Measure.pi λ i => m.emission (s i) (ρ i)

omit [DecidableEq S] [Nonempty S] [Nonempty C] [MeasurableSingletonClass C]
  [∀ s, IsProbabilityMeasure (m.scenario s)] in
theorem emissions_apply (ρ : Fin n → Option R) (s : Fin n → S) :
    m.emissions ρ s = Measure.pi λ i => m.emission (s i) (ρ i) := rfl

omit [DecidableEq S] [Nonempty S] [Nonempty C] in
instance (ρ : Fin n → Option R) : IsFiniteKernel (m.emissions ρ) :=
  ⟨⟨1, ENNReal.one_lt_top, λ s => by
    rw [emissions_apply, Measure.pi_univ]
    exact Finset.prod_le_one λ i _ => m.emission_univ_le_one _ _⟩⟩

omit [Nonempty C] in
/-- The joint law of scenario and concept assignments (Figure 5, nodes 1–9). -/
noncomputable def joint (ρ : Fin n → Option R) : Measure ((Fin n → S) × (Fin n → C)) :=
  polyaUrn m.prior n ⊗ₘ m.emissions ρ

omit [Nonempty C] in
instance (ρ : Fin n → Option R) : IsFiniteMeasure (m.joint ρ) :=
  inferInstanceAs (IsFiniteMeasure (_ ⊗ₘ _))

/-- Each node emits its condition label deterministically (Figure 5, nodes 10–14). -/
noncomputable def observe (S : Type*) [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (label : C → L) (n : ℕ) :
    Kernel ((Fin n → S) × (Fin n → C)) (Fin n → L) :=
  Kernel.deterministic (λ ω i => label (ω.2 i)) (measurable_of_countable _)

instance (label : C → L) (n : ℕ) : IsFiniteKernel (observe S label n) :=
  inferInstanceAs (IsFiniteKernel (Kernel.deterministic _ _))

/-- The posterior over the concept at node `t`, given the labels `x` of all nodes. -/
noncomputable def nodePosterior (label : C → L) (ρ : Fin n → Option R) (x : Fin n → L)
    (t : Fin n) : Measure C :=
  (((observe S label n)†(m.joint ρ)) x).map λ ω => ω.2 t

variable (label : C → L) (ρ : Fin n → Option R) (x : Fin n → L)

omit [Nonempty S] [Nonempty C] in
theorem joint_apply_univ_prod_pi (T : Fin n → Set C) :
    m.joint ρ (Set.univ ×ˢ Set.pi Set.univ T) =
      ∑ s, polyaUrn m.prior n {s} * ∏ i, m.emission (s i) (ρ i) (T i) := by
  rw [joint, Measure.compProd_apply_prod .univ .of_discrete, Measure.restrict_univ,
    lintegral_fintype]
  exact Finset.sum_congr rfl λ s _ => by rw [emissions_apply, Measure.pi_pi, mul_comm]

theorem nodePosterior_apply (t : Fin n) (c : C)
    (hx : ∑ s, polyaUrn m.prior n {s} * ∏ i, m.emission (s i) (ρ i) (label ⁻¹' {x i}) ≠ 0) :
    m.nodePosterior label ρ x t {c} =
      (∑ s, polyaUrn m.prior n {s} *
          ∏ i, m.emission (s i) (ρ i) {c' | label c' = x i ∧ (i = t → c' = c)}) /
        ∑ s, polyaUrn m.prior n {s} * ∏ i, m.emission (s i) (ρ i) (label ⁻¹' {x i}) := by
  have hF : (λ ω : (Fin n → S) × (Fin n → C) => λ i => label (ω.2 i)) ⁻¹' {x} =
      Set.univ ×ˢ Set.pi Set.univ λ i => label ⁻¹' {x i} := by
    ext ⟨s, c⟩; simp [funext_iff]
  have hE : (Set.univ ×ˢ Set.pi Set.univ λ i => label ⁻¹' {x i}) ∩
      ((λ ω : (Fin n → S) × (Fin n → C) => ω.2 t) ⁻¹' {c}) =
      Set.univ ×ˢ Set.pi Set.univ λ i => {c' | label c' = x i ∧ (i = t → c' = c)} := by
    ext ⟨s, c'⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact ⟨λ ⟨h₁, h₂⟩ i => ⟨h₁ i, λ hi => hi ▸ h₂⟩, λ h => ⟨λ i => (h i).1, (h t).2 rfl⟩⟩
  rw [nodePosterior, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton c)]
  unfold observe
  rw [posterior_deterministic_eq_cond _ _ (by rwa [hF, joint_apply_univ_prod_pi]), hF,
    ProbabilityTheory.cond_apply
      (s := Set.univ ×ˢ Set.pi Set.univ λ i => label ⁻¹' {x i}) .of_discrete, hE,
    joint_apply_univ_prod_pi, joint_apply_univ_prod_pi, ENNReal.div_eq_inv_mul]

omit [Nonempty C] [MeasurableSingletonClass C] in
theorem sum_toReal (T : Fin n → Set C) :
    (∑ s, polyaUrn m.prior n {s} * ∏ i, m.emission (s i) (ρ i) (T i)).toReal =
      ∑ s, polyaUrnProb m.prior (countVec s) * ∏ i, (m.emission (s i) (ρ i)).real (T i) := by
  rw [ENNReal.toReal_sum λ s _ =>
    ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.prod_ne_top λ i _ => measure_ne_top _ _)]
  refine Finset.sum_congr rfl λ s _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, polyaUrn_singleton m.prior_pos,
    ENNReal.toReal_ofReal (polyaUrnProb_pos m.prior_pos _).le]
  rfl

end Sentence

end SDS

/-! ### Evaluation helpers -/

private theorem sum_fin_three {S M : Type*} [Fintype S] [AddCommMonoid M]
    (f : (Fin 3 → S) → M) : ∑ s, f s = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
  rw [← (Fin.consEquiv λ _ => S).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl λ a _ => ?_
  rw [← (Fin.consEquiv λ _ => S).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl λ b _ => ?_
  rw [← (Fin.consEquiv λ _ => S).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl λ c _ => ?_
  rw [Fintype.sum_unique]
  exact congrArg f (by funext i; fin_cases i <;> rfl)

/-! ### *A player was holding a bat* (§5.1, Figure 5, Table 1) -/

/-- The concept inventory (p. 569). -/
inductive BatConcept
  | BALL | BAT_ANIMAL | HOLD | BAT_STICK | CANDLE | CAT | PLAYER | STONE | VAMPIRE
  deriving Fintype, DecidableEq

/-- The two scenarios (p. 569). -/
inductive BatScenario
  | BASEBALL | GOTHIC
  deriving Fintype, DecidableEq

/-- The semantic roles of HOLD (p. 569). -/
inductive BatRole
  | holdAgent | holdTheme
  deriving Fintype, DecidableEq

/-- Condition labels: one word form per concept; *bat* is shared by its two senses. -/
inductive BatLabel
  | ball | bat | hold | candle | cat | player | stone | vampire
  deriving Fintype, DecidableEq

instance : MeasurableSpace BatConcept := ⊤
instance : DiscreteMeasurableSpace BatConcept := ⟨λ _ => trivial⟩
instance : MeasurableSpace BatScenario := ⊤
instance : DiscreteMeasurableSpace BatScenario := ⟨λ _ => trivial⟩
instance : MeasurableSpace BatRole := ⊤
instance : DiscreteMeasurableSpace BatRole := ⟨λ _ => trivial⟩
instance : MeasurableSpace BatLabel := ⊤
instance : DiscreteMeasurableSpace BatLabel := ⟨λ _ => trivial⟩
instance : Nonempty BatConcept := ⟨.HOLD⟩
instance : Nonempty BatScenario := ⟨.BASEBALL⟩

/-- The condition label of each concept (Figure 5, nodes 10–14). -/
def batLabel : BatConcept → BatLabel
  | .BALL => .ball | .BAT_ANIMAL => .bat | .HOLD => .hold | .BAT_STICK => .bat
  | .CANDLE => .candle | .CAT => .cat | .PLAYER => .player | .STONE => .stone
  | .VAMPIRE => .vampire

/-- The concepts of each scenario: BASEBALL and GOTHIC give equal probability to five concepts
each and zero to the rest (p. 569). -/
def batScenario : BatScenario → Finset BatConcept
  | .BASEBALL => {.BALL, .BAT_STICK, .HOLD, .PLAYER, .STONE}
  | .GOTHIC => {.BAT_ANIMAL, .CANDLE, .CAT, .HOLD, .VAMPIRE}

/-- HOLD-THEME: `0` for HOLD and `0.125` for each of the eight concrete objects (p. 569).
HOLD-AGENT, which the paper leaves unspecified, is set the same way. -/
def holdFiller : Finset BatConcept :=
  {.BALL, .BAT_ANIMAL, .BAT_STICK, .CANDLE, .CAT, .PLAYER, .STONE, .VAMPIRE}

/-- The bat-sentence system with Dirichlet concentration `α`. -/
noncomputable def batSDS (α : ℝ) (hα : 0 < α) : SDS BatScenario BatConcept BatRole where
  prior _ := α
  prior_pos _ := hα
  scenario s := uniformOn ↑(batScenario s)
  selectional _ := uniformOn ↑holdFiller

instance (α : ℝ) (hα : 0 < α) (s : BatScenario) :
    IsProbabilityMeasure ((batSDS α hα).scenario s) :=
  isProbabilityMeasure_uniformOn (Finset.finite_toSet _)
    (Finset.coe_nonempty.mpr (by cases s <;> decide))

/-- Node roles (Figure 5): the verb node has no role; *player* fills HOLD-AGENT and *bat*
HOLD-THEME. -/
def batRoles : Fin 3 → Option BatRole := ![none, some .holdAgent, some .holdTheme]

/-- The observed labels `hold(_)`, `player(_)`, `bat(_)` (Figure 5, nodes 12, 10, 14). -/
def batLabels : Fin 3 → BatLabel := ![.hold, .player, .bat]

@[simp] theorem batSDS_prior (α : ℝ) (hα : 0 < α) : (batSDS α hα).prior = fun _ ↦ α := rfl

@[simp] theorem batSDS_scenario (α : ℝ) (hα : 0 < α) (s : BatScenario) :
    (batSDS α hα).scenario s = uniformOn ↑(batScenario s) := rfl

theorem batSDS_poe (α : ℝ) (hα : 0 < α) (s : BatScenario) (r : BatRole) :
    (batSDS α hα).poe (s, r) = uniformOn (↑(batScenario s ∩ holdFiller) : Set BatConcept) :=
  Kernel.ofWeights_uniformOn_mul_uniformOn (λ p : BatScenario × BatRole => batScenario p.1)
    (λ _ => holdFiller) (s, r)

private theorem sum_batScenario {M : Type*} [AddCommMonoid M] (f : BatScenario → M) :
    ∑ s, f s = f .BASEBALL + f .GOTHIC := by
  rw [show (Finset.univ : Finset BatScenario) = {.BASEBALL, .GOTHIC} by decide,
    Finset.sum_pair (by decide)]

private theorem uniformOn_real_preimage {C L : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [DecidableEq C] [Fintype C] [DecidableEq L] (A : Finset C)
    (f : C → L) (y : L) :
    (uniformOn ↑A).real (f ⁻¹' {y}) = ((A.filter (f · = y)).card : ℝ) / A.card :=
  uniformOn_finset_real_setOf A (f · = y)

private theorem countVec_vecCons {S : Type*} [DecidableEq S] {N : ℕ} (c : S) (seq : Fin N → S) :
    countVec (Matrix.vecCons c seq) = Function.update (countVec seq) c (countVec seq c + 1) :=
  countVec_cons c seq

private theorem polyaUrnProb_countVec_vecCons {S : Type*} [Fintype S] [DecidableEq S]
    (θ : S → ℝ) (c : S) {N : ℕ} (seq : Fin N → S) :
    polyaUrnProb θ (countVec (Matrix.vecCons c seq)) =
      polyaUrnProb θ (countVec seq) * polyaUrnPredictive θ (countVec seq) c :=
  polyaUrnProb_countVec_cons θ c seq

private theorem bat_cards :
    ((batScenario .BASEBALL).filter (batLabel · = .hold)).card = 1 ∧
    ((batScenario .GOTHIC).filter (batLabel · = .hold)).card = 1 ∧
    ((batScenario .BASEBALL ∩ holdFiller).filter (batLabel · = .player)).card = 1 ∧
    ((batScenario .GOTHIC ∩ holdFiller).filter (batLabel · = .player)).card = 0 ∧
    (batScenario .BASEBALL).card = 5 ∧ (batScenario .GOTHIC).card = 5 ∧
    (batScenario .BASEBALL ∩ holdFiller).card = 4 ∧
    (batScenario .GOTHIC ∩ holdFiller).card = 4 := by decide

private theorem bat_cards_den :
    ((batScenario .BASEBALL ∩ holdFiller).filter (batLabel · = .bat)).card = 1 ∧
    ((batScenario .GOTHIC ∩ holdFiller).filter (batLabel · = .bat)).card = 1 := by decide

private theorem bat_cards_num :
    ((batScenario .BASEBALL ∩ holdFiller).filter
      (λ c => batLabel c = .bat ∧ c = .BAT_STICK)).card = 1 ∧
    ((batScenario .GOTHIC ∩ holdFiller).filter
      (λ c => batLabel c = .bat ∧ c = .BAT_STICK)).card = 0 := by decide

private theorem bat_den (α : ℝ) (hα : 0 < α) :
    (∑ s, polyaUrn (batSDS α hα).prior 3 {s} *
      ∏ i, (batSDS α hα).emission (s i) (batRoles i) (batLabel ⁻¹' {batLabels i})).toReal =
      1 / 160 := by
  rw [SDS.sum_toReal, sum_fin_three]
  simp only [sum_batScenario, Fin.prod_univ_three, batRoles, batLabels, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, SDS.emission,
    batSDS_poe, batSDS_scenario, batSDS_prior, polyaUrnProb_countVec_vecCons,
    uniformOn_real_preimage,
    bat_cards, bat_cards_den]
  simp +decide only [countVec_vecCons, countVec_zero, polyaUrnProb_zero,
    polyaUrnPredictive, Pi.zero_apply, Function.update_apply,
    sum_batScenario, ↓reduceIte]
  push_cast
  field_simp
  ring

private theorem bat_num (α : ℝ) (hα : 0 < α) :
    (∑ s, polyaUrn (batSDS α hα).prior 3 {s} * ∏ i, (batSDS α hα).emission (s i) (batRoles i)
      {c' | batLabel c' = batLabels i ∧ (i = 2 → c' = .BAT_STICK)}).toReal =
      (α + 1) / (160 * (2 * α + 1)) := by
  rw [SDS.sum_toReal, sum_fin_three]
  simp +decide only [sum_batScenario, Fin.prod_univ_three, batRoles, batLabels,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, SDS.emission, batSDS_poe, batSDS_scenario, batSDS_prior,
    polyaUrnProb_countVec_vecCons, false_implies, true_implies, and_true,
    uniformOn_finset_real_setOf, bat_cards, bat_cards_num]
  simp +decide only [countVec_vecCons, countVec_zero, polyaUrnProb_zero,
    polyaUrnPredictive, Pi.zero_apply, Function.update_apply,
    sum_batScenario, ↓reduceIte]
  push_cast
  field_simp
  ring

-- Table 1
theorem batStick_real (α : ℝ) (hα : 0 < α) :
    ((batSDS α hα).nodePosterior batLabel batRoles batLabels 2).real {.BAT_STICK} =
      (α + 1) / (2 * α + 1) := by
  have hden : ∑ s, polyaUrn (batSDS α hα).prior 3 {s} *
      ∏ i, (batSDS α hα).emission (s i) (batRoles i) (batLabel ⁻¹' {batLabels i}) ≠ 0 := by
    intro h
    have := bat_den α hα
    rw [h, ENNReal.toReal_zero] at this
    norm_num at this
  rw [measureReal_def, SDS.nodePosterior_apply _ _ _ _ _ _ hden, ENNReal.toReal_div, bat_num,
    bat_den]
  field_simp

-- Table 1
theorem batStick_half :
    ((batSDS (1 / 2) (by norm_num)).nodePosterior batLabel batRoles batLabels 2).real
      {.BAT_STICK} = 3 / 4 := by
  rw [batStick_real]; norm_num

-- Table 1
theorem batStick_tenth :
    ((batSDS (1 / 10) (by norm_num)).nodePosterior batLabel batRoles batLabels 2).real
      {.BAT_STICK} = 11 / 12 := by
  rw [batStick_real]; norm_num

-- p. 571
theorem batStick_strictAnti {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ((batSDS β (hα.trans hαβ)).nodePosterior batLabel batRoles batLabels 2).real {.BAT_STICK} <
      ((batSDS α hα).nodePosterior batLabel batRoles batLabels 2).real {.BAT_STICK} := by
  have hβ : 0 < β := hα.trans hαβ
  rw [batStick_real, batStick_real, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### *An astronomer married a star* (§5.2, Figure 6, Table 2) -/

/-- The concept inventory (p. 571). -/
inductive StarConcept
  | ASTRONOMER | STAR_PERSON | STAR_SUN | MARRY
  deriving Fintype, DecidableEq

/-- The two scenarios (p. 571). -/
inductive StarScenario
  | STARGAZING | STAGE
  deriving Fintype, DecidableEq

/-- The semantic roles of MARRY (p. 571). -/
inductive StarRole
  | marryAgent | marryTheme
  deriving Fintype, DecidableEq

/-- Condition labels; *star* is shared by its two senses. -/
inductive StarLabel
  | astronomer | star | marry
  deriving Fintype, DecidableEq

instance : MeasurableSpace StarConcept := ⊤
instance : DiscreteMeasurableSpace StarConcept := ⟨λ _ => trivial⟩
instance : MeasurableSpace StarScenario := ⊤
instance : DiscreteMeasurableSpace StarScenario := ⟨λ _ => trivial⟩
instance : MeasurableSpace StarRole := ⊤
instance : DiscreteMeasurableSpace StarRole := ⟨λ _ => trivial⟩
instance : MeasurableSpace StarLabel := ⊤
instance : DiscreteMeasurableSpace StarLabel := ⟨λ _ => trivial⟩
instance : Nonempty StarConcept := ⟨.MARRY⟩
instance : Nonempty StarScenario := ⟨.STARGAZING⟩

/-- The condition label of each concept. -/
def starLabel : StarConcept → StarLabel
  | .ASTRONOMER => .astronomer | .STAR_PERSON => .star | .STAR_SUN => .star | .MARRY => .marry

/-- STARGAZING gives equal probability to ASTRONOMER, STAR-SUN and MARRY; STAGE to STAR-PERSON
and MARRY (p. 571). -/
def starScenario : StarScenario → Finset StarConcept
  | .STARGAZING => {.ASTRONOMER, .STAR_SUN, .MARRY}
  | .STAGE => {.STAR_PERSON, .MARRY}

/-- MARRY-THEME (p. 571): `0.475` on ASTRONOMER and on STAR-PERSON, `0.05` on STAR-SUN, and
`0` on MARRY. MARRY-AGENT, "with a strong preference for human role fillers" but otherwise
unspecified, is set the same way. -/
noncomputable def marryFiller : StarConcept → ℝ≥0∞
  | .ASTRONOMER => 19 / 40 | .STAR_PERSON => 19 / 40 | .STAR_SUN => 1 / 20 | .MARRY => 0

/-- The selectional constraint of MARRY's roles as a measure. -/
noncomputable def marryTheme : Measure StarConcept := ∑ c, marryFiller c • Measure.dirac c

@[simp] theorem marryTheme_apply_singleton (c : StarConcept) : marryTheme {c} = marryFiller c :=
  Measure.sum_smul_dirac_apply_singleton _ c

/-- The astronomer-sentence system with Dirichlet concentration `α`. -/
noncomputable def starSDS (α : ℝ) (hα : 0 < α) : SDS StarScenario StarConcept StarRole where
  prior _ := α
  prior_pos _ := hα
  scenario s := uniformOn ↑(starScenario s)
  selectional _ := marryTheme

instance (α : ℝ) (hα : 0 < α) (s : StarScenario) :
    IsProbabilityMeasure ((starSDS α hα).scenario s) :=
  isProbabilityMeasure_uniformOn (Finset.finite_toSet _)
    (Finset.coe_nonempty.mpr (by cases s <;> decide))

@[simp] theorem starSDS_prior (α : ℝ) (hα : 0 < α) : (starSDS α hα).prior = fun _ ↦ α := rfl

@[simp] theorem starSDS_scenario (α : ℝ) (hα : 0 < α) (s : StarScenario) :
    (starSDS α hα).scenario s = uniformOn ↑(starScenario s) := rfl

/-- Node roles (Figure 6): *astronomer* fills MARRY-AGENT, the verb node has no role, *star*
fills MARRY-THEME. -/
def starRoles : Fin 3 → Option StarRole := ![some .marryAgent, none, some .marryTheme]

/-- The observed labels `astronomer(_)`, `marry(_)`, `star(_)`. -/
def starLabels : Fin 3 → StarLabel := ![.astronomer, .marry, .star]

theorem starSDS_poe (α : ℝ) (hα : 0 < α) :
    (starSDS α hα).poe =
      Kernel.ofWeights λ p c => uniformOn ↑(starScenario p.1) {c} * marryFiller c := by
  show Kernel.ofWeights _ = _
  congr 1
  funext p c
  exact congrArg _ (marryTheme_apply_singleton c)

private theorem uniformOn_mul_marryFiller_ne_top (s : StarScenario) (c : StarConcept) :
    uniformOn (↑(starScenario s) : Set StarConcept) {c} * marryFiller c ≠ ∞ := by
  refine ENNReal.mul_ne_top ?_ (by cases c <;> simp only [marryFiller] <;> finiteness)
  rw [uniformOn_finset_apply_singleton]
  split_ifs with h
  · exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨c, h⟩).ne')
  · exact ENNReal.zero_ne_top

private theorem starSDS_poe_real (α : ℝ) (hα : 0 < α) (s : StarScenario) (r : StarRole)
    (p : StarConcept → Prop) [DecidablePred p] :
    ((starSDS α hα).poe (s, r)).real {c | p c} =
      (∑ c with p c, (uniformOn ↑(starScenario s) {c} * marryFiller c).toReal) /
        ∑ c, (uniformOn ↑(starScenario s) {c} * marryFiller c).toReal := by
  rw [starSDS_poe]
  exact Kernel.ofWeights_real_setOf _ (s, r) (uniformOn_mul_marryFiller_ne_top s) p

private theorem sum_starScenario {M : Type*} [AddCommMonoid M] (f : StarScenario → M) :
    ∑ s, f s = f .STARGAZING + f .STAGE := by
  rw [show (Finset.univ : Finset StarScenario) = {.STARGAZING, .STAGE} by decide,
    Finset.sum_pair (by decide)]

private theorem sum_starConcept {M : Type*} [AddCommMonoid M] (f : StarConcept → M) :
    ∑ c, f c = f .ASTRONOMER + (f .STAR_PERSON + (f .STAR_SUN + f .MARRY)) := by
  rw [show (Finset.univ : Finset StarConcept) = {.ASTRONOMER, .STAR_PERSON, .STAR_SUN, .MARRY}
    by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem star_cards :
    ((starScenario .STARGAZING).filter (starLabel · = .marry)).card = 1 ∧
    ((starScenario .STAGE).filter (starLabel · = .marry)).card = 1 ∧
    (starScenario .STARGAZING).card = 3 ∧ (starScenario .STAGE).card = 2 := by decide

private theorem star_den (α : ℝ) (hα : 0 < α) :
    (∑ s, polyaUrn (starSDS α hα).prior 3 {s} *
      ∏ i, (starSDS α hα).emission (s i) (starRoles i) (starLabel ⁻¹' {starLabels i})).toReal =
      19 * (115 * α + 8) / (10584 * (2 * α + 1)) := by
  rw [SDS.sum_toReal, sum_fin_three]
  simp +decide only [sum_starScenario, Fin.prod_univ_three, starRoles, starLabels,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, SDS.emission, starSDS_scenario, starSDS_prior, polyaUrnProb_countVec_vecCons,
    Set.preimage_singleton, starSDS_poe_real, uniformOn_finset_real_setOf, star_cards]
  simp +decide only [countVec_vecCons, countVec_zero, polyaUrnProb_zero,
    polyaUrnPredictive, Pi.zero_apply, Function.update_apply,
    sum_starScenario, Finset.sum_filter, sum_starConcept, uniformOn_finset_apply_singleton,
    marryFiller, star_cards, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_zero,
    ↓reduceIte]
  push_cast
  field_simp
  ring

private theorem star_num (α : ℝ) (hα : 0 < α) :
    (∑ s, polyaUrn (starSDS α hα).prior 3 {s} * ∏ i, (starSDS α hα).emission (s i) (starRoles i)
      {c' | starLabel c' = starLabels i ∧ (i = 2 → c' = .STAR_PERSON)}).toReal =
      95 * α / (504 * (2 * α + 1)) := by
  rw [SDS.sum_toReal, sum_fin_three]
  simp +decide only [sum_starScenario, Fin.prod_univ_three, starRoles, starLabels,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, SDS.emission, starSDS_scenario, starSDS_prior, polyaUrnProb_countVec_vecCons,
    false_implies, true_implies, and_true, starSDS_poe_real, uniformOn_finset_real_setOf,
    star_cards]
  simp +decide only [countVec_vecCons, countVec_zero, polyaUrnProb_zero,
    polyaUrnPredictive, Pi.zero_apply, Function.update_apply,
    sum_starScenario, Finset.sum_filter, sum_starConcept, uniformOn_finset_apply_singleton,
    marryFiller, star_cards, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_zero,
    ↓reduceIte]
  push_cast
  field_simp
  ring

private theorem star_num_sun (α : ℝ) (hα : 0 < α) :
    (∑ s, polyaUrn (starSDS α hα).prior 3 {s} * ∏ i, (starSDS α hα).emission (s i) (starRoles i)
      {c' | starLabel c' = starLabels i ∧ (i = 2 → c' = .STAR_SUN)}).toReal =
      38 * (5 * α + 4) / (10584 * (2 * α + 1)) := by
  rw [SDS.sum_toReal, sum_fin_three]
  simp +decide only [sum_starScenario, Fin.prod_univ_three, starRoles, starLabels,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, SDS.emission, starSDS_scenario, starSDS_prior, polyaUrnProb_countVec_vecCons,
    false_implies, true_implies, and_true, starSDS_poe_real, uniformOn_finset_real_setOf,
    star_cards]
  simp +decide only [countVec_vecCons, countVec_zero, polyaUrnProb_zero,
    polyaUrnPredictive, Pi.zero_apply, Function.update_apply,
    sum_starScenario, Finset.sum_filter, sum_starConcept, uniformOn_finset_apply_singleton,
    marryFiller, star_cards, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_zero,
    ↓reduceIte]
  push_cast
  field_simp
  ring

private theorem star_den_ne_zero (α : ℝ) (hα : 0 < α) :
    ∑ s, polyaUrn (starSDS α hα).prior 3 {s} *
      ∏ i, (starSDS α hα).emission (s i) (starRoles i) (starLabel ⁻¹' {starLabels i}) ≠ 0 := by
  intro h
  have := star_den α hα
  rw [h, ENNReal.toReal_zero] at this
  have : (0 : ℝ) < 19 * (115 * α + 8) / (10584 * (2 * α + 1)) := by positivity
  linarith

-- Table 2
theorem starPerson_real (α : ℝ) (hα : 0 < α) :
    ((starSDS α hα).nodePosterior starLabel starRoles starLabels 2).real {.STAR_PERSON} =
      105 * α / (115 * α + 8) := by
  rw [measureReal_def, SDS.nodePosterior_apply _ _ _ _ _ _ (star_den_ne_zero α hα),
    ENNReal.toReal_div, star_num, star_den]
  field_simp
  ring

theorem starSun_real (α : ℝ) (hα : 0 < α) :
    ((starSDS α hα).nodePosterior starLabel starRoles starLabels 2).real {.STAR_SUN} =
      (10 * α + 8) / (115 * α + 8) := by
  rw [measureReal_def, SDS.nodePosterior_apply _ _ _ _ _ _ (star_den_ne_zero α hα),
    ENNReal.toReal_div, star_num_sun, star_den]
  field_simp
  ring

-- Table 2
theorem starPerson_half :
    ((starSDS (1 / 2) (by norm_num)).nodePosterior starLabel starRoles starLabels 2).real
      {.STAR_PERSON} = 105 / 131 := by
  rw [starPerson_real]; norm_num

-- Table 2
theorem starPerson_tenth :
    ((starSDS (1 / 10) (by norm_num)).nodePosterior starLabel starRoles starLabels 2).real
      {.STAR_PERSON} = 7 / 13 := by
  rw [starPerson_real]; norm_num

-- p. 572
theorem starSun_strictAnti {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ((starSDS β (hα.trans hαβ)).nodePosterior starLabel starRoles starLabels 2).real
        {.STAR_SUN} <
      ((starSDS α hα).nodePosterior starLabel starRoles starLabels 2).real {.STAR_SUN} := by
  have hβ : 0 < β := hα.trans hαβ
  rw [starSun_real, starSun_real, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### Figure 6: the two constraints on *star* conflict -/

-- p. 571
theorem marryTheme_prefers_person (α : ℝ) (hα : 0 < α) :
    ((starSDS α hα).selectional .marryTheme).real {.STAR_SUN} <
      ((starSDS α hα).selectional .marryTheme).real {.STAR_PERSON} := by
  show marryTheme.real {.STAR_SUN} < marryTheme.real {.STAR_PERSON}
  simp only [measureReal_def, marryTheme_apply_singleton, marryFiller, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

-- p. 571
theorem stargazing_prefers_sun (α : ℝ) (hα : 0 < α) :
    ((starSDS α hα).scenario .STARGAZING).real {.STAR_PERSON} <
      ((starSDS α hα).scenario .STARGAZING).real {.STAR_SUN} := by
  simp +decide only [starSDS_scenario, measureReal_def, uniformOn_finset_apply_singleton,
    ↓reduceIte, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero,
    star_cards]
  norm_num

-- Figure 6
theorem star_constraints_conflict (α : ℝ) (hα : 0 < α) :
    ((starSDS α hα).selectional .marryTheme).real {.STAR_SUN} <
        ((starSDS α hα).selectional .marryTheme).real {.STAR_PERSON} ∧
      ((starSDS α hα).scenario .STARGAZING).real {.STAR_PERSON} <
        ((starSDS α hα).scenario .STARGAZING).real {.STAR_SUN} :=
  ⟨marryTheme_prefers_person α hα, stargazing_prefers_sun α hα⟩

end ErkHerbelot2024
