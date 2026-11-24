/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic.Measure
public import Linglib.Core.Probability.Distributions.Dirichlet
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Dirichlet priors on probabilistic context-free grammars

A PCFG [is a family of probability vectors](##PCFG.simplexEquiv), one over the rules at each
nonterminal. A Dirichlet PCFG puts a Dirichlet distribution on each, independently across
nonterminals: [the prior](##DirichletPCFG.prior) is a measure on the PCFGs over the grammar. With
the rule weights integrated out, the rules applied at a nonterminal are draws from a Pólya urn
over its rules weighted by their pseudo-counts, so the expected probability of a corpus
[depends only on its rule counts](##DirichletPCFG.lintegral_prod_map_ruleWeight_prior) and
[factors](##DirichletPCFG.countsProb_add) through the posterior given part of them. The PCFG of
normalized pseudo-counts is [the mean of the prior](##DirichletPCFG.lintegral_weight_prior).

## Implementation notes

The mean PCFG of the posterior given a corpus is the proposal grammar of the Hastings sampler of
[johnson-griffiths-goldwater-2007]. `DirichletPCFG.countsProb` is real-valued, as
`ProbabilityTheory.polyaUrnProb` is.

## TODO

* The law of a corpus as a measure, the PCFG derivation measure mixed over the prior.
* With unit pseudo-counts the posterior density is the likelihood, so the posterior mode is
  the relative frequencies of the counts.

## References

* [johnson-griffiths-goldwater-2007]
-/

@[expose] public section

open Convexity Finset MeasureTheory ProbabilityTheory RoseTree

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] [DecidableEq T]

/-- The PCFG of a family of real probability vectors depends measurably on the family. -/
theorem measurable_ofSimplex_ofReal :
    Measurable fun θ : ∀ a : G.inputs, StdSimplex ℝ (G.rulesWithInput a) ↦
      ofSimplex fun a ↦ (θ a).ofReal := by
  refine measurable_comap_iff.mpr (measurable_pi_iff.mpr fun r ↦ ?_)
  by_cases h : r ∈ G.rules
  · simp only [Function.comp_def, ofSimplex, mk'_weight, dite_eq_left h, StdSimplex.ofReal_weights]
    fun_prop
  · simp only [Function.comp_def, ofSimplex, mk'_weight, dite_eq_right h]
    exact measurable_const

end PCFG

/-- A Dirichlet prior on the rule distributions of `G`, with a positive pseudo-count for every
rule of the grammar. -/
@[ext]
structure DirichletPCFG {T : Type*} (G : ContextFreeGrammar T) where
  /-- The Dirichlet pseudo-count of a rule. -/
  pseudo : ContextFreeRule T G.NT → ℝ
  /-- Pseudo-counts are positive on the rules of the grammar. -/
  pseudo_pos : ∀ r ∈ G.rules, 0 < pseudo r

namespace DirichletPCFG

variable {T : Type*} {G : ContextFreeGrammar T} (M : DirichletPCFG G)

/-! ### Conjugate update -/

/-- The posterior given rule counts `x`, in which each rule's pseudo-count grows by its count. -/
def update (x : ContextFreeRule T G.NT → ℕ) : DirichletPCFG G where
  pseudo r := M.pseudo r + x r
  pseudo_pos r hr := add_pos_of_pos_of_nonneg (M.pseudo_pos r hr) (Nat.cast_nonneg _)

@[simp]
theorem update_zero : M.update 0 = M := by
  ext r
  simp [update]

theorem update_add (x y : ContextFreeRule T G.NT → ℕ) :
    M.update (x + y) = (M.update x).update y := by
  ext r
  simp [update, add_assoc]

variable [DecidableEq G.NT]

/-! ### The urns and the probability of rule counts -/

/-- The weights of the Pólya urn at `a`, the pseudo-counts of the rules with left-hand side
`a`. -/
def urn (a : G.NT) (r : G.rulesWithInput a) : ℝ :=
  M.pseudo r

theorem urn_pos (a : G.NT) (r : G.rulesWithInput a) : 0 < M.urn a r :=
  M.pseudo_pos r (ContextFreeGrammar.mem_rulesWithInput.mp r.2).1

/-- The probability of the rule counts `x` with the rule weights integrated out, the product over
the nonterminals the grammar expands of the urn probability of the counts there. -/
noncomputable def countsProb (x : ContextFreeRule T G.NT → ℕ) : ℝ :=
  ∏ a ∈ G.inputs, polyaUrnProb (M.urn a) fun r ↦ x r

theorem countsProb_pos (x : ContextFreeRule T G.NT → ℕ) : 0 < M.countsProb x :=
  prod_pos fun a _ ↦ polyaUrnProb_pos (M.urn_pos a) _

@[simp]
theorem countsProb_zero : M.countsProb 0 = 1 :=
  prod_eq_one fun a _ ↦ polyaUrnProb_zero (M.urn a)

theorem urn_update (x : ContextFreeRule T G.NT → ℕ) (a : G.NT) :
    (M.update x).urn a = M.urn a + fun r : G.rulesWithInput a ↦ (x r : ℝ) :=
  rfl

/-- **Chain rule.** The probability of the counts `x + y` is the probability of `x` times the
probability of `y` under the posterior given `x`. -/
theorem countsProb_add (x y : ContextFreeRule T G.NT → ℕ) :
    M.countsProb (x + y) = M.countsProb x * (M.update x).countsProb y := by
  rw [countsProb, countsProb, countsProb, ← prod_mul_distrib]
  exact prod_congr rfl fun a _ ↦ polyaUrnProb_add (M.urn a) (fun r ↦ x r) fun r ↦ y r

/-! ### The prior on rule weights -/

variable [DecidableEq T]

/-- The prior on PCFGs: at each nonterminal the grammar has a rule for, the Dirichlet distribution
on the probability vectors over its rules with their pseudo-counts as parameters, independently
across nonterminals. -/
noncomputable def prior : Measure (PCFG G) :=
  (Measure.pi fun a : G.inputs ↦ dirichlet (M.urn a)).map fun θ ↦
    PCFG.ofSimplex fun a ↦ (θ a).ofReal

instance : IsProbabilityMeasure M.prior := by
  have (a : G.inputs) : IsProbabilityMeasure (dirichlet (M.urn a)) :=
    isProbabilityMeasure_dirichlet (M.urn_pos a)
  exact (Measure.isProbabilityMeasure_map_iff
    PCFG.measurable_ofSimplex_ofReal.aemeasurable).mpr inferInstance

/-- The probability `∏ r, W.weight r ^ x r` of a corpus with rule counts `x`, integrated against
the prior, is the probability of the counts
([johnson-griffiths-goldwater-2007] Equation 3). -/
theorem lintegral_prod_pow_prior (x : ContextFreeRule T G.NT → ℕ) :
    ∫⁻ W, ∏ r ∈ G.rules, W.weight r ^ x r ∂M.prior = .ofReal (M.countsProb x) := by
  have (a : G.inputs) : IsProbabilityMeasure (dirichlet (M.urn a)) :=
    isProbabilityMeasure_dirichlet (M.urn_pos a)
  have hX (a : G.inputs) : Measurable fun t : StdSimplex ℝ
      (G.rulesWithInput a) ↦ ∏ r, ENNReal.ofReal (t.weights r) ^ x r := by
    fun_prop
  have hpt (θ : ∀ a : G.inputs, StdSimplex ℝ (G.rulesWithInput a)) :
      ∏ r ∈ G.rules, (PCFG.ofSimplex fun a ↦ (θ a).ofReal).weight r ^ x r =
        ∏ a : G.inputs, ∏ r : G.rulesWithInput a, ENNReal.ofReal ((θ a).weights r) ^ x r := by
    rw [PCFG.prod_weight_pow, PCFG.toSimplex_ofSimplex]
    rfl
  rw [prior, lintegral_map (by fun_prop) PCFG.measurable_ofSimplex_ofReal, lintegral_congr hpt,
    lintegral_prod_eq_prod_lintegral_of_indepFun univ _
      (iIndepFun_pi fun a ↦ (hX a).aemeasurable) fun a ↦ (hX a).comp (measurable_pi_apply a),
    countsProb, ← prod_coe_sort G.inputs fun a ↦ polyaUrnProb (M.urn a) fun r ↦ x r,
    ENNReal.ofReal_prod_of_nonneg
      fun (a : G.inputs) _ ↦ (polyaUrnProb_pos (M.urn_pos a) _).le]
  refine prod_congr rfl fun a _ ↦ ?_
  have h := MeasurePreserving.lintegral_comp
    (measurePreserving_eval (μ := fun a : G.inputs ↦ dirichlet (M.urn a)) a) (hX a)
  rw [← lintegral_prod_pow_dirichlet (M.urn_pos a), ← h]

/-- The expected probability under the prior of a corpus of derivation trees the grammar licenses
is the probability of its rule counts. -/
theorem lintegral_prod_map_ruleWeight_prior {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) :
    ∫⁻ W, (D.map (ruleWeight W.weight)).prod ∂M.prior = .ofReal (M.countsProb (ruleCounts D)) := by
  rw [← lintegral_prod_pow_prior]
  exact lintegral_congr fun W ↦ prod_map_ruleWeight W.weight D hD

/-! ### Mean rule weights -/

omit [DecidableEq T] in
private theorem sum_ofReal_pseudo_ne_zero {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules) :
    ∑ r' ∈ G.rulesWithInput r.input, ENNReal.ofReal (M.pseudo r') ≠ 0 :=
  ((ENNReal.ofReal_pos.mpr (M.pseudo_pos r hr)).trans_le <|
    single_le_sum (f := fun r ↦ ENNReal.ofReal (M.pseudo r)) (fun _ _ ↦ zero_le)
      (G.mem_rulesWithInput_input hr)).ne'

/-- The PCFG of normalized pseudo-counts. It is [the mean of the
prior](##DirichletPCFG.lintegral_weight_prior), the predictive rule distribution, and for the
posterior given rule counts the posterior predictive one. -/
noncomputable def mean : PCFG G :=
  PCFG.normalize fun r ↦ .ofReal (M.pseudo r)

theorem mean_weight {a : G.NT} (r : G.rulesWithInput a) :
    M.mean.weight r = .ofReal (M.urn a r / ∑ r', M.urn a r') := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
  have hpos : 0 < ∑ r' : G.rulesWithInput r.input, M.urn r.input r' :=
    sum_pos (fun r' _ ↦ M.urn_pos _ r') ⟨⟨r, hr⟩, mem_univ _⟩
  rw [mean, PCFG.normalize_weight ⟨r, hr⟩ (M.sum_ofReal_pseudo_ne_zero hmem) (by simp),
    ENNReal.ofReal_div_of_pos hpos, urn,
    ENNReal.ofReal_sum_of_nonneg fun r' _ ↦ (M.urn_pos _ r').le]
  congr 1
  exact (sum_coe_sort (G.rulesWithInput r.input) fun r' ↦ ENNReal.ofReal (M.pseudo r')).symm

theorem mean_weight_lt_mean_weight_iff {a : G.NT} (r r' : G.rulesWithInput a) :
    M.mean.weight r < M.mean.weight r' ↔ M.pseudo r < M.pseudo r' := by
  rw [mean, PCFG.normalize_weight_lt_normalize_weight_iff r r' (by simp),
    ENNReal.ofReal_lt_ofReal_iff
      (M.pseudo_pos r' (ContextFreeGrammar.mem_rulesWithInput.mp r'.2).1)]

/-- Counts with at most one counted rule at each nonterminal have, under the mean PCFG, their
probability under the prior. -/
theorem prod_pow_mean_weight {x : ContextFreeRule T G.NT → ℕ}
    (hx : ∀ a, ∑ r ∈ G.rulesWithInput a, x r ≤ 1) :
    ∏ r ∈ G.rules, M.mean.weight r ^ x r = .ofReal (M.countsProb x) := by
  rw [countsProb, ← G.prod_inputs_prod_rulesWithInput,
    ENNReal.ofReal_prod_of_nonneg fun a _ ↦ (polyaUrnProb_pos (M.urn_pos a) _).le]
  refine prod_congr rfl fun a _ ↦ ?_
  have hcount : ∑ r : G.rulesWithInput a, x r ≤ 1 := by
    rw [sum_coe_sort (G.rulesWithInput a) x]
    exact hx a
  rw [polyaUrnProb_eq_prod_pow_of_sum_le_one _ hcount,
    ENNReal.ofReal_prod_of_nonneg fun r _ ↦
      pow_nonneg (polyaUrnPredictive_pos (M.urn_pos a) 0 r).le _]
  refine (prod_coe_sort _ _).symm.trans (Fintype.prod_congr _ _ fun r ↦ ?_)
  rw [mean_weight, polyaUrnPredictive_zero, ENNReal.ofReal_pow
    (div_nonneg (M.urn_pos a r).le (sum_nonneg fun r' _ ↦ (M.urn_pos a r').le))]

/-- **The mean PCFG is the mean of the prior**: the expected weight of a rule of the grammar is
its normalized pseudo-count. -/
theorem lintegral_weight_prior {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules) :
    ∫⁻ W, W.weight r ∂M.prior = M.mean.weight r := by
  have h := M.lintegral_prod_pow_prior (Pi.single r 1)
  rw [← M.prod_pow_mean_weight (x := Pi.single r 1) fun a ↦ by
    rw [Finset.sum_pi_single']; split_ifs <;> simp] at h
  simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq', hr] using h

/-- On a tree with at most one node labelled by each nonterminal, the mean PCFG gives the tree its
probability under the prior. For the posterior given a corpus, the proposal grammar of the
Hastings sampler of [johnson-griffiths-goldwater-2007] is then the exact conditional. A tree that
expands a nonterminal twice generally separates the two: the first expansion reinforces the urn
at that nonterminal, and the mean PCFG does not see it. -/
theorem ruleWeight_mean {t : RoseTree (Symbol T G.NT)} (ht : t.Licensed G.Licenses)
    (hone : ∀ a, t.values.count (.nonterminal a) ≤ 1) :
    t.ruleWeight M.mean.weight = .ofReal (M.countsProb (ruleCounts {t})) := by
  rw [ruleWeight_eq_prod_pow_ruleCount _ ht,
    ← M.prod_pow_mean_weight fun a ↦ by
      simpa using (ht.sum_ruleCount_eq_count_values a).trans_le (hone a)]
  simp [ruleCounts_singleton]

end DirichletPCFG
