module

public import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic
public import Linglib.Core.Probability.Distributions.Dirichlet
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Dirichlet priors on probabilistic context-free grammars

A Dirichlet PCFG puts a Dirichlet prior on the rule distribution at each nonterminal. With the
rule weights integrated out, the rules applied at a nonterminal are draws from a Pólya urn over
its rules, weighted by their pseudo-counts, and a corpus enters only through its rule counts.

## Main definitions

* `DirichletPCFG G`: positive pseudo-counts on the rules of `G`.
* `DirichletPCFG.prior`: the prior on rule weights.
* `DirichletPCFG.countsProb`: the probability of rule counts.
* `DirichletPCFG.update`: the posterior given rule counts.
* `DirichletPCFG.mean`: the PCFG of mean rule weights, the predictive rule distribution.

## Main results

* `DirichletPCFG.ofReal_countsProb`: the probability of rule counts is the PCFG probability of
  those counts integrated against the prior.
* `DirichletPCFG.countsProb_add`: the probability of counts `x + y` is that of `x` times that of
  `y` under the posterior given `x`.
* `DirichletPCFG.derivProb_mean`: on a tree with at most one node per nonterminal, the mean PCFG
  gives the tree its probability.

## Implementation notes

The mean PCFG of the posterior given a corpus is the proposal grammar of the Hastings sampler of
Johnson, Griffiths and Goldwater. With unit pseudo-counts the posterior mode is `PCFG.relFreq`.

## TODO

* The law of a corpus as a measure, the PCFG derivation measure mixed over the prior.

## References

* [johnson-griffiths-goldwater-2007]
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory RoseTree

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
def urn (a : G.NT) (r : G.RulesWithLHS a) : ℝ :=
  M.pseudo r

theorem urn_pos (a : G.NT) (r : G.RulesWithLHS a) : 0 < M.urn a r :=
  M.pseudo_pos r (mem_filter.mp r.2).1

/-- The probability of the rule counts `x` with the rule weights integrated out, the product over
the nonterminals the grammar expands of the urn probability of the counts there. -/
noncomputable def countsProb (x : ContextFreeRule T G.NT → ℕ) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), polyaUrnProb (M.urn a) fun r ↦ x r

theorem countsProb_pos (x : ContextFreeRule T G.NT → ℕ) : 0 < M.countsProb x :=
  prod_pos fun a _ ↦ polyaUrnProb_pos (M.urn_pos a) _

@[simp]
theorem countsProb_zero : M.countsProb 0 = 1 :=
  prod_eq_one fun a _ ↦ polyaUrnProb_zero (M.urn a)

theorem urn_update (x : ContextFreeRule T G.NT → ℕ) (a : G.NT) :
    (M.update x).urn a = M.urn a + fun r : G.RulesWithLHS a ↦ (x r : ℝ) :=
  rfl

/-- **Chain rule.** The probability of the counts `x + y` is the probability of `x` times the
probability of `y` under the posterior given `x`. -/
theorem countsProb_add (x y : ContextFreeRule T G.NT → ℕ) :
    M.countsProb (x + y) = M.countsProb x * (M.update x).countsProb y := by
  rw [countsProb, countsProb, countsProb, ← prod_mul_distrib]
  exact prod_congr rfl fun a _ ↦ polyaUrnProb_add (M.urn a) (fun r ↦ x r) fun r ↦ y r

/-! ### The prior on rule weights -/

/-- The prior on rule weights: at each nonterminal the grammar expands, the Dirichlet distribution
on the probability vectors over its rules with their pseudo-counts as parameters, independently
across nonterminals. -/
noncomputable def prior :
    Measure ((a : G.rules.image (·.input)) → Convexity.StdSimplex ℝ (G.RulesWithLHS a)) :=
  Measure.pi fun a ↦ dirichlet (M.urn a)

/-- The probability of the rule counts `x` is the PCFG probability `∏ r, θ r ^ x r` of a corpus
with those counts, integrated against the prior ([johnson-griffiths-goldwater-2007] Equation 3). -/
theorem ofReal_countsProb (x : ContextFreeRule T G.NT → ℕ) :
    ENNReal.ofReal (M.countsProb x) =
      ∫⁻ θ, ∏ a, ∏ r, ENNReal.ofReal ((θ a).weights r) ^ x r ∂M.prior := by
  have (a : G.rules.image (·.input)) : Nonempty (G.RulesWithLHS a) :=
    ContextFreeGrammar.nonempty_rulesWithLHS_iff.mpr a.2
  have (a : G.rules.image (·.input)) : IsProbabilityMeasure (dirichlet (M.urn a)) :=
    isProbabilityMeasure_dirichlet (M.urn_pos a)
  have hX (a : G.rules.image (·.input)) : Measurable fun t : Convexity.StdSimplex ℝ
      (G.RulesWithLHS a) ↦ ∏ r, ENNReal.ofReal (t.weights r) ^ x r := by
    fun_prop
  rw [prior, lintegral_prod_eq_prod_lintegral_of_indepFun univ _
      (iIndepFun_pi fun a ↦ (hX a).aemeasurable) fun a ↦ (hX a).comp (measurable_pi_apply a),
    countsProb, ← prod_coe_sort, ENNReal.ofReal_prod_of_nonneg
      fun (a : G.rules.image (·.input)) _ ↦ (polyaUrnProb_pos (M.urn_pos a) _).le]
  refine prod_congr rfl fun a _ ↦ ?_
  have h := MeasurePreserving.lintegral_comp
    (measurePreserving_eval (μ := fun a : G.rules.image (·.input) ↦ dirichlet (M.urn a)) a) (hX a)
  rw [← lintegral_prod_pow_dirichlet (M.urn_pos a), ← h]

/-! ### Mean rule weights -/

variable [DecidableEq T]

/-- The mean of the prior is the PCFG of normalized pseudo-counts. It is the predictive rule
distribution, and for the posterior given rule counts the posterior predictive one. -/
noncomputable def mean : PCFG G :=
  PCFG.normalize (fun r ↦ .ofReal (M.pseudo r))
    (fun a ha ↦ by
      obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
      refine (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (M.pseudo_pos r hr)) ?_).ne'
      exact single_le_sum (f := fun r ↦ ENNReal.ofReal (M.pseudo r)) (fun _ _ ↦ zero_le)
        (mem_filter.mpr ⟨hr, rfl⟩))
    fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top

theorem mean_weight {a : G.NT} (r : G.RulesWithLHS a) :
    M.mean.weight r = .ofReal (M.urn a r / ∑ r', M.urn a r') := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨hmem, rfl⟩ := mem_filter.mp hr
  have hpos : 0 < ∑ r' : G.RulesWithLHS r.input, M.urn r.input r' :=
    sum_pos (fun r' _ ↦ M.urn_pos _ r') ⟨⟨r, hr⟩, mem_univ _⟩
  rw [mean, PCFG.normalize_weight hmem, ENNReal.ofReal_div_of_pos hpos, urn,
    ENNReal.ofReal_sum_of_nonneg fun r' _ ↦ (M.urn_pos _ r').le]
  congr 1
  exact (sum_coe_sort (G.rules.filter (·.input = r.input))
    fun r' ↦ ENNReal.ofReal (M.pseudo r')).symm

theorem mean_weight_lt_mean_weight_iff {a : G.NT} {r r' : G.RulesWithLHS a} :
    M.mean.weight r < M.mean.weight r' ↔ M.pseudo r < M.pseudo r' := by
  rw [mean, PCFG.normalize_weight_lt_normalize_weight_iff,
    ENNReal.ofReal_lt_ofReal_iff (M.pseudo_pos r' (mem_filter.mp r'.2).1)]

/-- On a tree with at most one node labelled by each nonterminal, the mean PCFG gives the tree its
probability under the prior. For the posterior given a corpus, the proposal grammar of the
Hastings sampler of [johnson-griffiths-goldwater-2007] is then the exact conditional. A tree that
expands a nonterminal twice generally separates the two: the first expansion reinforces the urn
at that nonterminal, and the mean PCFG does not see it. -/
theorem derivProb_mean {t : RoseTree (Symbol T G.NT)} (ht : t.Licensed G.Licenses)
    (hone : ∀ a, t.values.count (.nonterminal a) ≤ 1) :
    M.mean.derivProb t = .ofReal (M.countsProb (ruleCounts {t})) := by
  rw [PCFG.derivProb_eq_prod_pow_ruleCount _ ht, countsProb,
    ← prod_fiberwise_of_maps_to (t := G.rules.image (·.input)) (g := (·.input))
      fun r hr ↦ mem_image_of_mem _ hr,
    ENNReal.ofReal_prod_of_nonneg fun a _ ↦ (polyaUrnProb_pos (M.urn_pos a) _).le]
  refine prod_congr rfl fun a _ ↦ ?_
  have hcount : ∑ r : G.RulesWithLHS a, ruleCounts {t} r ≤ 1 := by
    rw [sum_coe_sort (G.rules.filter (·.input = a)) (ruleCounts {t})]
    simpa using (ht.sum_ruleCount_eq_count_values a).trans_le (hone a)
  rw [polyaUrnProb_eq_prod_pow_of_sum_le_one _ hcount,
    ENNReal.ofReal_prod_of_nonneg fun r _ ↦
      pow_nonneg (polyaUrnPredictive_pos (M.urn_pos a) 0 r).le _]
  refine (prod_coe_sort _ _).symm.trans (Fintype.prod_congr _ _ fun r ↦ ?_)
  rw [mean_weight, polyaUrnPredictive_zero, ENNReal.ofReal_pow
    (div_nonneg (M.urn_pos a r).le (sum_nonneg fun r' _ ↦ (M.urn_pos a r').le)),
    ruleCounts_singleton]

end DirichletPCFG
