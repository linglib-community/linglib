module

public import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic
public import Linglib.Core.Probability.PolyaUrn
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Dirichlet priors on probabilistic context-free grammars

A Dirichlet PCFG over `G` puts a Dirichlet prior on the rule distribution at each nonterminal,
given by a positive pseudo-count for every rule. Integrating the rule weights out, the rules
applied at a nonterminal across a corpus are draws from a Pólya urn over the rules with that
left-hand side, weighted by their pseudo-counts, and each notion here is read off those urns:

* the probability of a corpus is the product over the nonterminals of the urn probability of the
  corpus rule counts there;
* the posterior given a corpus raises each pseudo-count by the corpus count of its rule, and the
  probability of a corpus `D₁ + D₂` is the probability of `D₁` times the probability of `D₂`
  under the posterior given `D₁`, so derivation trees are exchangeable but not independent as
  they are under a PCFG (`PCFG.corpusProb_add`);
* the posterior predictive probability of a rule, the posterior mean of its weight, is the
  prediction rule of the urn at its left-hand side, and these probabilities form a PCFG.

## Main definitions

* `DirichletPCFG G`: positive pseudo-counts on the rules of `G`.
* `DirichletPCFG.urn`: the urn weights at a nonterminal, the pseudo-counts of its rules.
* `DirichletPCFG.countsProb`, `DirichletPCFG.lhsCounts`, `DirichletPCFG.corpusProb`: the
  probability of rule counts, the corpus rule counts at a nonterminal, and the probability of a
  corpus.
* `DirichletPCFG.posterior`: the conjugate update by a corpus.
* `DirichletPCFG.predictive`, `DirichletPCFG.predictivePCFG`: the posterior predictive
  probabilities of the rules at a nonterminal, and the PCFG they form.

## Main results

* `DirichletPCFG.corpusProb_add`: the probability of `D₁ + D₂` is the probability of `D₁` times
  the probability of `D₂` under the posterior given `D₁`. Dividing out, the probability of a tree
  given the rest of the corpus is its probability under the posterior given the rest, the
  conditional of the collapsed sampler of [johnson-griffiths-goldwater-2007].
* `DirichletPCFG.predictive_lt_predictive_iff`: at a nonterminal the predictive probabilities
  order rules by posterior pseudo-count.
* `DirichletPCFG.predictivePCFG_posterior`: predicting from `D₂` under the posterior given `D₁`
  is predicting from `D₁ + D₂`.
* `DirichletPCFG.derivProb_predictivePCFG`: on a tree that expands each nonterminal at most once,
  the predictive PCFG gives the tree its probability under the posterior.

## Implementation notes

The pseudo-counts are a function on all rules, positive on the rules of the grammar, so that the
posterior is a pointwise sum; `urn` restricts them to the rules with a given left-hand side.
`corpusProb` is the closed form of [johnson-griffiths-goldwater-2007]'s Equation 3, a product of
ratios of Dirichlet normalising constants, written in rising factorials by `polyaUrnProb`.
`predictivePCFG D` is the proposal grammar of their Hastings sampler, the posterior mean of the
rule weights given `D`. With every pseudo-count `1` the Dirichlet prior is uniform on the simplex,
so the posterior mode is the PCFG that maximizes the likelihood of the corpus, its
relative-frequency estimate `PCFG.relFreq` (`PCFG.corpusProb_le_corpusProb_relFreq`).

## TODO

The law of a corpus as a measure, the PCFG derivation measure mixed over the Dirichlet prior, is
not constructed; `corpusProb` is its value on a sequence of trees.

## References

* [johnson-griffiths-goldwater-2007]
-/

@[expose] public section

open Finset ProbabilityTheory RoseTree

/-- A Dirichlet prior on the rule distributions of `G`: a positive pseudo-count for every rule
of the grammar. -/
@[ext]
structure DirichletPCFG {T : Type*} (G : ContextFreeGrammar T) where
  /-- The Dirichlet pseudo-count of a rule. -/
  pseudo : ContextFreeRule T G.NT → ℝ
  /-- Pseudo-counts are positive on the rules of the grammar. -/
  pseudo_pos : ∀ r ∈ G.rules, 0 < pseudo r

namespace DirichletPCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (M : DirichletPCFG G)

/-- The weights of the Pólya urn at `a`: the pseudo-counts of the rules with left-hand side
`a`. -/
def urn (a : G.NT) (r : G.RulesWithLHS a) : ℝ :=
  M.pseudo r

theorem urn_pos (a : G.NT) (r : G.RulesWithLHS a) : 0 < M.urn a r :=
  M.pseudo_pos r (mem_filter.mp r.2).1

/-- The probability of the rule counts `x` with the rule weights integrated out: the product over
the nonterminals the grammar expands of the urn probability of the counts there. -/
noncomputable def countsProb (x : ContextFreeRule T G.NT → ℕ) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), polyaUrnProb (M.urn a) fun r ↦ x r

theorem countsProb_pos (x : ContextFreeRule T G.NT → ℕ) : 0 < M.countsProb x :=
  prod_pos fun a ha ↦
    have := ContextFreeGrammar.nonempty_rulesWithLHS_iff.mpr ha
    polyaUrnProb_pos (M.urn_pos a) _

@[simp]
theorem countsProb_zero : M.countsProb 0 = 1 :=
  prod_eq_one fun a _ ↦ polyaUrnProb_zero (M.urn a)

variable [DecidableEq T]

/-- The corpus counts of the rules with left-hand side `a`. -/
def lhsCounts (a : G.NT) (D : Multiset (RoseTree (Symbol T G.NT))) (r : G.RulesWithLHS a) : ℕ :=
  corpusRuleCount r D

@[simp]
theorem lhsCounts_zero (a : G.NT) : lhsCounts (G := G) a 0 = 0 := by
  funext r
  simp [lhsCounts]

theorem lhsCounts_add (a : G.NT) (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    lhsCounts a (D₁ + D₂) = lhsCounts a D₁ + lhsCounts a D₂ := by
  funext r
  simp [lhsCounts, corpusRuleCount_add]

/-- The probability of a corpus with the rule weights integrated out: the probability of its rule
counts. -/
noncomputable def corpusProb (D : Multiset (RoseTree (Symbol T G.NT))) : ℝ :=
  M.countsProb fun r ↦ corpusRuleCount r D

theorem corpusProb_eq (D : Multiset (RoseTree (Symbol T G.NT))) :
    M.corpusProb D = ∏ a ∈ G.rules.image (·.input), polyaUrnProb (M.urn a) (lhsCounts a D) :=
  rfl

theorem corpusProb_pos (D : Multiset (RoseTree (Symbol T G.NT))) : 0 < M.corpusProb D :=
  M.countsProb_pos _

@[simp]
theorem corpusProb_zero : M.corpusProb 0 = 1 := by
  simp [corpusProb_eq]

/-! ### Conjugate update -/

/-- The posterior given a corpus: each rule's pseudo-count grows by its corpus count. -/
def posterior (D : Multiset (RoseTree (Symbol T G.NT))) : DirichletPCFG G where
  pseudo r := M.pseudo r + corpusRuleCount r D
  pseudo_pos r hr := add_pos_of_pos_of_nonneg (M.pseudo_pos r hr) (Nat.cast_nonneg _)

/-- The urn of the posterior at `a` adds the corpus counts at `a` to the weights. -/
theorem urn_posterior (a : G.NT) (D : Multiset (RoseTree (Symbol T G.NT))) :
    (M.posterior D).urn a = M.urn a + fun r ↦ (lhsCounts a D r : ℝ) :=
  rfl

@[simp]
theorem posterior_zero : M.posterior 0 = M := by
  ext r
  simp [posterior]

theorem posterior_add (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    M.posterior (D₁ + D₂) = (M.posterior D₁).posterior D₂ := by
  ext r
  simp [posterior, corpusRuleCount_add, add_assoc]

/-- **Chain rule.** The probability of the corpus `D₁ + D₂` is the probability of `D₁` times the
probability of `D₂` under the posterior given `D₁`. -/
theorem corpusProb_add (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    M.corpusProb (D₁ + D₂) = M.corpusProb D₁ * (M.posterior D₁).corpusProb D₂ := by
  simp only [corpusProb_eq, lhsCounts_add, polyaUrnProb_add, urn_posterior, prod_mul_distrib]

/-! ### Posterior predictive rule distribution -/

/-- The posterior predictive probabilities of the rules with left-hand side `a` given a corpus,
the posterior means of their weights: the prediction rule of the urn at `a` after the corpus
counts. -/
noncomputable def predictive (a : G.NT) (D : Multiset (RoseTree (Symbol T G.NT))) :
    G.RulesWithLHS a → ℝ :=
  polyaUrnPredictive (M.urn a) (lhsCounts a D)

theorem predictive_pos (a : G.NT) (D : Multiset (RoseTree (Symbol T G.NT)))
    (r : G.RulesWithLHS a) : 0 < M.predictive a D r :=
  polyaUrnPredictive_pos (M.urn_pos a) _ r

/-- With no data the predictive probability is the normalised prior pseudo-count. -/
@[simp]
theorem predictive_zero (a : G.NT) (r : G.RulesWithLHS a) :
    M.predictive a 0 r = M.urn a r / ∑ r', M.urn a r' := by
  simp [predictive, polyaUrnPredictive_zero]

theorem sum_predictive {a : G.NT} [Nonempty (G.RulesWithLHS a)]
    (D : Multiset (RoseTree (Symbol T G.NT))) : ∑ r, M.predictive a D r = 1 :=
  sum_polyaUrnPredictive (M.urn_pos a) _

/-- At a nonterminal, the predictive probabilities order rules by posterior pseudo-count. -/
theorem predictive_lt_predictive_iff {a : G.NT} {D : Multiset (RoseTree (Symbol T G.NT))}
    {r r' : G.RulesWithLHS a} :
    M.predictive a D r < M.predictive a D r' ↔
      M.pseudo r + corpusRuleCount r D < M.pseudo r' + corpusRuleCount r' D :=
  polyaUrnPredictive_lt_polyaUrnPredictive_iff (M.urn_pos a)

/-- Predicting from `D₂` under the posterior given `D₁` is predicting from `D₁ + D₂`. -/
theorem predictive_posterior (a : G.NT) (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    (M.posterior D₁).predictive a D₂ = M.predictive a (D₁ + D₂) := by
  rw [predictive, urn_posterior, polyaUrnPredictive_add, ← lhsCounts_add, predictive]

/-- The posterior predictive PCFG: each rule of the grammar has its predictive probability at
its left-hand side. -/
noncomputable def predictivePCFG (D : Multiset (RoseTree (Symbol T G.NT))) : PCFG G where
  weight r :=
    if hr : r ∈ G.rules then .ofReal (M.predictive r.input D ⟨r, mem_filter.mpr ⟨hr, rfl⟩⟩)
    else 0
  weight_nonneg _ := zero_le
  weight_eq_zero_of_not_mem _ hr := dite_eq_right hr
  sum_weight a ha := by
    have := ContextFreeGrammar.nonempty_rulesWithLHS_iff.mpr ha
    rw [← sum_coe_sort, ← ENNReal.ofReal_one, ← M.sum_predictive (a := a) D,
      ENNReal.ofReal_sum_of_nonneg fun r _ ↦ (M.predictive_pos a D r).le]
    refine Fintype.sum_congr _ _ fun ⟨r, hr⟩ ↦ ?_
    obtain ⟨hmem, rfl⟩ := mem_filter.mp hr
    exact dite_eq_left hmem

theorem predictivePCFG_weight {a : G.NT} (r : G.RulesWithLHS a)
    (D : Multiset (RoseTree (Symbol T G.NT))) :
    (M.predictivePCFG D).weight r = .ofReal (M.predictive a D r) := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨hmem, rfl⟩ := mem_filter.mp hr
  exact dite_eq_left hmem

/-- Predicting from `D₂` under the posterior given `D₁` is predicting from `D₁ + D₂`; with
`D₂ = 0`, the prior predictive PCFG of the posterior is the posterior predictive PCFG. -/
theorem predictivePCFG_posterior (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    (M.posterior D₁).predictivePCFG D₂ = M.predictivePCFG (D₁ + D₂) := by
  ext r
  simp only [predictivePCFG, predictive_posterior]

/-- On a tree that expands each nonterminal at most once, the predictive PCFG given `D` agrees
with the posterior given `D`, so there the proposal grammar of the Hastings sampler of
[johnson-griffiths-goldwater-2007] is the exact conditional. A tree that expands a nonterminal
twice generally separates them: the first expansion reinforces the urn at that nonterminal, and
the predictive PCFG does not see it. -/
theorem derivProb_predictivePCFG {t : RoseTree (Symbol T G.NT)} (ht : t.Licensed G.Licenses)
    (hone : ∀ a, t.values.count (.nonterminal a) ≤ 1)
    (D : Multiset (RoseTree (Symbol T G.NT))) :
    (M.predictivePCFG D).derivProb t = .ofReal ((M.posterior D).corpusProb {t}) := by
  rw [PCFG.derivProb_eq_prod_pow_ruleCount _ ht, corpusProb_eq,
    ← prod_fiberwise_of_maps_to (t := G.rules.image (·.input)) (g := (·.input))
      fun r hr ↦ mem_image_of_mem _ hr,
    ENNReal.ofReal_prod_of_nonneg fun a ha ↦
      have := ContextFreeGrammar.nonempty_rulesWithLHS_iff.mpr ha
      (polyaUrnProb_pos ((M.posterior D).urn_pos a) _).le]
  refine prod_congr rfl fun a _ ↦ ?_
  have hpred : polyaUrnPredictive ((M.posterior D).urn a) 0 = M.predictive a D := by
    simpa [predictive] using M.predictive_posterior a D 0
  have hcount : ∑ r, lhsCounts a {t} r ≤ 1 :=
    calc ∑ r, lhsCounts a {t} r = ∑ r ∈ G.rules.filter (·.input = a), ruleCount r t := by
          simp only [lhsCounts, corpusRuleCount_singleton]
          exact Finset.sum_coe_sort _ (ruleCount · t)
      _ ≤ 1 := (ht.sum_ruleCount_eq_count_values a).trans_le (hone a)
  rw [polyaUrnProb_eq_prod_pow_of_sum_le_one _ hcount, hpred,
    ENNReal.ofReal_prod_of_nonneg fun r _ ↦ pow_nonneg (M.predictive_pos a D r).le _]
  refine (prod_coe_sort _ _).symm.trans (Fintype.prod_congr _ _ fun r ↦ ?_)
  rw [predictivePCFG_weight, ENNReal.ofReal_pow (M.predictive_pos a D r).le]
  simp [lhsCounts]

end DirichletPCFG
