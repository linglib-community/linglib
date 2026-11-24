/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.Convex.StdSimplex
public import Linglib.Core.Basic.ENNReal.BigOperators
public import Linglib.Core.Computability.ContextFreeGrammar.RuleCount
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.ENNReal.Inv

/-!
# Weighted and probabilistic context-free grammars

Rule weights give a derivation tree the product of the weights of the rules it applies, and a
corpus, a multiset of trees, the product over its trees; over licensed trees that is the product
of the rule weights [raised to their counts](##RoseTree.prod_map_ruleWeight).
A probabilistic context-free grammar (PCFG) over `G` is a weighting in which the rules at each
nonterminal have total weight one ([abney-mcallester-pereira-1999], [smith-johnson-2007]), so
[a family of probability vectors](##PCFG.simplexEquiv), one over the rules at each nonterminal.
Normalizing rule counts at each nonterminal gives the relative-frequency estimate,
[the maximum-likelihood PCFG](##PCFG.prod_map_ruleWeight_le_ofCounts) of a corpus of licensed
trees ([chi-1999]) and [the only one](##PCFG.prod_map_ruleWeight_eq_ofCounts_iff) at the
nonterminals the corpus applies a rule to.

## Implementation notes

Weights are `ℝ≥0∞`, the scalar of `MeasureTheory.Measure`. A PCFG's weights sum to one at the
nonterminals the grammar has a rule for, where the sources assume every nonterminal has one, and
may be zero on a rule. `PCFG.normalize` is total: at a nonterminal where the weights total `0` or
`⊤` it gives the rules equal weights, where [chi-1999] defines relative frequencies only for a
sample in which every nonterminal occurs. The measure on trees whose singleton masses are the tree
weights, and its total mass ([booth-thompson-1973]), are in
`Linglib.Core.Computability.ContextFreeGrammar.Measure`.

## References

* [abney-mcallester-pereira-1999]
* [booth-thompson-1973]
* [chi-1999]
* [smith-johnson-2007]
-/

@[expose] public section

open Convexity
open scoped ENNReal

/-! ### Weighted grammars

Rule weights are any function from rules to `ℝ≥0∞`. The weight of a tree is the product of the
weights of the rules it applies. -/

section Weights

variable {T N : Type*} (w : ContextFreeRule T N → ℝ≥0∞)

/-- The weight of a node under rule weights `w`, read from its symbol and the symbols of its
children: the weight of the rule at a nonterminal, `1` at a childless terminal and `0` at a
terminal with children. -/
noncomputable def Symbol.ruleWeight : Symbol T N → List (Symbol T N) → ℝ≥0∞
  | .nonterminal A, syms => w ⟨A, syms⟩
  | .terminal _, [] => 1
  | .terminal _, _ :: _ => 0

@[simp] theorem Symbol.ruleWeight_nonterminal (A : N) (syms : List (Symbol T N)) :
    (Symbol.nonterminal A).ruleWeight w syms = w ⟨A, syms⟩ := rfl

@[simp] theorem Symbol.ruleWeight_terminal_nil (a : T) :
    (Symbol.terminal a : Symbol T N).ruleWeight w [] = 1 := rfl

@[simp] theorem Symbol.ruleWeight_terminal_cons (a : T) (s : Symbol T N)
    (syms : List (Symbol T N)) : (Symbol.terminal a).ruleWeight w (s :: syms) = 0 := rfl

namespace RoseTree

/-- The weight of a tree under rule weights `w` is the product over its nodes of the weight of
the rule applied there. -/
noncomputable def ruleWeight (t : RoseTree (Symbol T N)) : ℝ≥0∞ :=
  (t.localTrees.map fun p ↦ p.1.ruleWeight w p.2).prod

theorem ruleWeight_node (s : Symbol T N) (cs : List (RoseTree (Symbol T N))) :
    (node s cs).ruleWeight w = s.ruleWeight w (cs.map value) * (cs.map (ruleWeight w)).prod := by
  simp only [ruleWeight, localTrees_node, List.map_cons, List.prod_cons, List.map_flatten,
    List.prod_flatten, List.map_map, Function.comp_def]
  rfl

end RoseTree

end Weights

namespace RoseTree

variable {T : Type*} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]
  (w : ContextFreeRule T G.NT → ℝ≥0∞)

theorem ruleWeight_eq_prod_pow_ruleCount {t : RoseTree (Symbol T G.NT)}
    (ht : t.Licensed G.Licenses) :
    t.ruleWeight w = ∏ r ∈ G.rules, w r ^ ruleCount r t :=
  ht.prod_map_localTrees fun _ ↦ rfl

/-- Over licensed derivation trees, the product of the weights of the trees of a corpus is the
product over the grammar's rules of the rule weight raised to the rule's count. -/
theorem prod_map_ruleWeight (D : Multiset (RoseTree (Symbol T G.NT)))
    (h : ∀ t ∈ D, t.Licensed G.Licenses) :
    (D.map (ruleWeight w)).prod = ∏ r ∈ G.rules, w r ^ ruleCounts D r :=
  prod_map_localTrees_eq_prod_ruleCounts h fun _ ↦ rfl

end RoseTree

/-! ### Probabilistic grammars -/

/-- A probabilistic context-free grammar over `G` weights the rules so that the weights vanish off
the grammar and sum to one over the rules at each nonterminal the grammar has a rule for. -/
@[ext]
structure PCFG {T : Type*} (G : ContextFreeGrammar T) where
  /-- The weight of a rule. -/
  weight : ContextFreeRule T G.NT → ℝ≥0∞
  /-- Rules outside the grammar have weight `0`. -/
  weight_eq_zero_of_notMem : ∀ r ∉ G.rules, weight r = 0
  /-- Weights sum to one over the rules sharing the input of a rule of the grammar. -/
  finsum_weight : ∀ r ∈ G.rules,
    ∑ᶠ r' ∈ {r' | r' ∈ G.rules ∧ r'.input = r.input}, weight r' = 1

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

attribute [simp] weight_eq_zero_of_notMem

/-- A PCFG from weights that vanish off the grammar and sum to one over the rules at each
nonterminal the grammar has a rule for. -/
def mk' (weight : ContextFreeRule T G.NT → ℝ≥0∞) (h0 : ∀ r ∉ G.rules, weight r = 0)
    (hsum : ∀ a ∈ G.inputs, ∑ r ∈ G.rulesWithInput a, weight r = 1) : PCFG G where
  weight := weight
  weight_eq_zero_of_notMem := h0
  finsum_weight r hr := by
    rw [← ContextFreeGrammar.coe_rulesWithInput, finsum_mem_coe_finset]
    exact hsum _ (G.input_mem_inputs hr)

@[simp]
theorem mk'_weight (weight : ContextFreeRule T G.NT → ℝ≥0∞) (h0 : ∀ r ∉ G.rules, weight r = 0)
    (hsum : ∀ a ∈ G.inputs, ∑ r ∈ G.rulesWithInput a, weight r = 1) :
    (mk' weight h0 hsum).weight = weight := rfl

theorem sum_weight (a : G.NT) (ha : a ∈ G.inputs) : ∑ r ∈ G.rulesWithInput a, W.weight r = 1 := by
  obtain ⟨r, hr, rfl⟩ := ContextFreeGrammar.mem_inputs.mp ha
  rw [← finsum_mem_coe_finset, ContextFreeGrammar.coe_rulesWithInput]
  exact W.finsum_weight r hr

theorem sum_weight_le_one (A : G.NT) : ∑ r ∈ G.rulesWithInput A, W.weight r ≤ 1 := by
  by_cases hA : A ∈ G.inputs
  · exact (W.sum_weight A hA).le
  · simp [ContextFreeGrammar.rulesWithInput_eq_empty_iff.mpr hA]

theorem weight_le_one (r : ContextFreeRule T G.NT) : W.weight r ≤ 1 := by
  by_cases hr : r ∈ G.rules
  · exact (Finset.single_le_sum (f := W.weight) (fun _ _ ↦ zero_le)
      (G.mem_rulesWithInput_input hr)).trans (W.sum_weight_le_one r.input)
  · simp [hr]

theorem weight_ne_top (r : ContextFreeRule T G.NT) : W.weight r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (W.weight_le_one r)

/-! ### Probability vectors -/

/-- The rule distribution of a PCFG at a nonterminal the grammar has a rule for, the probability
vector of the weights of the rules there. -/
noncomputable def toSimplex (a : G.inputs) : StdSimplex ℝ≥0∞ (G.rulesWithInput a) :=
  .ofFintype (fun r ↦ W.weight r) (fun _ ↦ zero_le) <| by
    rw [Finset.sum_coe_sort (G.rulesWithInput a) W.weight, W.sum_weight a a.2]

@[simp]
theorem toSimplex_weights (a : G.inputs) (r : G.rulesWithInput a) :
    (W.toSimplex a).weights r = W.weight r :=
  rfl

/-- A product of powers of the rule weights is the product over the nonterminals of the products
at their probability vectors. -/
theorem prod_weight_pow (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r =
      ∏ a : G.inputs, ∏ r : G.rulesWithInput a, (W.toSimplex a).weights r ^ x r := by
  rw [← G.prod_inputs_prod_rulesWithInput,
    ← Finset.prod_coe_sort G.inputs fun a ↦ ∏ r ∈ G.rulesWithInput a, W.weight r ^ x r]
  exact Finset.prod_congr rfl fun a _ ↦
    (Finset.prod_coe_sort (G.rulesWithInput a) fun r ↦ W.weight r ^ x r).symm

section

variable [DecidableEq T]

/-- The PCFG whose rule distribution at each nonterminal is a given probability vector over the
rules there. -/
noncomputable def ofSimplex (θ : ∀ a : G.inputs, StdSimplex ℝ≥0∞ (G.rulesWithInput a)) : PCFG G :=
  mk' (fun r ↦
      if h : r ∈ G.rules then
        (θ ⟨r.input, G.input_mem_inputs h⟩).weights ⟨r, G.mem_rulesWithInput_input h⟩
      else 0)
    (fun _ hr ↦ dite_eq_right hr) fun a ha ↦ by
    rw [← Finset.sum_attach, ← Finset.univ_eq_attach,
      Finset.sum_congr rfl (g := fun r ↦ (θ ⟨a, ha⟩).weights r) fun r _ ↦ by
        obtain ⟨r, hr⟩ := r
        obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
        exact dite_eq_left hmem,
      StdSimplex.total_of_fintype]

theorem ofSimplex_weight (θ : ∀ a : G.inputs, StdSimplex ℝ≥0∞ (G.rulesWithInput a))
    (a : G.inputs) (r : G.rulesWithInput a) : (ofSimplex θ).weight r = (θ a).weights r := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨a, ha⟩ := a
  obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
  exact dite_eq_left hmem

theorem ofSimplex_toSimplex : ofSimplex W.toSimplex = W := by
  refine PCFG.ext (funext fun r ↦ ?_)
  by_cases hr : r ∈ G.rules
  · exact ofSimplex_weight _ ⟨_, G.input_mem_inputs hr⟩ ⟨r, G.mem_rulesWithInput_input hr⟩
  · simp [ofSimplex, hr]

theorem toSimplex_ofSimplex (θ : ∀ a : G.inputs, StdSimplex ℝ≥0∞ (G.rulesWithInput a)) :
    (ofSimplex θ).toSimplex = θ :=
  funext fun a ↦ StdSimplex.weights_inj.mp (Finsupp.ext fun r ↦ ofSimplex_weight θ a r)

/-- PCFGs over `G` are the families of probability vectors over the rules at each nonterminal the
grammar has a rule for. -/
noncomputable def simplexEquiv : PCFG G ≃ ∀ a : G.inputs, StdSimplex ℝ≥0∞ (G.rulesWithInput a) where
  toFun := toSimplex
  invFun := ofSimplex
  left_inv W := W.ofSimplex_toSimplex
  right_inv := toSimplex_ofSimplex

@[simp] theorem simplexEquiv_apply : simplexEquiv W = W.toSimplex := rfl

@[simp]
theorem simplexEquiv_symm_apply (θ : ∀ a : G.inputs, StdSimplex ℝ≥0∞ (G.rulesWithInput a)) :
    simplexEquiv.symm θ = ofSimplex θ :=
  rfl

/-! ### Normalized weights -/

/-- The rule weights `w` normalized at each nonterminal give a rule of the grammar its weight over
the total weight of the rules sharing its input. At a nonterminal where that total is `0` or `⊤`
the rules get equal weights. -/
noncomputable def normalize (w : ContextFreeRule T G.NT → ℝ≥0∞) : PCFG G :=
  ofSimplex fun _ ↦ .normalize fun r ↦ w r

variable {w : ContextFreeRule T G.NT → ℝ≥0∞} {a : G.NT}

theorem toSimplex_normalize (a : G.inputs) :
    (normalize w).toSimplex a = .normalize fun r ↦ w r :=
  congrFun (toSimplex_ofSimplex _) a

theorem normalize_weight (r : G.rulesWithInput a) (h0 : ∑ r' ∈ G.rulesWithInput a, w r' ≠ 0)
    (htop : ∑ r' ∈ G.rulesWithInput a, w r' ≠ ⊤) :
    (normalize w).weight r = w r / ∑ r' ∈ G.rulesWithInput a, w r' := by
  obtain ⟨a, rfl⟩ : ∃ a' : G.inputs, (a' : G.NT) = a :=
    ⟨⟨a, ContextFreeGrammar.rulesWithInput_nonempty_iff.mp ⟨r, r.2⟩⟩, rfl⟩
  rw [normalize, ofSimplex_weight _ a r,
    StdSimplex.normalize_weights (by rwa [Finset.sum_coe_sort (G.rulesWithInput a) w])
      (by rwa [Finset.sum_coe_sort (G.rulesWithInput a) w]),
    Finset.sum_coe_sort (G.rulesWithInput a) w]

theorem normalize_weight_lt_normalize_weight_iff (r r' : G.rulesWithInput a)
    (htop : ∑ r'' ∈ G.rulesWithInput a, w r'' ≠ ⊤) :
    (normalize w).weight r < (normalize w).weight r' ↔ w r < w r' := by
  obtain ⟨a, rfl⟩ : ∃ a' : G.inputs, (a' : G.NT) = a :=
    ⟨⟨a, ContextFreeGrammar.rulesWithInput_nonempty_iff.mp ⟨r, r.2⟩⟩, rfl⟩
  rw [normalize, ofSimplex_weight _ a r, ofSimplex_weight _ a r',
    StdSimplex.normalize_weights_lt_normalize_weights_iff
      (by rwa [Finset.sum_coe_sort (G.rulesWithInput a) w])]

/-- The uniform PCFG puts the uniform distribution over its rules at every nonterminal. -/
noncomputable def uniform : PCFG G :=
  normalize 1

noncomputable instance : Inhabited (PCFG G) := ⟨uniform⟩

/-! ### Relative frequencies -/

/-- The relative frequencies of rule counts `x` give each rule its count over the counts of the
rules sharing its input, and are uniform at a nonterminal whose rules all have count `0`. -/
noncomputable def ofCounts (x : ContextFreeRule T G.NT → ℕ) : PCFG G :=
  normalize fun r ↦ x r

variable {x : ContextFreeRule T G.NT → ℕ}

theorem toSimplex_ofCounts (a : G.inputs) :
    (ofCounts x).toSimplex a = .normalize fun r ↦ (x r : ℝ≥0∞) :=
  toSimplex_normalize a

theorem ofCounts_weight (r : G.rulesWithInput a) (h : ∑ r' ∈ G.rulesWithInput a, x r' ≠ 0) :
    (ofCounts x).weight r = x r / ∑ r' ∈ G.rulesWithInput a, (x r' : ℝ≥0∞) :=
  normalize_weight r (by exact_mod_cast h) (by simp [← Nat.cast_sum])

theorem ofCounts_weight_lt_ofCounts_weight_iff (r r' : G.rulesWithInput a) :
    (ofCounts x).weight r < (ofCounts x).weight r' ↔ x r < x r' := by
  rw [ofCounts, normalize_weight_lt_normalize_weight_iff r r' (by simp [← Nat.cast_sum]),
    Nat.cast_lt]

/-- Relative frequencies maximize the likelihood of rule counts ([chi-1999] §3). -/
theorem prod_pow_le_prod_ofCounts_pow (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r ≤ ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r := by
  rw [W.prod_weight_pow, (ofCounts x).prod_weight_pow]
  refine Finset.prod_le_prod fun a _ ↦ ?_
  rw [toSimplex_ofCounts]
  exact (W.toSimplex a).prod_weights_pow_le_normalize fun r : G.rulesWithInput a ↦ x r

/-- Rule counts attain their greatest likelihood only at their relative frequencies: a PCFG giving
them that likelihood has the relative frequencies as its rule distribution at every nonterminal
with a counted rule. -/
theorem prod_pow_eq_prod_ofCounts_pow_iff (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r = ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r ↔
      ∀ a : G.inputs, ∑ r ∈ G.rulesWithInput a, x r ≠ 0 →
        W.toSimplex a = (ofCounts x).toSimplex a := by
  rw [W.prod_weight_pow, (ofCounts x).prod_weight_pow,
    ENNReal.prod_eq_prod_iff_of_le
      (fun a _ ↦ by
        rw [toSimplex_ofCounts]
        exact (W.toSimplex a).prod_weights_pow_le_normalize fun r : G.rulesWithInput a ↦ x r)
      (fun a _ ↦ by
        rw [toSimplex_ofCounts]
        exact StdSimplex.prod_normalize_weights_pow_ne_zero fun r : G.rulesWithInput a ↦ x r)
      fun a _ ↦ ENNReal.prod_ne_top fun r _ ↦
        ENNReal.pow_ne_top (StdSimplex.weights_ne_top _ r)]
  refine forall_congr' fun a ↦ ?_
  simp only [Finset.mem_univ, forall_true_left]
  rw [toSimplex_ofCounts]
  by_cases hx : ∑ r ∈ G.rulesWithInput a, x r = 0
  · have h0 : ∀ r : G.rulesWithInput a, x r = 0 := fun r ↦ Finset.sum_eq_zero_iff.mp hx r r.2
    simp [h0, hx]
  · rw [StdSimplex.prod_weights_pow_eq_normalize_iff _ (x := fun r : G.rulesWithInput a ↦ x r)
      (by rwa [Finset.sum_coe_sort (G.rulesWithInput a) x])]
    simp [hx]

/-- When every nonterminal with a rule has a counted rule, the relative frequencies are the only
PCFG giving the counts their greatest likelihood. -/
theorem prod_pow_eq_prod_ofCounts_pow_iff_eq {x : ContextFreeRule T G.NT → ℕ}
    (hx : ∀ a ∈ G.inputs, ∑ r ∈ G.rulesWithInput a, x r ≠ 0) :
    ∏ r ∈ G.rules, W.weight r ^ x r = ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r ↔
      W = ofCounts x := by
  rw [prod_pow_eq_prod_ofCounts_pow_iff]
  exact ⟨fun h ↦ simplexEquiv.injective (funext fun a ↦ h a (hx a a.2)), fun h _ _ ↦ by rw [h]⟩

/-! ### Corpora -/

/-- **Relative frequencies are the maximum-likelihood PCFG** of a corpus of derivation trees the
grammar licenses. -/
theorem prod_map_ruleWeight_le_ofCounts {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) :
    (D.map (RoseTree.ruleWeight W.weight)).prod ≤
      (D.map (RoseTree.ruleWeight (ofCounts (RoseTree.ruleCounts D)).weight)).prod := by
  rw [RoseTree.prod_map_ruleWeight _ D hD, RoseTree.prod_map_ruleWeight _ D hD]
  exact W.prod_pow_le_prod_ofCounts_pow _

/-- **The maximum-likelihood PCFG is unique**: a PCFG giving a corpus of licensed derivation trees
the probability its relative frequencies do has those frequencies as its rule distribution at
every nonterminal the corpus applies a rule to. -/
theorem prod_map_ruleWeight_eq_ofCounts_iff {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) :
    (D.map (RoseTree.ruleWeight W.weight)).prod =
        (D.map (RoseTree.ruleWeight (ofCounts (RoseTree.ruleCounts D)).weight)).prod ↔
      ∀ a : G.inputs, ∑ r ∈ G.rulesWithInput a, RoseTree.ruleCounts D r ≠ 0 →
        W.toSimplex a = (ofCounts (RoseTree.ruleCounts D)).toSimplex a := by
  rw [RoseTree.prod_map_ruleWeight _ D hD, RoseTree.prod_map_ruleWeight _ D hD]
  exact W.prod_pow_eq_prod_ofCounts_pow_iff _

end

end PCFG
