module

public import Linglib.Core.Analysis.MeanInequalities
public import Linglib.Core.Basic.ENNReal.BigOperators
public import Linglib.Core.Computability.ContextFreeGrammar.Tree
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.ENNReal.Inv

/-!
# Weighted and probabilistic context-free grammars

Rule weights give a derivation tree the product of the weights of the rules it applies, and a
corpus, a multiset of trees, the product over its trees; over licensed trees that is the product
of the rule weights [raised to their counts](##RoseTree.prod_map_ruleWeight).
A probabilistic context-free grammar (PCFG) over `G` is a weighting in which the rules at each
nonterminal have total weight one ([abney-mcallester-pereira-1999], [smith-johnson-2007]).
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
    t.ruleWeight w = ∏ r ∈ G.rules, w r ^ ruleCount r t := by
  induction ht using Licensed.grammar_induction with
  | terminal a => simp [leaf, ruleWeight_node, ruleCount_node_terminal]
  | nonterminal A cs hrule hcs ih =>
    simp only [ruleWeight_node, ruleCount_node_nonterminal, pow_add,
      Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', ite_eq_left hrule,
      Symbol.ruleWeight_nonterminal]
    congr 1
    clear hrule hcs
    induction cs with
    | nil => simp
    | cons c cs ihl =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
      rw [ih c (List.mem_cons_self ..), ihl fun c' hc' ↦ ih c' (List.mem_cons_of_mem _ hc')]

/-- Over licensed derivation trees, the product of the weights of the trees of a corpus is the
product over the grammar's rules of the rule weight raised to the rule's count. -/
theorem prod_map_ruleWeight (D : Multiset (RoseTree (Symbol T G.NT)))
    (h : ∀ t ∈ D, t.Licensed G.Licenses) :
    (D.map (ruleWeight w)).prod = ∏ r ∈ G.rules, w r ^ ruleCounts D r := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons t D ih =>
    rw [← Multiset.singleton_add, Multiset.map_add, Multiset.prod_add,
      ih fun t' ht' ↦ h t' (Multiset.mem_cons_of_mem ht')]
    simp only [Multiset.map_singleton, Multiset.prod_singleton, map_add,
      Pi.add_apply, pow_add, Finset.prod_mul_distrib, ruleCounts_singleton,
      ruleWeight_eq_prod_pow_ruleCount w (h t (Multiset.mem_cons_self t D))]

end RoseTree

/-! ### Probabilistic grammars -/

/-- A probabilistic context-free grammar over `G` weights the rules so that the weights vanish off
the grammar and sum to one over the rules at each nonterminal the grammar has a rule for. -/
@[ext]
structure PCFG {T : Type*} (G : ContextFreeGrammar T) where
  /-- The weight of a rule. -/
  weight : ContextFreeRule T G.NT → ℝ≥0∞
  /-- Rules outside the grammar have weight `0`. -/
  weight_eq_zero_of_not_mem : ∀ r ∉ G.rules, weight r = 0
  /-- Weights sum to one over the rules sharing the input of a rule of the grammar. -/
  finsum_weight : ∀ r ∈ G.rules,
    ∑ᶠ r' ∈ {r' | r' ∈ G.rules ∧ r'.input = r.input}, weight r' = 1

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

attribute [simp] weight_eq_zero_of_not_mem

/-- A PCFG from weights that vanish off the grammar and sum to one over the rules at each
nonterminal the grammar has a rule for. -/
def mk' (weight : ContextFreeRule T G.NT → ℝ≥0∞) (h0 : ∀ r ∉ G.rules, weight r = 0)
    (hsum : ∀ a ∈ G.inputs, ∑ r ∈ G.rulesWithInput a, weight r = 1) : PCFG G where
  weight := weight
  weight_eq_zero_of_not_mem := h0
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

section

variable [DecidableEq T]

/-! ### Normalized weights -/

open scoped Classical in
/-- The rule weights `w` normalized at each nonterminal give a rule of the grammar its weight over
the total weight of the rules sharing its input. At a nonterminal where that total is `0` or `⊤`
the rules get equal weights. -/
noncomputable def normalize (w : ContextFreeRule T G.NT → ℝ≥0∞) : PCFG G :=
  mk' (fun r ↦
      if r ∈ G.rules then
        if ∑ r' ∈ G.rulesWithInput r.input, w r' = 0 ∨ ∑ r' ∈ G.rulesWithInput r.input, w r' = ⊤
        then ((G.rulesWithInput r.input).card : ℝ≥0∞)⁻¹
        else w r / ∑ r' ∈ G.rulesWithInput r.input, w r'
      else 0)
    (fun _ hr ↦ ite_eq_right hr) fun a ha ↦ by
    rw [Finset.sum_congr rfl (g := fun r ↦
      if ∑ r' ∈ G.rulesWithInput a, w r' = 0 ∨ ∑ r' ∈ G.rulesWithInput a, w r' = ⊤
      then ((G.rulesWithInput a).card : ℝ≥0∞)⁻¹ else w r / ∑ r' ∈ G.rulesWithInput a, w r')
      fun r hr ↦ by
        obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
        exact ite_eq_left hmem]
    by_cases h : ∑ r' ∈ G.rulesWithInput a, w r' = 0 ∨ ∑ r' ∈ G.rulesWithInput a, w r' = ⊤
    · simp only [ite_eq_left h, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
        (ContextFreeGrammar.rulesWithInput_nonempty_iff.mpr ha))) (ENNReal.natCast_ne_top _)
    · simp only [ite_eq_right h, div_eq_mul_inv, ← Finset.sum_mul]
      exact ENNReal.mul_inv_cancel (fun h0 ↦ h (.inl h0)) fun htop ↦ h (.inr htop)

variable {w : ContextFreeRule T G.NT → ℝ≥0∞} {a : G.NT} {r r' : ContextFreeRule T G.NT}

theorem normalize_weight (hr : r ∈ G.rules) (h0 : ∑ r' ∈ G.rulesWithInput r.input, w r' ≠ 0)
    (htop : ∑ r' ∈ G.rulesWithInput r.input, w r' ≠ ⊤) :
    (normalize w).weight r = w r / ∑ r' ∈ G.rulesWithInput r.input, w r' := by
  simp [normalize, hr, h0, htop]

theorem normalize_weight_lt_normalize_weight_iff (hr : r ∈ G.rulesWithInput a)
    (hr' : r' ∈ G.rulesWithInput a) (htop : ∑ r'' ∈ G.rulesWithInput a, w r'' ≠ ⊤) :
    (normalize w).weight r < (normalize w).weight r' ↔ w r < w r' := by
  obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
  obtain ⟨hmem', hin⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr'
  by_cases h0 : ∑ r'' ∈ G.rulesWithInput r.input, w r'' = 0
  · simp [normalize, hmem, hmem', hin, h0, (Finset.sum_eq_zero_iff.mp h0 _ hr),
      (Finset.sum_eq_zero_iff.mp h0 _ hr')]
  · rw [normalize_weight hmem h0 htop, normalize_weight hmem' (hin ▸ h0) (hin ▸ htop), hin]
    exact ENNReal.div_lt_div_iff_left h0 htop

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

theorem ofCounts_weight (hr : r ∈ G.rules) (h : ∑ r' ∈ G.rulesWithInput r.input, x r' ≠ 0) :
    (ofCounts x).weight r = x r / ∑ r' ∈ G.rulesWithInput r.input, (x r' : ℝ≥0∞) :=
  normalize_weight hr (by exact_mod_cast h) (by simp [← Nat.cast_sum])

theorem ofCounts_weight_lt_ofCounts_weight_iff (hr : r ∈ G.rulesWithInput a)
    (hr' : r' ∈ G.rulesWithInput a) :
    (ofCounts x).weight r < (ofCounts x).weight r' ↔ x r < x r' := by
  rw [ofCounts, normalize_weight_lt_normalize_weight_iff hr hr'
    (by simp [← Nat.cast_sum]), Nat.cast_lt]

private theorem prod_ofCounts_pow (x : ContextFreeRule T G.NT → ℕ) (a : G.NT) :
    ∏ r ∈ G.rulesWithInput a, (ofCounts x).weight r ^ x r =
      ∏ r ∈ G.rulesWithInput a,
        ((x r : ℝ≥0∞) / ∑ r' ∈ G.rulesWithInput a, (x r' : ℝ≥0∞)) ^ x r := by
  refine Finset.prod_congr rfl fun r hr ↦ ?_
  obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
  rcases Nat.eq_zero_or_pos (x r) with h | h
  · simp [h]
  rw [ofCounts_weight hmem
    (h.trans_le (Finset.single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _) hr)).ne']

private theorem prod_pow_le_prod_ofCounts_pow_aux (x : ContextFreeRule T G.NT → ℕ) (a : G.NT) :
    ∏ r ∈ G.rulesWithInput a, W.weight r ^ x r ≤
      ∏ r ∈ G.rulesWithInput a, (ofCounts x).weight r ^ x r :=
  (ENNReal.prod_pow_le_prod_div_sum_pow _ (W.sum_weight_le_one a) x).trans_eq
    (prod_ofCounts_pow x a).symm

/-- Relative frequencies maximize the likelihood of rule counts ([chi-1999] §3). -/
theorem prod_pow_le_prod_ofCounts_pow (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r ≤ ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r := by
  rw [← G.prod_inputs_prod_rulesWithInput, ← G.prod_inputs_prod_rulesWithInput]
  exact Finset.prod_le_prod fun a _ ↦ W.prod_pow_le_prod_ofCounts_pow_aux x a

/-- Rule counts attain their greatest likelihood only at their relative frequencies: a PCFG giving
them that likelihood has the relative frequencies as its weights at every nonterminal with a
counted rule. -/
theorem prod_pow_eq_prod_ofCounts_pow_iff (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r = ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r ↔
      ∀ r ∈ G.rules, ∑ r' ∈ G.rulesWithInput r.input, x r' ≠ 0 →
        W.weight r = (ofCounts x).weight r := by
  rw [← G.prod_inputs_prod_rulesWithInput, ← G.prod_inputs_prod_rulesWithInput,
    ENNReal.prod_eq_prod_iff_of_le (fun a _ ↦ W.prod_pow_le_prod_ofCounts_pow_aux x a)
      (fun a _ ↦ Finset.prod_ne_zero_iff.mpr fun r hr ↦ ?_)
      fun a _ ↦ ENNReal.prod_ne_top fun r _ ↦
        ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ((ofCounts x).weight_le_one r))]
  · refine ⟨fun h r hr hX ↦ ?_, fun h a _ ↦ ?_⟩
    · have ha := h r.input (G.input_mem_inputs hr)
      rw [prod_ofCounts_pow,
        ENNReal.prod_pow_eq_prod_div_sum_pow_iff _ (W.sum_weight_le_one _) hX] at ha
      rw [ha r (G.mem_rulesWithInput_input hr), ofCounts_weight hr hX]
    · by_cases hX : ∑ r' ∈ G.rulesWithInput a, x r' = 0
      · exact Finset.prod_congr rfl fun r hr ↦ by simp [Finset.sum_eq_zero_iff.mp hX r hr]
      · rw [prod_ofCounts_pow,
          ENNReal.prod_pow_eq_prod_div_sum_pow_iff _ (W.sum_weight_le_one _) hX]
        intro r hr
        obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
        rw [h r hmem hX, ofCounts_weight hmem hX]
  · obtain ⟨hmem, rfl⟩ := ContextFreeGrammar.mem_rulesWithInput.mp hr
    rcases Nat.eq_zero_or_pos (x r) with h | h
    · simp [h]
    · have hX := (h.trans_le (Finset.single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _) hr)).ne'
      rw [ofCounts_weight hmem hX]
      exact pow_ne_zero _ (ENNReal.div_ne_zero.mpr
        ⟨by exact_mod_cast h.ne', by simp [← Nat.cast_sum]⟩)

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
the probability its relative frequencies do has those frequencies as weights at every nonterminal
the corpus applies a rule to. -/
theorem prod_map_ruleWeight_eq_ofCounts_iff {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) :
    (D.map (RoseTree.ruleWeight W.weight)).prod =
        (D.map (RoseTree.ruleWeight (ofCounts (RoseTree.ruleCounts D)).weight)).prod ↔
      ∀ r ∈ G.rules, ∑ r' ∈ G.rulesWithInput r.input, RoseTree.ruleCounts D r' ≠ 0 →
        W.weight r = (ofCounts (RoseTree.ruleCounts D)).weight r := by
  rw [RoseTree.prod_map_ruleWeight _ D hD, RoseTree.prod_map_ruleWeight _ D hD]
  exact W.prod_pow_eq_prod_ofCounts_pow_iff _

end

end PCFG
