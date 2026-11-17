module

public import Linglib.Core.Analysis.MeanInequalities
public import Linglib.Core.Computability.ContextFreeGrammar.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.ENNReal.Inv

/-!
# Weighted and probabilistic context-free grammars

Rule weights give a derivation tree the product of the weights of the rules it applies, and a
corpus, a multiset of trees, the product over its trees; over licensed trees that is the product
of the rule weights [raised to their counts](##RoseTree.corpusWeight_eq_prod_pow_ruleCounts).
A probabilistic context-free grammar (PCFG) over `G` is a weighting in which the rules at each
nonterminal have total weight one ([abney-mcallester-pereira-1999], [smith-johnson-2007]).
Normalizing rule counts at each nonterminal gives the relative-frequency estimate,
[the maximum-likelihood PCFG](##PCFG.corpusWeight_le_corpusWeight_relFreq) of a corpus of licensed
trees ([chi-1999]) and [the only one](##PCFG.corpusWeight_eq_corpusWeight_relFreq_iff) at the
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

/-- A product over the rules of a grammar is a product over the nonterminals it has a rule for
of the products over the rules at each. -/
@[to_additive /-- A sum over the rules of a grammar is a sum over the nonterminals it has a rule
for of the sums over the rules at each. -/]
theorem ContextFreeGrammar.prod_inputs_prod_rulesWithInput {T M : Type*} [CommMonoid M]
    (g : ContextFreeGrammar T) [DecidableEq g.NT] (f : ContextFreeRule T g.NT → M) :
    ∏ a ∈ g.inputs, ∏ r ∈ g.rulesWithInput a, f r = ∏ r ∈ g.rules, f r :=
  Finset.prod_fiberwise_of_maps_to (fun _ hr ↦ g.input_mem_inputs hr) f

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

/-- The weight of a corpus is the product of the weights of its trees. -/
noncomputable def corpusWeight (D : Multiset (RoseTree (Symbol T N))) : ℝ≥0∞ :=
  (D.map (ruleWeight w)).prod

@[simp]
theorem corpusWeight_zero : corpusWeight w 0 = 1 := by
  simp [corpusWeight]

theorem corpusWeight_add (D₁ D₂ : Multiset (RoseTree (Symbol T N))) :
    corpusWeight w (D₁ + D₂) = corpusWeight w D₁ * corpusWeight w D₂ := by
  simp [corpusWeight]

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

/-- Over licensed derivation trees, the weight of a corpus is the product over the grammar's
rules of the rule weight raised to the rule's count. -/
theorem corpusWeight_eq_prod_pow_ruleCounts (D : Multiset (RoseTree (Symbol T G.NT)))
    (h : ∀ t ∈ D, t.Licensed G.Licenses) :
    corpusWeight w D = ∏ r ∈ G.rules, w r ^ ruleCounts D r := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons t D ih =>
    rw [← Multiset.singleton_add, corpusWeight_add,
      ih fun t' ht' ↦ h t' (Multiset.mem_cons_of_mem ht')]
    simp only [corpusWeight, Multiset.map_singleton, Multiset.prod_singleton, map_add,
      Pi.add_apply, pow_add, Finset.prod_mul_distrib, ruleCounts_singleton,
      ruleWeight_eq_prod_pow_ruleCount w (h t (Multiset.mem_cons_self t D))]

end RoseTree

/-! ### Probabilistic grammars -/

/-- A probabilistic context-free grammar over `G` weights the rules so that the weights vanish off
the grammar and sum to one over the rules at each nonterminal the grammar has a rule for. -/
@[ext]
structure PCFG {T : Type*} (G : ContextFreeGrammar T) [DecidableEq G.NT] where
  /-- The weight of a rule. -/
  weight : ContextFreeRule T G.NT → ℝ≥0∞
  /-- Rules outside the grammar have weight `0`. -/
  weight_eq_zero_of_not_mem : ∀ r ∉ G.rules, weight r = 0
  /-- Weights sum to one over the rules at each nonterminal the grammar has a rule for. -/
  sum_weight : ∀ a ∈ G.inputs, ∑ r ∈ G.rulesWithInput a, weight r = 1

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

attribute [simp] weight_eq_zero_of_not_mem

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
noncomputable def normalize (w : ContextFreeRule T G.NT → ℝ≥0∞) : PCFG G where
  weight r :=
    if r ∈ G.rules then
      if ∑ r' ∈ G.rulesWithInput r.input, w r' = 0 ∨ ∑ r' ∈ G.rulesWithInput r.input, w r' = ⊤
      then ((G.rulesWithInput r.input).card : ℝ≥0∞)⁻¹
      else w r / ∑ r' ∈ G.rulesWithInput r.input, w r'
    else 0
  weight_eq_zero_of_not_mem _ hr := ite_eq_right hr
  sum_weight a ha := by
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
  (ENNReal.prod_pow_le_prod_div_sum_pow (W.sum_weight_le_one a) x).trans_eq
    (prod_ofCounts_pow x a).symm

/-- Relative frequencies maximize the likelihood of rule counts ([chi-1999] §3). -/
theorem prod_pow_le_prod_ofCounts_pow (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r ≤ ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r := by
  rw [← G.prod_inputs_prod_rulesWithInput, ← G.prod_inputs_prod_rulesWithInput]
  exact Finset.prod_le_prod fun a _ ↦ W.prod_pow_le_prod_ofCounts_pow_aux x a

private theorem _root_.ENNReal.prod_eq_prod_iff_of_le {ι : Type*} {s : Finset ι} {f g : ι → ℝ≥0∞}
    (hle : ∀ i ∈ s, f i ≤ g i) (h0 : ∀ i ∈ s, g i ≠ 0) (htop : ∀ i ∈ s, g i ≠ ⊤) :
    ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  refine ⟨fun h i hi ↦ ?_, Finset.prod_congr rfl⟩
  have key : (∏ j ∈ s, f j / g j) * ∏ j ∈ s, g j = ∏ j ∈ s, g j := by
    rw [← Finset.prod_mul_distrib, ← h]
    exact Finset.prod_congr rfl fun j hj ↦ ENNReal.div_mul_cancel (h0 j hj) (htop j hj)
  rw [ENNReal.mul_eq_right (Finset.prod_ne_zero_iff.mpr h0) (ENNReal.prod_ne_top htop)] at key
  exact (ENNReal.div_eq_one_iff (h0 i hi) (htop i hi)).mp <|
    (Finset.prod_eq_one_iff_of_le_one fun j hj ↦
      ENNReal.div_le_of_le_mul (by simpa using hle j hj)).mp key i hi

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
        ENNReal.prod_pow_eq_prod_div_sum_pow_iff (W.sum_weight_le_one _) hX] at ha
      rw [ha r (G.mem_rulesWithInput_input hr), ofCounts_weight hr hX]
    · by_cases hX : ∑ r' ∈ G.rulesWithInput a, x r' = 0
      · exact Finset.prod_congr rfl fun r hr ↦ by simp [Finset.sum_eq_zero_iff.mp hX r hr]
      · rw [prod_ofCounts_pow, ENNReal.prod_pow_eq_prod_div_sum_pow_iff (W.sum_weight_le_one _) hX]
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

/-- The relative-frequency estimate from a corpus of derivation trees, the relative frequencies of
its rule counts. -/
noncomputable def relFreq (D : Multiset (RoseTree (Symbol T G.NT))) : PCFG G :=
  ofCounts (RoseTree.ruleCounts D)

/-- **The relative-frequency estimate is the maximum-likelihood PCFG** of a corpus of derivation
trees the grammar licenses. -/
theorem corpusWeight_le_corpusWeight_relFreq {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) :
    RoseTree.corpusWeight W.weight D ≤ RoseTree.corpusWeight (relFreq D).weight D := by
  rw [RoseTree.corpusWeight_eq_prod_pow_ruleCounts _ D hD,
    RoseTree.corpusWeight_eq_prod_pow_ruleCounts _ D hD]
  exact W.prod_pow_le_prod_ofCounts_pow _

/-- **The maximum-likelihood PCFG is unique**: a PCFG giving a corpus of licensed derivation trees
the probability its relative-frequency estimate does has the weights of that estimate at every
nonterminal the corpus applies a rule to. -/
theorem corpusWeight_eq_corpusWeight_relFreq_iff {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) :
    RoseTree.corpusWeight W.weight D = RoseTree.corpusWeight (relFreq D).weight D ↔
      ∀ r ∈ G.rules, ∑ r' ∈ G.rulesWithInput r.input, RoseTree.ruleCounts D r' ≠ 0 →
        W.weight r = (relFreq D).weight r := by
  rw [RoseTree.corpusWeight_eq_prod_pow_ruleCounts _ D hD,
    RoseTree.corpusWeight_eq_prod_pow_ruleCounts _ D hD]
  exact W.prod_pow_eq_prod_ofCounts_pow_iff _

end

end PCFG
