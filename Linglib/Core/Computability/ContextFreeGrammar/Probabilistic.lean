module

public import Linglib.Core.Analysis.MeanInequalities
public import Linglib.Core.Computability.ContextFreeGrammar.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.ENNReal.Inv

/-!
# Probabilistic context-free grammars

A probabilistic context-free grammar (PCFG) over `G` weights the rules of `G` so that the rules
expanding each nonterminal have total weight one. A derivation tree has the product of the
weights of the rules it applies, and a corpus, a multiset of trees, the product over its trees.

## Main definitions

* `PCFG G`: rule weights, zero off the grammar and normalised at each nonterminal.
* `PCFG.derivProb`, `PCFG.corpusProb`: the probability of a derivation tree and of a corpus.
* `PCFG.normalize`: rule weights normalised at each nonterminal.
* `PCFG.uniform`, `PCFG.ofCounts`, `PCFG.relFreq`: the uniform PCFG, the relative frequencies of
  rule counts, and the relative-frequency estimate from a corpus.

## Main results

* `PCFG.corpusProb_eq_prod_pow_ruleCounts`: over licensed trees, the probability of a corpus is
  the product of the rule weights raised to their counts.
* `PCFG.corpusProb_le_corpusProb_relFreq`: the relative-frequency estimate is the
  maximum-likelihood PCFG of a corpus of licensed trees ([chi-1999] §3).

## Implementation notes

Weights are `ℝ≥0∞`, the scalar of `MeasureTheory.Measure`. The measure on trees whose singleton
masses are `derivProb`, and tightness ([booth-thompson-1973], [chi-1999]), are in
`Linglib.Core.Computability.ContextFreeGrammar.Measure`.

## References

* [booth-thompson-1973]
* [chi-1999]
-/

@[expose] public section

open scoped ENNReal

/-- A probabilistic context-free grammar over `G` weights the rules so that the weights vanish off
the grammar and sum to one over the rules with each left-hand side the grammar expands. -/
@[ext]
structure PCFG {T : Type*} (G : ContextFreeGrammar T) [DecidableEq G.NT] where
  /-- The weight of a rule. -/
  weight : ContextFreeRule T G.NT → ℝ≥0∞
  /-- Rules outside the grammar have weight `0`. -/
  weight_eq_zero_of_not_mem : ∀ r ∉ G.rules, weight r = 0
  /-- Weights sum to one over the rules with each left-hand side the grammar expands. -/
  sum_weight : ∀ a ∈ G.rules.image (·.input), ∑ r ∈ G.rules.filter (·.input = a), weight r = 1

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

attribute [simp] weight_eq_zero_of_not_mem

/-- The weight of a node, read from its symbol and the symbols of its children, is the rule
weight at a nonterminal, `1` at a childless terminal and `0` at a terminal with children. -/
noncomputable def symbolWeight : Symbol T G.NT → List (Symbol T G.NT) → ℝ≥0∞
  | .nonterminal A, syms => W.weight ⟨A, syms⟩
  | .terminal _, [] => 1
  | .terminal _, _ :: _ => 0

@[simp] theorem symbolWeight_nonterminal (A : G.NT) (syms : List (Symbol T G.NT)) :
    W.symbolWeight (.nonterminal A) syms = W.weight ⟨A, syms⟩ := rfl

@[simp] theorem symbolWeight_terminal_nil (a : T) : W.symbolWeight (.terminal a) [] = 1 := rfl

@[simp] theorem symbolWeight_terminal_cons (a : T) (s : Symbol T G.NT)
    (syms : List (Symbol T G.NT)) : W.symbolWeight (.terminal a) (s :: syms) = 0 := rfl

/-- The probability of a derivation tree is the product over its nodes of the weight of the rule
applied there. -/
noncomputable def derivProb (t : RoseTree (Symbol T G.NT)) : ℝ≥0∞ :=
  (t.localTrees.map fun p ↦ W.symbolWeight p.1 p.2).prod

theorem derivProb_node (s : Symbol T G.NT) (cs : List (RoseTree (Symbol T G.NT))) :
    W.derivProb (RoseTree.node s cs) =
      W.symbolWeight s (cs.map RoseTree.value) * (cs.map W.derivProb).prod := by
  simp only [derivProb, RoseTree.localTrees_node, List.map_cons, List.prod_cons, List.map_flatten,
    List.prod_flatten, List.map_map, Function.comp_def]
  rfl

/-- The probability of a corpus is the product of the probabilities of its derivation trees. -/
noncomputable def corpusProb (D : Multiset (RoseTree (Symbol T G.NT))) : ℝ≥0∞ :=
  (D.map W.derivProb).prod

@[simp]
theorem corpusProb_zero : W.corpusProb 0 = 1 := by
  simp [corpusProb]

theorem corpusProb_add (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    W.corpusProb (D₁ + D₂) = W.corpusProb D₁ * W.corpusProb D₂ := by
  simp [corpusProb]

theorem sum_weight_le_one (A : G.NT) : ∑ r ∈ G.rules.filter (·.input = A), W.weight r ≤ 1 := by
  by_cases hA : A ∈ G.rules.image (·.input)
  · exact (W.sum_weight A hA).le
  · rw [Finset.sum_eq_zero fun r hr ↦ (hA (Finset.mem_image.mpr
      ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩)).elim]
    exact zero_le_one

section

variable [DecidableEq T]

/-! ### Normalized weights -/

/-- The rule weights `w` normalized at each nonterminal give a rule its weight over the total
weight of the rules sharing its left-hand side, and `0` off the grammar. The totals must be
nonzero and finite. -/
noncomputable def normalize (w : ContextFreeRule T G.NT → ℝ≥0∞)
    (h0 : ∀ a ∈ G.rules.image (·.input), ∑ r ∈ G.rules.filter (·.input = a), w r ≠ 0)
    (htop : ∀ a ∈ G.rules.image (·.input), ∑ r ∈ G.rules.filter (·.input = a), w r ≠ ⊤) :
    PCFG G where
  weight r := if r ∈ G.rules then w r / ∑ r' ∈ G.rules.filter (·.input = r.input), w r' else 0
  weight_eq_zero_of_not_mem _ hr := ite_eq_right hr
  sum_weight a ha :=
    calc _ = ∑ r ∈ G.rules.filter (·.input = a),
            w r * (∑ r' ∈ G.rules.filter (·.input = a), w r')⁻¹ :=
          Finset.sum_congr rfl fun r hr ↦ by
            obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hr
            exact (ite_eq_left hmem).trans (div_eq_mul_inv _ _)
      _ = 1 := by rw [← Finset.sum_mul]; exact ENNReal.mul_inv_cancel (h0 a ha) (htop a ha)

section Normalize

variable {w : ContextFreeRule T G.NT → ℝ≥0∞}
  {h0 : ∀ a ∈ G.rules.image (·.input), ∑ r ∈ G.rules.filter (·.input = a), w r ≠ 0}
  {htop : ∀ a ∈ G.rules.image (·.input), ∑ r ∈ G.rules.filter (·.input = a), w r ≠ ⊤}

theorem normalize_weight {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules) :
    (normalize w h0 htop).weight r = w r / ∑ r' ∈ G.rules.filter (·.input = r.input), w r' :=
  ite_eq_left hr

theorem normalize_weight_lt_normalize_weight_iff {a : G.NT} {r r' : G.RulesWithLHS a} :
    (normalize w h0 htop).weight r < (normalize w h0 htop).weight r' ↔ w r < w r' := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨r', hr'⟩ := r'
  obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hr
  obtain ⟨hmem', hin⟩ := Finset.mem_filter.mp hr'
  have ha : r.input ∈ G.rules.image (·.input) := Finset.mem_image_of_mem _ hmem
  rw [normalize_weight hmem, normalize_weight hmem', hin]
  exact ENNReal.div_lt_div_iff_left (h0 _ ha) (htop _ ha)

end Normalize

/-- The uniform PCFG puts the uniform distribution over its rules at every nonterminal. -/
noncomputable def uniform : PCFG G :=
  normalize 1 (fun _ ha ↦ by simpa using ContextFreeGrammar.card_filter_input_ne_zero ha)
    fun _ _ ↦ by simp

noncomputable instance : Inhabited (PCFG G) := ⟨uniform⟩

/-! ### Relative frequencies -/

/-- The relative frequencies of rule counts `x` give each rule its count over the counts of the
rules sharing its left-hand side, and are uniform at a nonterminal whose rules all have count
`0`. -/
noncomputable def ofCounts (x : ContextFreeRule T G.NT → ℕ) : PCFG G :=
  normalize
    (fun r ↦ ((if ∑ r' ∈ G.rules.filter (·.input = r.input), x r' = 0 then 1 else x r : ℕ) : ℝ≥0∞))
    (fun a ha ↦ by
      rw [← Nat.cast_sum, Nat.cast_ne_zero,
        Finset.sum_congr rfl fun r hr ↦ by rw [(Finset.mem_filter.mp hr).2]]
      by_cases h : ∑ r' ∈ G.rules.filter (·.input = a), x r' = 0
      · simpa [h] using ContextFreeGrammar.card_filter_input_ne_zero ha
      · simp [h])
    fun _ _ ↦ by rw [← Nat.cast_sum]; exact ENNReal.natCast_ne_top _

theorem ofCounts_weight {x : ContextFreeRule T G.NT → ℕ} {r : ContextFreeRule T G.NT}
    (hr : r ∈ G.rules) (h : ∑ r' ∈ G.rules.filter (·.input = r.input), x r' ≠ 0) :
    (ofCounts x).weight r = x r / ∑ r' ∈ G.rules.filter (·.input = r.input), (x r' : ℝ≥0∞) := by
  rw [ofCounts, normalize_weight hr]
  congr 1
  · simp [h]
  · exact Finset.sum_congr rfl fun r' hr' ↦ by simp [(Finset.mem_filter.mp hr').2, h]

theorem ofCounts_weight_lt_ofCounts_weight_iff {x : ContextFreeRule T G.NT → ℕ} {a : G.NT}
    {r r' : G.RulesWithLHS a} : (ofCounts x).weight r < (ofCounts x).weight r' ↔ x r < x r' := by
  rw [ofCounts, normalize_weight_lt_normalize_weight_iff, Nat.cast_lt]
  obtain ⟨r, hr⟩ := r
  obtain ⟨r', hr'⟩ := r'
  have hle {s} (hs : s ∈ G.rules.filter (·.input = a)) :
      x s ≤ ∑ r'' ∈ G.rules.filter (·.input = a), x r'' :=
    Finset.single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _) hs
  simp only [(Finset.mem_filter.mp hr).2, (Finset.mem_filter.mp hr').2]
  split_ifs with h0
  · simp [Nat.le_zero.mp (h0 ▸ hle hr), Nat.le_zero.mp (h0 ▸ hle hr')]
  · rfl

/-- **Relative frequencies maximize the likelihood of rule counts** ([chi-1999] §3): the counts
`x` have probability `∏ r, W.weight r ^ x r` under a PCFG `W`, at most their probability under
their relative frequencies. -/
theorem prod_pow_le_prod_ofCounts_pow (x : ContextFreeRule T G.NT → ℕ) :
    ∏ r ∈ G.rules, W.weight r ^ x r ≤ ∏ r ∈ G.rules, (ofCounts x).weight r ^ x r := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := G.rules) (t := G.rules.image (·.input))
      (g := (·.input)) fun r hr ↦ Finset.mem_image_of_mem _ hr,
    ← Finset.prod_fiberwise_of_maps_to (s := G.rules) (t := G.rules.image (·.input))
      (g := (·.input)) fun r hr ↦ Finset.mem_image_of_mem _ hr]
  refine Finset.prod_le_prod fun a _ ↦
    (ENNReal.prod_pow_le_prod_div_sum_pow (W.sum_weight_le_one a) x).trans_eq ?_
  refine Finset.prod_congr rfl fun r hr ↦ ?_
  obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hr
  rcases Nat.eq_zero_or_pos (x r) with h | h
  · simp [h]
  rw [ofCounts_weight hmem
    (h.trans_le (Finset.single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _) hr)).ne']

/-! ### Corpora -/

theorem derivProb_eq_prod_pow_ruleCount {t : RoseTree (Symbol T G.NT)}
    (ht : t.Licensed G.Licenses) :
    W.derivProb t = ∏ r ∈ G.rules, W.weight r ^ RoseTree.ruleCount r t := by
  induction ht using RoseTree.Licensed.grammar_induction with
  | terminal a => simp [RoseTree.leaf, derivProb_node, RoseTree.ruleCount_node_terminal]
  | nonterminal A cs hrule hcs ih =>
    simp only [derivProb_node, RoseTree.ruleCount_node_nonterminal, pow_add,
      Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', ite_eq_left hrule,
      symbolWeight_nonterminal]
    congr 1
    clear hrule hcs
    induction cs with
    | nil => simp
    | cons c cs ihl =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
      rw [ih c (List.mem_cons_self ..), ihl fun c' hc' ↦ ih c' (List.mem_cons_of_mem _ hc')]

theorem corpusProb_eq_prod_pow_ruleCounts (D : Multiset (RoseTree (Symbol T G.NT)))
    (h : ∀ t ∈ D, t.Licensed G.Licenses) :
    W.corpusProb D = ∏ r ∈ G.rules, W.weight r ^ RoseTree.ruleCounts D r := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons t D ih =>
    rw [← Multiset.singleton_add, corpusProb_add,
      ih fun t' ht' ↦ h t' (Multiset.mem_cons_of_mem ht')]
    simp only [corpusProb, Multiset.map_singleton, Multiset.prod_singleton, map_add,
      Pi.add_apply, pow_add, Finset.prod_mul_distrib, RoseTree.ruleCounts_singleton,
      W.derivProb_eq_prod_pow_ruleCount (h t (Multiset.mem_cons_self t D))]

/-- The relative-frequency estimate from a corpus of derivation trees, the relative frequencies of
its rule counts. -/
noncomputable def relFreq (D : Multiset (RoseTree (Symbol T G.NT))) : PCFG G :=
  ofCounts (RoseTree.ruleCounts D)

theorem corpusProb_le_corpusProb_relFreq {D : Multiset (RoseTree (Symbol T G.NT))}
    (hD : ∀ t ∈ D, t.Licensed G.Licenses) : W.corpusProb D ≤ (relFreq D).corpusProb D := by
  rw [W.corpusProb_eq_prod_pow_ruleCounts D hD, (relFreq D).corpusProb_eq_prod_pow_ruleCounts D hD]
  exact W.prod_pow_le_prod_ofCounts_pow _

end

end PCFG
