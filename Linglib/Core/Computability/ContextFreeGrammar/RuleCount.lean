/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Rule counts of derivation trees

The count of a rule in a tree is the number of nonterminal nodes that apply it, and the rule counts
of a multiset of trees add the counts over its trees. A product over the local trees of a licensed
tree is then a product over the rules of the grammar, each raised to its count: this is how the
weight of a derivation under a weighted grammar depends on the tree only through its rule counts.

## Main definitions

* `RoseTree.ruleCount`: the number of applications of a rule in a tree.
* `RoseTree.ruleCounts`: the rule counts of a multiset of trees, as an additive homomorphism.

## Main results

* `RoseTree.Licensed.prod_map_localTrees`: a product over the local trees of a licensed tree is a
  product over the rules of the grammar, each raised to its count.
* `RoseTree.prod_map_localTrees_eq_prod_ruleCounts`: the same for a multiset of licensed trees.
* `RoseTree.Licensed.sum_ruleCount_eq_count_values`: the rules at a nonterminal are applied in a
  licensed tree as often as the nonterminal occurs.
* `ContextFreeGrammar.prod_inputs_prod_rulesWithInput`: a product over the rules of a grammar is a
  product over its nonterminals of the products over the rules at each.
-/

@[expose] public section

namespace RoseTree

variable {T N : Type*}

/-! ### Rule counts -/

section RuleCount

variable [DecidableEq T] [DecidableEq N]

/-- `ruleCount r t` counts the applications of the rule `r` in `t`, the nonterminal nodes whose
symbol and children's symbols spell out `r`. -/
def ruleCount (r : ContextFreeRule T N) (t : RoseTree (Symbol T N)) : ℕ := t.rules.count r

theorem ruleCount_node_nonterminal (r : ContextFreeRule T N) (A : N)
    (cs : List (RoseTree (Symbol T N))) :
    ruleCount r (node (.nonterminal A) cs) =
      (if r = ⟨A, cs.map value⟩ then 1 else 0) + (cs.map (ruleCount r)).sum := by
  rw [ruleCount, rules_node_nonterminal, List.count_cons, List.count_flatten, List.map_map,
    add_comm]
  exact congrArg₂ (· + ·) (if_congr (by rw [beq_iff_eq, eq_comm]) rfl rfl) rfl

theorem ruleCount_node_terminal (r : ContextFreeRule T N) (a : T)
    (cs : List (RoseTree (Symbol T N))) :
    ruleCount r (node (.terminal a) cs) = (cs.map (ruleCount r)).sum := by
  rw [ruleCount, rules_node_terminal, List.count_flatten, List.map_map]
  rfl

/-- The rule counts of a multiset of trees record how often each rule is applied across its
trees. -/
def ruleCounts : Multiset (RoseTree (Symbol T N)) →+ ContextFreeRule T N → ℕ where
  toFun D r := (D.map (ruleCount r)).sum
  map_zero' := by
    funext r
    simp
  map_add' D₁ D₂ := by
    funext r
    simp

theorem ruleCounts_apply (D : Multiset (RoseTree (Symbol T N))) (r : ContextFreeRule T N) :
    ruleCounts D r = (D.map (ruleCount r)).sum :=
  rfl

@[simp] theorem ruleCounts_singleton (t : RoseTree (Symbol T N)) (r : ContextFreeRule T N) :
    ruleCounts {t} r = ruleCount r t := by
  simp [ruleCounts_apply]

@[simp] theorem ruleCounts_cons (t : RoseTree (Symbol T N)) (D : Multiset (RoseTree (Symbol T N)))
    (r : ContextFreeRule T N) : ruleCounts (t ::ₘ D) r = ruleCount r t + ruleCounts D r := by
  simp [ruleCounts_apply]

end RuleCount

section BigOperators

variable {M : Type*} {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
  {F : Symbol T g.NT × List (Symbol T g.NT) → M}

/-- A product over the local trees of a licensed tree is a product over the rules it applies, for
a quantity that is `1` at terminal leaves. -/
@[to_additive /-- A total over the local trees of a licensed tree is a total over the rules it
applies, for a quantity that vanishes at terminal leaves. -/]
theorem Licensed.prod_map_localTrees_eq_prod_map_rules [Monoid M] (ht : t.Licensed g.Licenses)
    (hF : ∀ a, F (.terminal a, []) = 1) :
    (t.localTrees.map F).prod = (t.rules.map fun r ↦ F (.nonterminal r.input, r.output)).prod := by
  induction ht using Licensed.grammar_induction with
  | terminal a => simp [leaf, hF]
  | nonterminal A cs hrule hcs ih =>
    simp only [localTrees_node, rules_node_nonterminal, List.map_cons, List.prod_cons,
      List.map_flatten, List.prod_flatten, List.map_map, Function.comp_def]
    rw [List.map_congr_left ih]

variable [DecidableEq T] [DecidableEq g.NT]

/-- A product over the local trees of a licensed tree is a product over the rules of the grammar,
each raised to its count, for a quantity that is `1` at terminal leaves. -/
@[to_additive /-- A total over the local trees of a licensed tree is a total over the rules by
their counts, for a quantity that vanishes at terminal leaves. -/]
theorem Licensed.prod_map_localTrees [CommMonoid M] (ht : t.Licensed g.Licenses)
    (hF : ∀ a, F (.terminal a, []) = 1) :
    (t.localTrees.map F).prod =
      ∏ r ∈ g.rules, F (.nonterminal r.input, r.output) ^ ruleCount r t := by
  rw [ht.prod_map_localTrees_eq_prod_map_rules hF, Finset.prod_list_map_count]
  refine Finset.prod_subset (fun r hr ↦ ht.mem_of_mem_rules (List.mem_toFinset.mp hr)) ?_
  intro r _ hr
  rw [List.count_eq_zero_of_not_mem (mt List.mem_toFinset.mpr hr), pow_zero]

/-- A product over the local trees of a corpus of licensed trees is a product over the rules of
the grammar, each raised to its count, for a quantity that is `1` at terminal leaves. -/
@[to_additive /-- A total over the local trees of a corpus of licensed trees is a total over the
rules by their counts, for a quantity that vanishes at terminal leaves. -/]
theorem prod_map_localTrees_eq_prod_ruleCounts [CommMonoid M]
    {D : Multiset (RoseTree (Symbol T g.NT))} (hD : ∀ t ∈ D, t.Licensed g.Licenses)
    (hF : ∀ a, F (.terminal a, []) = 1) :
    (D.map fun t ↦ (t.localTrees.map F).prod).prod =
      ∏ r ∈ g.rules, F (.nonterminal r.input, r.output) ^ ruleCounts D r := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons t D ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih fun t' ht' ↦ hD t' (Multiset.mem_cons_of_mem ht'),
      (hD t (Multiset.mem_cons_self t D)).prod_map_localTrees hF, ← Finset.prod_mul_distrib]
    simp [pow_add]

/-- The rules at a nonterminal are applied in a licensed tree as often as the nonterminal
occurs. -/
theorem Licensed.sum_ruleCount_eq_count_values (ht : t.Licensed g.Licenses) (A : g.NT) :
    ∑ r ∈ g.rulesWithInput A, ruleCount r t = t.values.count (.nonterminal A) := by
  have hcount (l : List (Symbol T g.NT × List (Symbol T g.NT))) :
      (l.map fun p ↦ if p.1 = .nonterminal A then 1 else 0).sum =
        (l.map Prod.fst).count (.nonterminal A) := by
    induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, List.count_cons, ih, beq_iff_eq]
      exact add_comm _ _
  rw [← map_fst_localTrees, ← hcount, ht.sum_map_localTrees (by simp),
    ContextFreeGrammar.rulesWithInput, Finset.sum_filter]
  simp

end BigOperators

end RoseTree

namespace ContextFreeGrammar

variable {T : Type*}

/-- A product over the rules of a grammar is a product over the nonterminals it has a rule for
of the products over the rules at each. -/
@[to_additive /-- A sum over the rules of a grammar is a sum over the nonterminals it has a rule
for of the sums over the rules at each. -/]
theorem prod_inputs_prod_rulesWithInput {M : Type*} [CommMonoid M]
    (g : ContextFreeGrammar T) [DecidableEq g.NT] (f : ContextFreeRule T g.NT → M) :
    ∏ a ∈ g.inputs, ∏ r ∈ g.rulesWithInput a, f r = ∏ r ∈ g.rules, f r :=
  Finset.prod_fiberwise_of_maps_to (fun _ hr ↦ g.input_mem_inputs hr) f

end ContextFreeGrammar
