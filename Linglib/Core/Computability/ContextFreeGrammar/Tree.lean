/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar
public import Linglib.Core.Data.RoseTree.Licensed
public import Linglib.Core.Data.RoseTree.Span
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Derivation trees of a context-free grammar

A derivation tree, or parse tree, of a context-free grammar is a rose tree over its symbols,
`RoseTree (Symbol T N)`. A grammar licenses a tree when every terminal node is a leaf and every
nonterminal node, read with the symbols of its children, is a rule: the trees a grammar licenses
are the local set of its rules. The yield of a tree is the list of terminals at its leaves, left to
right, and its rules are the rules its nonterminal nodes apply.

A symbol derives a word exactly when some licensed tree has that symbol at its root and that word
as its yield, so the language of a grammar is the set of yields of its derivation trees.

## Main definitions

* `RoseTree.yield`: the terminal frontier.
* `ContextFreeGrammar.Licenses g`: the local trees the grammar `g` licenses.
* `ContextFreeGrammar.derivationTrees`: the licensed trees with the start symbol at the root.
* `RoseTree.rule?`, `RoseTree.rules`, `RoseTree.ruleAt?`: the rule applied at the root, the rules
  applied in a tree, and the rule applied at a Gorn address.
* `RoseTree.ruleCount`, `RoseTree.ruleCounts`: the number of applications of a rule in a tree,
  and the rule counts of a multiset of trees.

## Main results

* `ContextFreeGrammar.derives_iff_exists_licensed`: a symbol derives a word if and only if a
  licensed tree has the symbol at its root and the word as its yield.
* `ContextFreeGrammar.image_yield_derivationTrees`: the language is the set of yields of the
  derivation trees.
* `RoseTree.Licensed.prod_map_localTrees`: a product over the local trees of a licensed tree is a
  product over the rules of the grammar, each raised to its count.
* `RoseTree.Licensed.map_mapNonterminal`: a relabelling of nonterminals that sends rules to rules
  sends licensed trees to licensed trees.
* `RoseTree.Licensed.exists_repeat`: a long enough path in a licensed tree passes two nodes with
  the same nonterminal.

## Implementation notes

A derivation tree is a tree over symbols together with a proof that the grammar licenses it, and
not an inductive family indexed by the root nonterminal with one constructor per rule. The trees of
all grammars over the same symbols then share one type, so that relabelling, subtrees, Gorn
addresses and grafting are those of `RoseTree`, and a tree can be tested against several grammars.

A nonterminal without children is an application of a rule with empty right-hand side. A tree
therefore has no open nonterminals, and the trees here describe derivations of words, not of
sentential forms.

The nonterminals of a grammar are a field of the grammar, so `decide` tests a concrete tree against
a grammar `g` when the tree is typed over `g.NT` and `g.NT` has decidable equality.

## References

* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

namespace RoseTree

variable {T N : Type*}

/-! ### The yield -/

/-- The terminal frontier of a tree lists the terminals among its leaves, left to right. -/
def yield (t : RoseTree (Symbol T N)) : List T := t.leafList.filterMap Symbol.terminal?

@[simp] theorem yield_node_nil (s : Symbol T N) : yield (node s []) = s.terminal?.toList := by
  cases s <;> simp [yield]

@[simp] theorem yield_leaf (s : Symbol T N) : yield (leaf s) = s.terminal?.toList :=
  yield_node_nil s

theorem yield_node_of_ne_nil (s : Symbol T N) {cs : List (RoseTree (Symbol T N))} (h : cs ≠ []) :
    yield (node s cs) = (cs.map yield).flatten :=
  filterMap_leafList_node_of_ne_nil _ s h

@[simp] theorem yield_node_cons (s : Symbol T N) (c : RoseTree (Symbol T N))
    (cs : List (RoseTree (Symbol T N))) :
    yield (node s (c :: cs)) = ((c :: cs).map yield).flatten :=
  yield_node_of_ne_nil s (List.cons_ne_nil c cs)

@[simp] theorem yield_node_nonterminal (A : N) (cs : List (RoseTree (Symbol T N))) :
    yield (node (.nonterminal A) cs) = (cs.map yield).flatten :=
  filterMap_leafList_node_of_eq_none rfl cs

@[simp] theorem yield_map {N' : Type*} (f : N → N') (t : RoseTree (Symbol T N)) :
    (t.map (Symbol.mapNonterminal f)).yield = t.yield := by
  simp only [yield, leafList_map, List.filterMap_map, Function.comp_def,
    Symbol.terminal?_mapNonterminal]

theorem yield_replaceAt {t s : RoseTree (Symbol T N)} {p : List ℕ} (h : t[p]? = some s) :
    ∃ pre post : List T, t.yield = pre ++ s.yield ++ post ∧
      ∀ new : RoseTree (Symbol T N), (t.replaceAt p new).yield = pre ++ new.yield ++ post := by
  refine ⟨(t.leafList.take (t.leafIndex p)).filterMap Symbol.terminal?,
    (t.leafList.drop (t.leafIndex p + s.numLeaves)).filterMap Symbol.terminal?, ?_, fun new ↦ ?_⟩
  · conv_lhs => rw [yield, ← take_append_leafList_append_drop h]
    simp only [yield, List.filterMap_append]
  · simp only [yield, leafList_replaceAt h, List.filterMap_append]

/-! ### Licensing -/

/-- A grammar licenses a local tree when it is a terminal without children, or a nonterminal
whose children's symbols are the right-hand side of one of its rules. -/
def _root_.ContextFreeGrammar.Licenses (g : ContextFreeGrammar T) :
    Symbol T g.NT → List (Symbol T g.NT) → Prop
  | .terminal _, ks => ks = []
  | .nonterminal A, ks => ⟨A, ks⟩ ∈ g.rules

@[simp] theorem _root_.ContextFreeGrammar.licenses_terminal {g : ContextFreeGrammar T} {a : T}
    {ks : List (Symbol T g.NT)} : g.Licenses (.terminal a) ks ↔ ks = [] := .rfl

@[simp] theorem _root_.ContextFreeGrammar.licenses_nonterminal {g : ContextFreeGrammar T}
    {A : g.NT} {ks : List (Symbol T g.NT)} : g.Licenses (.nonterminal A) ks ↔ ⟨A, ks⟩ ∈ g.rules :=
  .rfl

instance {g : ContextFreeGrammar T} [DecidableEq T] [DecidableEq g.NT] :
    ∀ (s : Symbol T g.NT) (ks : List (Symbol T g.NT)), Decidable (g.Licenses s ks)
  | .terminal _, ks => inferInstanceAs (Decidable (ks = []))
  | .nonterminal A, ks => inferInstanceAs (Decidable (⟨A, ks⟩ ∈ g.rules))

theorem licensed_node_terminal_iff {g : ContextFreeGrammar T} {a : T}
    {cs : List (RoseTree (Symbol T g.NT))} :
    (node (.terminal a) cs).Licensed g.Licenses ↔ cs = [] :=
  ⟨fun h ↦ List.map_eq_nil_iff.mp h.rel_root, fun h ↦ h ▸ licensed_leaf_iff.mpr rfl⟩

theorem licensed_node_nonterminal_iff {g : ContextFreeGrammar T} {A : g.NT}
    {cs : List (RoseTree (Symbol T g.NT))} :
    (node (.nonterminal A) cs).Licensed g.Licenses ↔
      ⟨A, cs.map value⟩ ∈ g.rules ∧ ∀ c ∈ cs, c.Licensed g.Licenses :=
  licensed_node_iff

namespace Licensed

variable {g : ContextFreeGrammar T}

theorem terminal (a : T) : (leaf (.terminal a) : RoseTree (Symbol T g.NT)).Licensed g.Licenses :=
  licensed_leaf_iff.mpr rfl

theorem nonterminal (A : g.NT) (cs : List (RoseTree (Symbol T g.NT)))
    (hrule : ⟨A, cs.map value⟩ ∈ g.rules) (hcs : ∀ c ∈ cs, c.Licensed g.Licenses) :
    (node (.nonterminal A) cs).Licensed g.Licenses :=
  licensed_node_iff.mpr ⟨hrule, hcs⟩

theorem rule_mem {A : g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : (node (.nonterminal A) cs).Licensed g.Licenses) : ⟨A, cs.map value⟩ ∈ g.rules :=
  h.rel_root

theorem eq_nil_of_terminal {a : T} {cs : List (RoseTree (Symbol T g.NT))}
    (h : (node (.terminal a) cs).Licensed g.Licenses) : cs = [] :=
  List.map_eq_nil_iff.mp h.rel_root

theorem exists_nonterminal_of_ne_nil {s : Symbol T g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : (node s cs).Licensed g.Licenses) (hcs : cs ≠ []) : ∃ A, s = .nonterminal A := by
  cases s with
  | terminal => exact absurd h.eq_nil_of_terminal hcs
  | nonterminal A => exact ⟨A, rfl⟩

@[elab_as_elim]
theorem grammar_induction
    {motive : (t : RoseTree (Symbol T g.NT)) → t.Licensed g.Licenses → Prop}
    (terminal : ∀ a, motive (leaf (.terminal a)) (terminal a))
    (nonterminal : ∀ A cs (hrule : ⟨A, cs.map value⟩ ∈ g.rules)
      (hcs : ∀ c ∈ cs, c.Licensed g.Licenses), (∀ c (hc : c ∈ cs), motive c (hcs c hc)) →
        motive (node (.nonterminal A) cs) (.nonterminal A cs hrule hcs))
    {t : RoseTree (Symbol T g.NT)} (ht : t.Licensed g.Licenses) : motive t ht := by
  induction ht using RoseTree.Licensed.induction with
  | node s cs hR hcs ih =>
    cases s with
    | terminal a => obtain rfl : cs = [] := List.map_eq_nil_iff.mp hR; exact terminal a
    | nonterminal A => exact nonterminal A cs hR hcs ih

/-- A licensed tree whose root is the terminal `a` has yield `[a]`. -/
theorem yield_eq_of_value_terminal {t : RoseTree (Symbol T g.NT)} (ht : t.Licensed g.Licenses)
    {a : T} (hv : t.value = .terminal a) : t.yield = [a] := by
  induction ht using grammar_induction with
  | terminal b =>
    obtain rfl : b = a := by simpa [leaf] using hv
    simp [leaf]
  | nonterminal => simp at hv

/-- A relabelling of nonterminals that sends rules to rules sends licensed trees to licensed
trees. -/
theorem map_mapNonterminal {g' : ContextFreeGrammar T} {f : g.NT → g'.NT}
    (hf : ∀ r ∈ g.rules, r.mapNonterminal f ∈ g'.rules) {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) : (t.map (Symbol.mapNonterminal f)).Licensed g'.Licenses :=
  licensed_map.mpr <| ht.mono fun s ks h ↦ by
    cases s with
    | terminal a => obtain rfl : ks = [] := h; rfl
    | nonterminal A => exact hf ⟨A, ks⟩ h

end Licensed

/-! ### The rules of a tree -/

section Rules

variable {N' : Type*}

/-- The rule applied at the root of a tree is the nonterminal there with the symbols of its
children; a terminal applies none. -/
def rule? : RoseTree (Symbol T N) → Option (ContextFreeRule T N)
  | node (.nonterminal A) cs => some ⟨A, cs.map value⟩
  | node (.terminal _) _ => none

@[simp] theorem rule?_node_nonterminal (A : N) (cs : List (RoseTree (Symbol T N))) :
    (node (.nonterminal A) cs).rule? = some ⟨A, cs.map value⟩ := rfl

@[simp] theorem rule?_node_terminal (a : T) (cs : List (RoseTree (Symbol T N))) :
    (node (.terminal a) cs).rule? = none := rfl

theorem rule?_eq_some_iff {t : RoseTree (Symbol T N)} {r : ContextFreeRule T N} :
    t.rule? = some r ↔ t.value = .nonterminal r.input ∧ t.children.map value = r.output := by
  obtain ⟨s, cs⟩ := t
  obtain ⟨A, w⟩ := r
  cases s <;> simp [eq_comm]

@[simp] theorem rule?_map (f : N → N') (t : RoseTree (Symbol T N)) :
    (t.map (Symbol.mapNonterminal f)).rule? = t.rule?.map (ContextFreeRule.mapNonterminal f) := by
  obtain ⟨s, cs⟩ := t
  cases s <;> simp [ContextFreeRule.mapNonterminal, Function.comp_def]

/-- The rules of a tree are the rules its nonterminal nodes apply, in preorder. -/
def rules (t : RoseTree (Symbol T N)) : List (ContextFreeRule T N) := t.subtrees.filterMap rule?

@[simp] theorem rules_node_nonterminal (A : N) (cs : List (RoseTree (Symbol T N))) :
    (node (.nonterminal A) cs).rules = ⟨A, cs.map value⟩ :: (cs.map rules).flatten := by
  rw [rules, subtrees_node, List.filterMap_cons_some (rule?_node_nonterminal A cs),
    List.flatMap_def, List.filterMap_flatten, List.map_map]
  rfl

@[simp] theorem rules_node_terminal (a : T) (cs : List (RoseTree (Symbol T N))) :
    (node (.terminal a) cs).rules = (cs.map rules).flatten := by
  rw [rules, subtrees_node, List.filterMap_cons_none (rule?_node_terminal a cs),
    List.flatMap_def, List.filterMap_flatten, List.map_map]
  rfl

theorem mem_rules {t : RoseTree (Symbol T N)} {r : ContextFreeRule T N} :
    r ∈ t.rules ↔ ∃ s, IsSubtree s t ∧ s.rule? = some r := by
  simp [rules, mem_subtrees]

@[simp] theorem rules_map (f : N → N') (t : RoseTree (Symbol T N)) :
    (t.map (Symbol.mapNonterminal f)).rules = t.rules.map (ContextFreeRule.mapNonterminal f) := by
  simp [rules, subtrees_map, List.filterMap_map, List.map_filterMap]

/-- A licensed tree applies only rules of the grammar. -/
theorem Licensed.mem_rules {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) {r : ContextFreeRule T g.NT} (hr : r ∈ t.rules) : r ∈ g.rules := by
  obtain ⟨s, hs, hr⟩ := RoseTree.mem_rules.mp hr
  obtain ⟨hv, hc⟩ := rule?_eq_some_iff.mp hr
  have h := ht s hs
  rwa [hv, hc] at h

/-- The rule applied at a Gorn address is the nonterminal there with the symbols of its children,
and `none` off the tree or at a terminal. -/
def ruleAt? (t : RoseTree (Symbol T N)) (p : List ℕ) : Option (ContextFreeRule T N) :=
  t[p]?.bind rule?

@[simp] theorem ruleAt?_nil (t : RoseTree (Symbol T N)) : ruleAt? t [] = t.rule? := by
  simp [ruleAt?]

theorem ruleAt?_eq_some {t : RoseTree (Symbol T N)} {p : List ℕ} {A : N}
    {cs : List (RoseTree (Symbol T N))} (h : t[p]? = some (node (.nonterminal A) cs)) :
    ruleAt? t p = some ⟨A, cs.map value⟩ := by
  simp [ruleAt?, h]

theorem Licensed.exists_mem_output_of_isSubtree {g : ContextFreeGrammar T}
    {t s : RoseTree (Symbol T g.NT)} (ht : t.Licensed g.Licenses) (hs : IsSubtree s t)
    (hne : s ≠ t) : ∃ r ∈ g.rules, s.value ∈ r.output := by
  obtain rfl | ⟨u, hsu, hut⟩ := hs.cases_head
  · exact absurd rfl hne
  have hlic := ht u hut
  obtain ⟨b, cs⟩ := u
  cases b with
  | terminal a => exact absurd hsu (by simp [ContextFreeGrammar.Licenses] at hlic; simp [hlic])
  | nonterminal A =>
    exact ⟨⟨A, cs.map value⟩, hlic, List.mem_map_of_mem hsu⟩

end Rules

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
  exact Finset.prod_subset (fun r hr ↦ ht.mem_rules (List.mem_toFinset.mp hr)) fun r _ hr ↦ by
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

theorem Licensed.exists_getElem?_take {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) {p : List ℕ} {s : RoseTree (Symbol T g.NT)}
    (hs : t[p]? = some s)
    (hh : 1 < s.height) {k : ℕ} (hk : k ≤ p.length) :
    ∃ A cs, t[p.take k]? = some (node (.nonterminal A) cs) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (getElem?_take_isSome hs k)
  obtain ⟨s₀, cs, rfl⟩ : ∃ s₀ cs, u = node s₀ cs := by cases u; exact ⟨_, _, rfl⟩
  have hne : cs ≠ [] := by
    rcases Nat.lt_or_ge k p.length with hlt | hge
    · rw [← List.take_append_drop k p, getElem?_append, hu, Option.bind_some,
        List.drop_eq_getElem_cons hlt] at hs
      obtain ⟨c, hc, -⟩ := getElem?_cons_eq_some_iff.mp hs
      exact List.ne_nil_of_mem (List.mem_of_getElem? hc)
    · rw [List.take_of_length_le (le_antisymm hk hge ▸ le_rfl), hs] at hu
      obtain rfl := Option.some.inj hu
      obtain ⟨c, hc, -⟩ := exists_mem_children_height_add_one hh
      exact List.ne_nil_of_mem hc
  obtain ⟨A, rfl⟩ := (ht.of_getElem? hu).exists_nonterminal_of_ne_nil hne
  exact ⟨A, cs, hu⟩

/-- By pigeonhole, a path of at least `g.rules.card` steps through a licensed tree, ending at a
node with children, passes two nodes with the same nonterminal. -/
theorem Licensed.exists_repeat {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) {p : List ℕ} {s : RoseTree (Symbol T g.NT)}
    (hs : t[p]? = some s)
    (hh : 1 < s.height) (hlen : g.rules.card ≤ p.length) :
    ∃ i j, i < j ∧ j ≤ p.length ∧ ∃ A csᵢ csⱼ,
      t[p.take i]? = some (node (.nonterminal A) csᵢ) ∧
      t[p.take j]? = some (node (.nonterminal A) csⱼ) := by
  classical
  let f : ℕ → ContextFreeRule T g.NT := fun k ↦ (ruleAt? t (p.take k)).getD ⟨g.initial, []⟩
  have hf : ∀ k ∈ Finset.range (p.length + 1), f k ∈ g.rules := fun k hk ↦ by
    obtain ⟨A, cs, hA⟩ :=
      ht.exists_getElem?_take hs hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simp only [f, ruleAt?_eq_some hA, Option.getD_some]
    exact (ht.of_getElem? hA).rule_mem
  obtain ⟨a, ha, b, hb, hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp only [Finset.card_range]; omega) hf
  wlog hab : a < b generalizing a b
  · exact this b hb a ha hne.symm hfeq.symm (lt_of_le_of_ne (not_lt.mp hab) hne.symm)
  rw [Finset.mem_range] at ha hb
  obtain ⟨A, csₐ, hA⟩ := ht.exists_getElem?_take hs hh (Nat.lt_succ_iff.mp ha)
  obtain ⟨B, cs_b, hB⟩ := ht.exists_getElem?_take hs hh (Nat.lt_succ_iff.mp hb)
  have : A = B := by
    have h := hfeq
    simp only [f, ruleAt?_eq_some hA, ruleAt?_eq_some hB, Option.getD_some,
      ContextFreeRule.mk.injEq] at h
    exact h.1
  subst this
  exact ⟨a, b, hab, Nat.lt_succ_iff.mp hb, A, csₐ, cs_b, hA, hB⟩

end RoseTree

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

/-! ### Soundness and completeness -/

private theorem derives_flatten_yield {cs : List (RoseTree (Symbol T g.NT))}
    (h : ∀ c ∈ cs, g.Derives [c.value] (c.yield.map Symbol.terminal)) :
    g.Derives (cs.map RoseTree.value) ((cs.map RoseTree.yield).flatten.map Symbol.terminal) := by
  induction cs with
  | nil => exact Relation.ReflTransGen.refl
  | cons c cs ih =>
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.map_append, ← List.singleton_append]
    exact ((h c (List.mem_cons_self ..)).append_right _).trans
      ((ih fun d hd ↦ h d (List.mem_cons_of_mem _ hd)).append_left _)

/-- A licensed tree derives its yield from its root symbol. -/
theorem _root_.RoseTree.Licensed.derives {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) :
    g.Derives [t.value] (t.yield.map Symbol.terminal) := by
  induction ht using RoseTree.Licensed.grammar_induction with
  | terminal a => simp [RoseTree.leaf]; exact Relation.ReflTransGen.refl
  | nonterminal A cs hrule _ ih =>
    rw [RoseTree.value_node, RoseTree.yield_node_nonterminal]
    exact (Produces.single ⟨⟨A, cs.map RoseTree.value⟩, hrule,
      ContextFreeRule.Rewrites.input_output⟩).trans (derives_flatten_yield ih)

private theorem exists_forest {sf : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives sf (w.map Symbol.terminal)) :
    ∃ ts : List (RoseTree (Symbol T g.NT)), ts.map RoseTree.value = sf ∧
      (∀ t ∈ ts, t.Licensed g.Licenses) ∧ (ts.map RoseTree.yield).flatten = w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨w.map fun a ↦ RoseTree.leaf (.terminal a), ?_, ?_, ?_⟩
    · simp [Function.comp_def, RoseTree.leaf]
    · rintro t ht
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
      exact .terminal a
    · induction w <;> simp_all
  | head hstep _ ih =>
    obtain ⟨ts, hroot, hvalid, hyield⟩ := ih
    obtain ⟨r, hr, hrew⟩ := hstep
    obtain ⟨p, q, hsf, hc⟩ := hrew.exists_parts
    subst hsf hc
    have hlen : p.length + r.output.length ≤ ts.length := by
      have := congrArg List.length hroot; simp at this; omega
    refine ⟨ts.take p.length ++ [RoseTree.node (.nonterminal r.input)
      ((ts.drop p.length).take r.output.length)] ++ ts.drop (p.length + r.output.length),
      ?_, ?_, ?_⟩
    · have h1 : (ts.take p.length).map RoseTree.value = p := by
        rw [List.map_take, hroot]; simp
      have h2 : ((ts.drop p.length).take r.output.length).map RoseTree.value = r.output := by
        rw [List.map_take, List.map_drop, hroot]; simp
      have h3 : (ts.drop (p.length + r.output.length)).map RoseTree.value = q := by
        rw [List.map_drop, hroot]; simp
      simp only [List.map_append, List.map_cons, List.map_nil, RoseTree.value_node, h1, h3]
    · intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | rfl) | ht
      · exact hvalid t (List.mem_of_mem_take ht)
      · refine .nonterminal r.input _ ?_ fun c hc ↦
          hvalid c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
        rw [List.map_take, List.map_drop, hroot]; simpa using hr
      · exact hvalid t (List.mem_of_mem_drop ht)
    · have hsplit : ts = ts.take p.length ++ (ts.drop p.length).take r.output.length ++
          ts.drop (p.length + r.output.length) := by
        rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
      conv_rhs => rw [← hyield, hsplit]
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, RoseTree.yield_node_nonterminal]

/-- A string of symbols derives a word if and only if the word is the concatenation of the
yields of licensed trees with those symbols at their roots. -/
theorem derives_iff_exists_forest {sf : List (Symbol T g.NT)} {w : List T} :
    g.Derives sf (w.map Symbol.terminal) ↔
      ∃ ts : List (RoseTree (Symbol T g.NT)), ts.map RoseTree.value = sf ∧
        (∀ t ∈ ts, t.Licensed g.Licenses) ∧ (ts.map RoseTree.yield).flatten = w := by
  refine ⟨exists_forest, ?_⟩
  rintro ⟨ts, rfl, hts, rfl⟩
  exact derives_flatten_yield fun t ht ↦ (hts t ht).derives

/-- A symbol derives a word if and only if a licensed tree has the symbol at its root and the
word as its yield. -/
theorem derives_iff_exists_licensed {s : Symbol T g.NT} {w : List T} :
    g.Derives [s] (w.map Symbol.terminal) ↔
      ∃ t : RoseTree (Symbol T g.NT), t.Licensed g.Licenses ∧ t.yield = w ∧ t.value = s := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨ts, hroot, hvalid, hyield⟩ := exists_forest h
    obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> simp at hroot
      exact ⟨t, rfl⟩
    exact ⟨t, hvalid t (List.mem_singleton_self t), by simpa using hyield, by simpa using hroot⟩
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ht.derives

/-- The derivation trees of a grammar are the trees it licenses with the start symbol at the
root. -/
def derivationTrees (g : ContextFreeGrammar T) : Set (RoseTree (Symbol T g.NT)) :=
  {t | t.Licensed g.Licenses ∧ t.value = .nonterminal g.initial}

theorem mem_derivationTrees {t : RoseTree (Symbol T g.NT)} :
    t ∈ g.derivationTrees ↔ t.Licensed g.Licenses ∧ t.value = .nonterminal g.initial := .rfl

/-- A word is in the language if and only if it is the yield of a derivation tree. -/
theorem mem_language_iff_exists_mem_derivationTrees {w : List T} :
    w ∈ g.language ↔ ∃ t ∈ g.derivationTrees, t.yield = w := by
  rw [mem_language_iff, derives_iff_exists_licensed]
  exact exists_congr fun t ↦ by rw [mem_derivationTrees, and_assoc, and_comm (a := t.yield = w)]

/-- The language of a grammar is the set of yields of its derivation trees. -/
theorem image_yield_derivationTrees (g : ContextFreeGrammar T) :
    RoseTree.yield '' g.derivationTrees = g.language :=
  Set.ext fun _ ↦ mem_language_iff_exists_mem_derivationTrees.symm

/-- Every word of the language has a licensed derivation tree from the start symbol. -/
theorem exists_licensed_tree (g : ContextFreeGrammar T) {w : List T} (hw : w ∈ g.language) :
    ∃ t : RoseTree (Symbol T g.NT), t.Licensed g.Licenses ∧ t.yield = w ∧
      t.value = .nonterminal g.initial :=
  derives_iff_exists_licensed.mp hw

/-- A product over the rules of a grammar is a product over the nonterminals it has a rule for
of the products over the rules at each. -/
@[to_additive /-- A sum over the rules of a grammar is a sum over the nonterminals it has a rule
for of the sums over the rules at each. -/]
theorem prod_inputs_prod_rulesWithInput {M : Type*} [CommMonoid M]
    (g : ContextFreeGrammar T) [DecidableEq g.NT] (f : ContextFreeRule T g.NT → M) :
    ∏ a ∈ g.inputs, ∏ r ∈ g.rulesWithInput a, f r = ∏ r ∈ g.rules, f r :=
  Finset.prod_fiberwise_of_maps_to (fun _ hr ↦ g.input_mem_inputs hr) f

end ContextFreeGrammar
