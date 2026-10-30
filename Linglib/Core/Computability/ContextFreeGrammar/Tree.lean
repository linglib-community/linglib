/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar
public import Linglib.Core.Data.RoseTree.Licensed
public import Linglib.Core.Data.RoseTree.Span
public import Linglib.Core.Data.RoseTree.Encodable
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find

/-!
# Derivation trees of a context-free grammar

A derivation tree, or parse tree, of a context-free grammar is a rose tree over its symbols,
`RoseTree (Symbol T N)`. A grammar licenses a tree when every terminal node is a leaf and every
nonterminal node, read with the symbols of its children, is a rule: the trees a grammar licenses
are the local set of its rules (`RoseTree.Licensed`). The yield of a tree is the list of terminals
at its leaves, left to right.

## Main definitions

* `RoseTree.yield`: the terminal frontier.
* `ContextFreeGrammar.Licenses g`: the local trees the grammar `g` licenses.
* `RoseTree.ruleCount`, `RoseTree.ruleCounts`: the number of applications of a rule in a tree,
  and the rule counts of a multiset of trees.
* `RoseTree.ruleAt?`: the rule applied at a Gorn address.

## Main results

* `RoseTree.Licensed.derives`: a licensed tree derives its yield from its root symbol.
* `ContextFreeGrammar.exists_licensed_tree`: every word of the language has a licensed derivation
  tree from the start symbol.
* `RoseTree.Licensed.replaceAt`, `RoseTree.Licensed.exists_repeat`: replacing a subtree by one
  with the same root symbol keeps the tree licensed, and a long enough path in a licensed tree
  passes two nodes with the same nonterminal; together with `RoseTree.numNodes_replaceAt_lt` these
  are the ingredients of the pumping lemma.
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
    yield (node s cs) = (cs.map yield).flatten := by
  rw [yield, leafList_node_of_ne_nil _ h, List.filterMap_flatten, List.map_map]
  rfl

@[simp] theorem yield_node_cons (s : Symbol T N) (c : RoseTree (Symbol T N))
    (cs : List (RoseTree (Symbol T N))) :
    yield (node s (c :: cs)) = ((c :: cs).map yield).flatten :=
  yield_node_of_ne_nil s (List.cons_ne_nil c cs)

@[simp] theorem yield_node_nonterminal (A : N) (cs : List (RoseTree (Symbol T N))) :
    yield (node (.nonterminal A) cs) = (cs.map yield).flatten := by
  cases cs with
  | nil => simp
  | cons c cs => exact yield_node_cons _ c cs

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

end Licensed

/-! ### Rule counts -/

section RuleCount

variable [DecidableEq T] [DecidableEq N]

/-- `ruleCount r t` counts the applications of the rule `r` in `t`, the nonterminal nodes whose
symbol and children's symbols spell out `r`. -/
def ruleCount (r : ContextFreeRule T N) (t : RoseTree (Symbol T N)) : ℕ :=
  t.localTrees.count (.nonterminal r.input, r.output)

theorem ruleCount_node_nonterminal (r : ContextFreeRule T N) (A : N)
    (cs : List (RoseTree (Symbol T N))) :
    ruleCount r (node (.nonterminal A) cs) =
      (if r = ⟨A, cs.map value⟩ then 1 else 0) + (cs.map (ruleCount r)).sum := by
  simp only [ruleCount, localTrees_node, List.count_cons, List.count_flatten, List.map_map,
    Function.comp_def, beq_iff_eq, Prod.mk.injEq, Symbol.nonterminal.injEq]
  rw [add_comm]
  congr 1
  cases r
  simp [ContextFreeRule.mk.injEq, eq_comm]

theorem ruleCount_node_terminal (r : ContextFreeRule T N) (a : T)
    (cs : List (RoseTree (Symbol T N))) :
    ruleCount r (node (.terminal a) cs) = (cs.map (ruleCount r)).sum := by
  simp only [ruleCount, localTrees_node, List.count_cons, List.count_flatten, List.map_map,
    Function.comp_def, beq_iff_eq, Prod.mk.injEq, reduceCtorEq, false_and, ite_false, add_zero]
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

end RuleCount

/-! ### The rule at an address -/

/-- The rule applied at a Gorn address is the nonterminal there with the symbols of its children,
and `none` off the tree or at a terminal. -/
def ruleAt? {g : ContextFreeGrammar T} (t : RoseTree (Symbol T g.NT)) (p : List ℕ) :
    Option (ContextFreeRule T g.NT) :=
  (t[p]?).bind fun s ↦ match s.value with
    | .nonterminal A => some ⟨A, s.children.map value⟩
    | .terminal _ => none

theorem ruleAt?_eq_some {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)} {p : List ℕ}
    {A : g.NT} {cs : List (RoseTree (Symbol T g.NT))}
    (h : t[p]? = some (node (.nonterminal A) cs)) :
    ruleAt? t p = some ⟨A, cs.map value⟩ := by
  simp [ruleAt?, h]

theorem ruleAt?_nil_eq_some_iff {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    {r : ContextFreeRule T g.NT} :
    ruleAt? t [] = some r ↔ t.value = .nonterminal r.input ∧ t.children.map value = r.output := by
  obtain ⟨s, cs⟩ := t
  obtain ⟨A, w⟩ := r
  cases s <;> simp [ruleAt?, eq_comm]

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

theorem Licensed.sum_ruleCount_eq_count_values [DecidableEq T] {g : ContextFreeGrammar T}
    [DecidableEq g.NT] {t : RoseTree (Symbol T g.NT)} (ht : t.Licensed g.Licenses) (A : g.NT) :
    ∑ r ∈ g.rules.filter (·.input = A), ruleCount r t = t.values.count (.nonterminal A) := by
  induction ht using Licensed.grammar_induction with
  | terminal a => simp [leaf, ruleCount_node_terminal]
  | nonterminal B cs hrule hcs ih =>
    have hsum (cs' : List (RoseTree (Symbol T g.NT))) (hcs' : ∀ c ∈ cs', c ∈ cs) :
        ∑ r ∈ g.rules.filter (·.input = A), (cs'.map (ruleCount r)).sum =
          (cs'.map fun c ↦ c.values.count (.nonterminal A)).sum := by
      induction cs' with
      | nil => simp
      | cons c cs' ihc =>
        simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
        rw [ih c (hcs' c (List.mem_cons_self ..)),
          ihc fun c' hc' ↦ hcs' c' (List.mem_cons_of_mem _ hc')]
    simp only [ruleCount_node_nonterminal, Finset.sum_add_distrib, hsum cs fun _ h ↦ h,
      values_node, List.count_cons, List.count_flatten, List.map_map, Function.comp_def,
      Finset.sum_ite_eq', Finset.mem_filter, beq_iff_eq, Symbol.nonterminal.injEq]
    by_cases hB : B = A
    · subst hB
      simp [hrule, add_comm]
    · simp [hB]

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

theorem Licensed.exists_min_numNodes {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) :
    ∃ t' : RoseTree (Symbol T g.NT), t'.Licensed g.Licenses ∧ t'.yield = t.yield ∧
      t'.value = t.value ∧ ∀ t'' : RoseTree (Symbol T g.NT), t''.Licensed g.Licenses →
        t''.yield = t.yield → t''.value = t.value → t'.numNodes ≤ t''.numNodes := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ t' : RoseTree (Symbol T g.NT),
    t'.Licensed g.Licenses ∧ t'.yield = t.yield ∧ t'.value = t.value ∧ t'.numNodes = n
  have hP : ∃ n, P n := ⟨t.numNodes, t, ht, rfl, rfl, rfl⟩
  obtain ⟨t', h₁, h₂, h₃, h₄⟩ := Nat.find_spec hP
  exact ⟨t', h₁, h₂, h₃, fun t'' hv hy hr ↦ h₄ ▸ Nat.find_le ⟨t'', hv, hy, hr, rfl⟩⟩

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

/-- **Soundness.** A licensed tree derives its yield from its root symbol. -/
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

/-- **Completeness.** Every word of the language has a licensed derivation tree from the start
symbol. -/
theorem exists_licensed_tree (g : ContextFreeGrammar T) {w : List T} (hw : w ∈ g.language) :
    ∃ t : RoseTree (Symbol T g.NT), t.Licensed g.Licenses ∧ t.yield = w ∧
      t.value = .nonterminal g.initial := by
  obtain ⟨ts, hroot, hvalid, hyield⟩ := exists_forest (g := g) hw
  obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> simp at hroot
    exact ⟨t, rfl⟩
  exact ⟨t, hvalid t (List.mem_singleton_self t), by simpa using hyield, by simpa using hroot⟩

end ContextFreeGrammar
