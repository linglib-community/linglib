/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Tree.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.Abel

/-!
# The pumping lemma for context-free languages

This file proves that [every context-free language has the pumping
property](##Language.IsContextFree.hasCFLPumpingProperty): beyond some length, every word splits as
`u ++ v ++ x ++ y ++ z` with `v ++ x ++ y` short and `v ++ y` nonempty, and every
`u ++ vⁱ ++ x ++ yⁱ ++ z` is in the language. A licensed tree of height `h` [has at most
`maxBranch ^ (h - 1)` terminals](##RoseTree.Licensed.length_yield_le), so a tree of a long word
[is taller than the number of rules](##RoseTree.Licensed.card_rules_add_one_lt_height) and [has a
low subtree with a proper subtree of the same
nonterminal](##RoseTree.Licensed.exists_repeat_of_lt_height). [Grafting the one into the
other](##RoseTree.Licensed.exists_pump) pumps the word, and in a tree with the fewest nodes the
pumped pieces are not both empty.

Arguments by counting letters need only the pumped pieces `t = v ++ y` as a multiset: `t` is a
nonempty sublist of the short infix `v ++ x ++ y`, and for every `i` the language has a word whose
letters are those of the original with `t` taken `i` times
(`Language.IsContextFree.exists_pump_multiset`).

## References

* [Y. Bar-Hillel, M. Perles and E. Shamir, *On formal properties of simple phrase structure
  grammars* (1961)][bar-hillel-perles-shamir-1961]
* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

open RoseTree List

/-- A language has the pumping property when, beyond some length, every word splits as
`u ++ v ++ x ++ y ++ z` with `v ++ x ++ y` no longer than that length, `v ++ y` nonempty, and every
`u ++ vⁱ ++ x ++ yⁱ ++ z` in the language. -/
def Language.HasCFLPumpingProperty {α : Type*} (L : Language α) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
    ∃ u v x y z : List α, w = u ++ v ++ x ++ y ++ z ∧ (v ++ x ++ y).length ≤ p ∧
      v ++ y ≠ [] ∧
      ∀ i : ℕ, u ++ (replicate i v).flatten ++ x ++ (replicate i y).flatten ++ z ∈ L

namespace ContextFreeGrammar

variable {T : Type*} (g : ContextFreeGrammar T)

/-- The branching bound of a grammar is the length of its longest right-hand side, and at least
`2`. -/
def maxBranch : ℕ := max 2 (g.rules.sup fun r ↦ r.output.length)

/-- The pumping constant is `maxBranch ^ (rules.card + 1)`, so that a licensed tree with as many
terminals has a path through two nodes with the same nonterminal. -/
def pumpingConstant : ℕ := g.maxBranch ^ (g.rules.card + 1)

theorem two_le_maxBranch : 2 ≤ g.maxBranch := le_max_left _ _

theorem pumpingConstant_pos : 0 < g.pumpingConstant :=
  Nat.pow_pos (Nat.zero_lt_of_lt g.two_le_maxBranch)

theorem length_output_le_maxBranch {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.output.length ≤ g.maxBranch :=
  (Finset.le_sup (f := fun r : ContextFreeRule T g.NT ↦ r.output.length) hr).trans
    (le_max_right _ _)

end ContextFreeGrammar

namespace RoseTree.Licensed

variable {T : Type*} {g : ContextFreeGrammar T} {t : RoseTree (Symbol T g.NT)}

theorem exists_getElem?_take
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
theorem exists_repeat
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

/-- A licensed tree of height `h` has at most `maxBranch ^ (h - 1)` terminals. -/
theorem length_yield_le (ht : t.Licensed g.Licenses) :
    t.yield.length ≤ g.maxBranch ^ (t.height - 1) := by
  refine (length_filterMap_le _ _).trans <| (length_leafList t).trans_le <|
    numLeaves_le_pow_height_sub_one <| ht.mono fun s ks h ↦ ?_
  cases s with
  | terminal => exact (show ks = [] from h) ▸ Nat.zero_le _
  | nonterminal A => exact g.length_output_le_maxBranch (r := ⟨A, ks⟩) h

/-- A licensed tree with at least `pumpingConstant` terminals is taller than the number of rules
plus one. -/
theorem card_rules_add_one_lt_height (ht : t.Licensed g.Licenses)
    (hlong : g.pumpingConstant ≤ t.yield.length) : g.rules.card + 1 < t.height := by
  have := (Nat.pow_le_pow_iff_right g.two_le_maxBranch).1
    (hlong.trans ht.length_yield_le)
  omega

/-- A licensed tree taller than the number of rules plus one has a subtree `outer`, of height at
most the number of rules plus two, with a proper subtree `inner` whose root symbol is the same:
of the last `rules.card + 1` nodes above the leaves on a longest path, two apply the same rule. -/
theorem exists_repeat_of_lt_height (ht : t.Licensed g.Licenses)
    (htall : g.rules.card + 1 < t.height) :
    ∃ (po pr : List ℕ) (outer inner : RoseTree (Symbol T g.NT)), pr ≠ [] ∧
      t[po]? = some outer ∧ outer[pr]? = some inner ∧ inner.value = outer.value ∧
      outer.height ≤ g.rules.card + 2 := by
  obtain ⟨p, hp, hpath⟩ := exists_getElem?_height_sub t (t.height - 2) (by omega)
  set off := t.height - 2 - g.rules.card
  obtain ⟨t₀, ht₀, ht₀h⟩ := hpath off (by omega)
  set q := p.drop off
  have hql : q.length = g.rules.card := by simp [q, hp]; omega
  have hpq : p = p.take off ++ q := (take_append_drop off p).symm
  obtain ⟨e, he, heh⟩ := hpath p.length hp.le
  rw [take_length, hpq, getElem?_append, ht₀, Option.bind_some] at he
  obtain ⟨i, j, hij, hjK, A, csᵢ, csⱼ, hi, hj⟩ :=
    (ht.of_getElem? ht₀).exists_repeat he (by omega) hql.ge
  have hqj : q.take j = q.take i ++ (q.take j).drop i := by
    conv_lhs => rw [← take_append_drop i (q.take j)]
    rw [take_take, min_eq_left hij.le]
  have hpo : t[p.take off ++ q.take i]? = some (node (.nonterminal A) csᵢ) := by
    rw [getElem?_append, ht₀, Option.bind_some, hi]
  refine ⟨_, (q.take j).drop i, _, node (.nonterminal A) csⱼ, fun h ↦ ?_, hpo, ?_, rfl, ?_⟩
  · have := congrArg length h
    simp [hql] at this
    omega
  · rwa [hqj, getElem?_append, hi, Option.bind_some] at hj
  · have := height_le_of_getElem? hi
    omega

/-- Grafting a tree in place of a proper subtree with the same root symbol, `n` times over, pumps
the terminals `v` and `y` around the subtree `n` times. -/
theorem exists_pump {outer inner : RoseTree (Symbol T g.NT)} (houter : outer.Licensed g.Licenses)
    {pr : List ℕ} (hpr : outer[pr]? = some inner) (hv : inner.value = outer.value) {v y : List T}
    (hvy : ∀ new, (outer.replaceAt pr new).yield = v ++ new.yield ++ y) (n : ℕ) :
    ∃ s : RoseTree (Symbol T g.NT), s.Licensed g.Licenses ∧ s.value = inner.value ∧
      s.yield = (replicate n v).flatten ++ inner.yield ++ (replicate n y).flatten := by
  induction n with
  | zero => exact ⟨inner, houter.of_getElem? hpr, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, hsv, hsy⟩ := ih
    refine ⟨outer.replaceAt pr s, houter.replaceAt hpr hs hsv, ?_, ?_⟩
    · rw [value_replaceAt hpr hsv, hv]
    · rw [hvy, hsy, replicate_succ, replicate_succ']
      simp

end RoseTree.Licensed

/-- **The pumping lemma for context-free languages.** -/
theorem Language.IsContextFree.hasCFLPumpingProperty {T : Type*} {L : Language T}
    (hcf : L.IsContextFree) : L.HasCFLPumpingProperty := by
  obtain ⟨g, rfl⟩ := hcf
  refine ⟨g.pumpingConstant, g.pumpingConstant_pos, fun w hw hlen ↦ ?_⟩
  -- a derivation tree of `w` with the fewest nodes
  obtain ⟨t₁, ⟨⟨ht₁, hr₁⟩, rfl⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun t ↦ t ∈ g.derivationTrees ∧ t.yield = w) numNodes
    (ContextFreeGrammar.mem_language_iff_exists_mem_derivationTrees.mp hw)
  obtain ⟨po, pr, outer, inner, hpr, hpo, hpri, hv, hh⟩ :=
    ht₁.exists_repeat_of_lt_height (ht₁.card_rules_add_one_lt_height hlen)
  have houter := ht₁.of_getElem? hpo
  obtain ⟨u, z, hyu, hyu'⟩ := yield_replaceAt hpo
  obtain ⟨v, y, hyv, hyv'⟩ := yield_replaceAt hpri
  refine ⟨u, v, inner.yield, y, z, ?_, ?_, ?_, fun k ↦ ?_⟩
  · rw [hyu, hyv]; simp only [append_assoc]
  · rw [← hyv]
    exact houter.length_yield_le.trans
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt g.two_le_maxBranch) (by omega))
  · -- replacing `outer` by `inner` would give a smaller tree with the same yield
    intro hvy
    obtain ⟨rfl, rfl⟩ := append_eq_nil_iff.1 hvy
    obtain ⟨i, rest, rfl⟩ := exists_cons_of_ne_nil hpr
    have hlt := numNodes_replaceAt_lt hpo (numNodes_lt_of_getElem?_cons hpri)
    exact hlt.not_ge <| hmin ⟨⟨ht₁.replaceAt hpo (houter.of_getElem? hpri) hv,
      by rw [value_replaceAt hpo hv, hr₁]⟩, by rw [hyu', hyu, hyv]; simp⟩ hlt.le
  · obtain ⟨s, hs, hsv, hsy⟩ := houter.exists_pump hpri hv hyv' k
    rw [ContextFreeGrammar.mem_language_iff, ← hr₁, ← value_replaceAt hpo (hsv.trans hv),
      show u ++ (replicate k v).flatten ++ inner.yield ++ (replicate k y).flatten ++ z =
        (t₁.replaceAt po s).yield by rw [hyu', hsy]; simp only [append_assoc]]
    exact (ht₁.replaceAt hpo hs (hsv.trans hv)).derives

/-- The pumping lemma in terms of letter counts: beyond some length, every word `w` of a
context-free language has an infix `s` no longer than that length and a nonempty sublist `t` of
`s` such that, for every `i`, some word of the language has the letters of `w` with `t` taken
`i` times instead of once. -/
theorem Language.IsContextFree.exists_pump_multiset {T : Type*} {L : Language T}
    (hcf : L.IsContextFree) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length → ∃ s t : List T, s <:+: w ∧ s.length ≤ p ∧
      t ≠ [] ∧ t <+ s ∧ ∀ i : ℕ, ∃ w' ∈ L, (w' : Multiset T) + t = w + i • (t : Multiset T) := by
  obtain ⟨p, hp, h⟩ := hcf.hasCFLPumpingProperty
  refine ⟨p, hp, fun w hw hlen ↦ ?_⟩
  obtain ⟨u, v, x, y, z, rfl, hvxy, hvy, hall⟩ := h w hw hlen
  have hrep (l : List T) (i : ℕ) :
      ((replicate i l).flatten : Multiset T) = i • (l : Multiset T) := by
    induction i with
    | zero => rfl
    | succ i ih => rw [replicate_succ, flatten_cons, ← Multiset.coe_add, ih, succ_nsmul']
  refine ⟨v ++ x ++ y, v ++ y, ⟨u, z, by simp⟩, hvxy, hvy,
    (sublist_append_left v x).append (.refl y), fun i ↦ ⟨_, hall i, ?_⟩⟩
  simp only [← Multiset.coe_add, hrep, nsmul_add]
  abel
