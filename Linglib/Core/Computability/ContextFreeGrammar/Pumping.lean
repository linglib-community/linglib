/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Tree
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The pumping lemma for context-free languages

Every context-free language has the pumping property: beyond the pumping constant of a grammar,
every word splits as `u ++ v ++ x ++ y ++ z` with `v ++ x ++ y` short, `v ++ y` nonempty, and
every `u ++ vⁱ ++ x ++ yⁱ ++ z` in the language.

The proof is the textbook one through derivation trees. A word longer than
`maxBranch ^ (rules.card + 1)` has a licensed tree of height above `rules.card + 1`
(`RoseTree.Licensed.length_yield_le`); a longest path in a tree of least size passes two nodes
with the same nonterminal (`RoseTree.Licensed.exists_repeat`); replacing the lower by the upper
would shrink the tree unless it adds terminals, and grafting the lower into the upper repeatedly
pumps them (`RoseTree.Licensed.replaceAt`, `RoseTree.Licensed.derives`).

## Main definitions

* `Language.HasCFLPumpingProperty`: the pumping property of a language.
* `ContextFreeGrammar.maxBranch`, `ContextFreeGrammar.pumpingConstant`: the branching bound and
  the pumping constant of a grammar.

## Main results

* `RoseTree.Licensed.length_yield_le`: a licensed tree of height `h` has at most `maxBranch ^ h`
  terminals.
* `Language.IsContextFree.hasCFLPumpingProperty`: every context-free language has the pumping
  property.
-/

@[expose] public section

open RoseTree

/-- A language has the pumping property when, beyond some length, every word splits as
`u ++ v ++ x ++ y ++ z` with `v ++ x ++ y` no longer than that length, `v ++ y` nonempty, and every
`u ++ vⁱ ++ x ++ yⁱ ++ z` in the language. -/
def Language.HasCFLPumpingProperty {α : Type*} (L : Language α) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
    ∃ u v x y z : List α, w = u ++ v ++ x ++ y ++ z ∧ (v ++ x ++ y).length ≤ p ∧
      1 ≤ v.length + y.length ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈ L

namespace ContextFreeGrammar

variable {T : Type*} (g : ContextFreeGrammar T)

/-! ### The branching bound -/

/-- The branching bound of a grammar is the length of its longest right-hand side, and at least
`2`. -/
noncomputable def maxBranch : ℕ := max 2 (g.rules.sup fun r => r.output.length)

/-- The pumping constant is `maxBranch ^ (rules.card + 1)`, so that a licensed tree with more
terminals has a path through two nodes with the same nonterminal. -/
noncomputable def pumpingConstant : ℕ := g.maxBranch ^ (g.rules.card + 1)

theorem two_le_maxBranch : 2 ≤ g.maxBranch := le_max_left _ _

theorem pumpingConstant_pos : 0 < g.pumpingConstant :=
  Nat.pow_pos (by have := g.two_le_maxBranch; omega)

theorem length_output_le_maxBranch {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.output.length ≤ g.maxBranch :=
  le_trans (Finset.le_sup (f := fun r : ContextFreeRule T g.NT => r.output.length) hr)
    (le_max_right _ _)

variable {g}

/-- A licensed tree of height `h` has at most `maxBranch ^ (h - 1)` terminals. -/
theorem _root_.RoseTree.Licensed.length_yield_le {t : RoseTree (Symbol T g.NT)}
    (ht : t.Licensed g.Licenses) : t.yield.length ≤ g.maxBranch ^ (t.height - 1) := by
  induction ht using RoseTree.Licensed.grammar_induction with
  | terminal a => simp
  | nonterminal A cs hrule _ ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      set h := (RoseTree.node (.nonterminal A) (c :: cs)).height with hh
      have hpos : 1 < h :=
        Nat.lt_of_le_of_lt (RoseTree.height_pos c) (RoseTree.height_lt_of_mem (c := c) (by simp))
      have hb : 0 < g.maxBranch := by have := g.two_le_maxBranch; omega
      rw [RoseTree.yield_node_nonterminal, List.length_flatten, List.map_map]
      calc ((c :: cs).map (List.length ∘ RoseTree.yield)).sum
          ≤ ((c :: cs).map fun _ => g.maxBranch ^ (h - 2)).sum := by
            refine List.sum_le_sum fun d hd => ?_
            refine (ih d hd).trans (Nat.pow_le_pow_right hb ?_)
            have := RoseTree.height_lt_of_mem (t := RoseTree.node (.nonterminal A) (c :: cs)) hd
            omega
        _ = (c :: cs).length * g.maxBranch ^ (h - 2) := by
            rw [List.map_const', List.sum_const_nat]
        _ ≤ g.maxBranch * g.maxBranch ^ (h - 2) :=
            Nat.mul_le_mul_right _ (by simpa using g.length_output_le_maxBranch hrule)
        _ = g.maxBranch ^ (h - 1) := by rw [← Nat.pow_succ']; congr 1; omega


private theorem flatten_replicate_succ (l : List T) (n : ℕ) :
    (List.replicate (n + 1) l).flatten = (List.replicate n l).flatten ++ l := by
  rw [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem pumping_from_tall_tree {t : RoseTree (Symbol T g.NT)} (ht : t.Licensed g.Licenses)
    (hroot : t.value = .nonterminal g.initial) (hlong : g.pumpingConstant ≤ t.yield.length) :
    ∃ u v x y z : List T, t.yield = u ++ v ++ x ++ y ++ z ∧
      (v ++ x ++ y).length ≤ g.pumpingConstant ∧ 1 ≤ v.length + y.length ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈
        g.language := by
  classical
  have hb : 1 < g.maxBranch := g.two_le_maxBranch
  -- a licensed tree of least size with the same yield and root
  obtain ⟨t₁, ht₁, hy₁, hr₁, hmin⟩ := ht.exists_min_numNodes
  -- it is taller than the number of rules
  have htall : g.rules.card + 1 < t₁.height := by
    by_contra hle
    have h1 := ht₁.length_yield_le
    have h2 : g.maxBranch ^ (t₁.height - 1) ≤ g.maxBranch ^ g.rules.card :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : g.maxBranch ^ g.rules.card < g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_lt_pow_right hb (by omega)
    rw [hy₁] at h1
    unfold pumpingConstant at hlong
    omega
  -- a longest path, and the window of its last `g.rules.card + 1` nodes
  obtain ⟨p, hp, hpath⟩ := exists_subtreeAt_height_sub t₁ (t₁.height - 2) (by omega)
  set off := t₁.height - 2 - g.rules.card with hoff
  obtain ⟨t₀, ht₀, hh₀⟩ := hpath off (by omega)
  set q := p.drop off with hq
  have hql : q.length = g.rules.card := by simp [q, hp]; omega
  have hpq : p = p.take off ++ q := (List.take_append_drop off p).symm
  obtain ⟨e, he, heh⟩ := hpath p.length hp.le
  rw [List.take_length, hpq, subtreeAt_append, ht₀, Option.bind_some] at he
  obtain ⟨i, j, hij, hjK, A, csᵢ, csⱼ, hi, hj⟩ :=
    (ht₁.of_subtreeAt ht₀).exists_repeat he (by omega) hql.ge
  -- the outer and inner repeats, and their addresses
  set outer := node (Symbol.nonterminal A) csᵢ with houter
  set inner := node (Symbol.nonterminal A) csⱼ with hinner
  set po := p.take off ++ q.take i with hpo
  have hpo_sub : subtreeAt t₁ po = some outer := by
    rw [hpo, subtreeAt_append, ht₀, Option.bind_some, hi]
  set pr := (q.take j).drop i with hpr
  have hqj : q.take j = q.take i ++ pr := by
    conv_lhs => rw [← List.take_append_drop i (q.take j)]
    rw [List.take_take, min_eq_left hij.le]
  have hpr_sub : subtreeAt outer pr = some inner := by
    rw [hqj, subtreeAt_append, hi, Option.bind_some] at hj; exact hj
  have hpr_ne : pr ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [pr, hql] at this
    omega
  have houter_h : outer.height ≤ g.rules.card + 2 := by
    obtain ⟨s, hs, hsh⟩ := hpath (off + i) (by omega)
    rw [List.take_add, ← hq, ← hpo, hpo_sub, Option.some.injEq] at hs
    rw [hs, hsh]; omega
  have houter_v : outer.Licensed g.Licenses := ht₁.of_subtreeAt hpo_sub
  have hinner_v : inner.Licensed g.Licenses := houter_v.of_subtreeAt hpr_sub
  -- yield decompositions
  obtain ⟨u, z, hyu, hyu'⟩ := yield_replaceAt hpo_sub
  obtain ⟨v, y, hyv, hyv'⟩ := yield_replaceAt hpr_sub
  refine ⟨u, v, inner.yield, y, z, ?_, ?_, ?_, fun k => ?_⟩
  · rw [← hy₁, hyu, hyv]; simp only [List.append_assoc]
  · rw [← hyv]
    exact houter_v.length_yield_le.trans (Nat.pow_le_pow_right (by omega) (by omega))
  · -- `v ++ y` is nonempty, by minimality
    by_contra hvy
    have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨i', rest, hpr'⟩ := List.exists_cons_of_ne_nil hpr_ne
    have hlt : (t₁.replaceAt po inner).numNodes < t₁.numNodes :=
      numNodes_replaceAt_lt hpo_sub (numNodes_lt_of_subtreeAt_cons (hpr' ▸ hpr_sub))
    have := hmin _ (ht₁.replaceAt hpo_sub hinner_v rfl)
      (by rw [hyu' inner, ← hy₁, hyu, hyv, hv, hy]; simp)
      (by rw [value_replaceAt (new := inner) hpo_sub rfl, hr₁])
    omega
  · -- pumping: graft the inner tree into the outer one `k` times, then into the tree
    let pump : ℕ → RoseTree (Symbol T g.NT) := fun n =>
      Nat.rec inner (fun _ prev => outer.replaceAt pr prev) n
    have hpump : ∀ n, (pump n).yield =
          (List.replicate n v).flatten ++ inner.yield ++ (List.replicate n y).flatten ∧
        (pump n).value = inner.value ∧ (pump n).Licensed g.Licenses := fun n => by
      induction n with
      | zero => exact ⟨by show inner.yield = _; simp, rfl, hinner_v⟩
      | succ n ih =>
        refine ⟨?_, ?_, houter_v.replaceAt hpr_sub ih.2.2 ih.2.1⟩
        · show (outer.replaceAt pr (pump n)).yield = _
          rw [hyv' (pump n), ih.1, List.replicate_succ, List.flatten_cons, flatten_replicate_succ]
          simp only [List.append_assoc]
        · exact (value_replaceAt hpr_sub ih.2.1).trans rfl
    have hfinal := ht₁.replaceAt hpo_sub (hpump k).2.2 (hpump k).2.1
    rw [mem_language_iff, ← hroot, ← hr₁, ← value_replaceAt hpo_sub (hpump k).2.1,
      show u ++ (List.replicate k v).flatten ++ inner.yield ++ (List.replicate k y).flatten ++ z =
        (t₁.replaceAt po (pump k)).yield by rw [hyu' (pump k), (hpump k).1]; simp]
    exact hfinal.derives

end ContextFreeGrammar

/-- **The pumping lemma for context-free languages.** -/
theorem Language.IsContextFree.hasCFLPumpingProperty {T : Type*} {L : Language T}
    (hcf : L.IsContextFree) : L.HasCFLPumpingProperty := by
  obtain ⟨g, rfl⟩ := hcf
  refine ⟨g.pumpingConstant, g.pumpingConstant_pos, fun w hw hlen => ?_⟩
  obtain ⟨t, hvalid, hyield, hroot⟩ := g.exists_licensed_tree hw
  obtain ⟨u, v, x, y, z, hdecomp, hvxy, hvy, hpump⟩ :=
    ContextFreeGrammar.pumping_from_tall_tree hvalid hroot (hyield ▸ hlen)
  exact ⟨u, v, x, y, z, hyield ▸ hdecomp, hvxy, hvy, hpump⟩
