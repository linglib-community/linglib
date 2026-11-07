/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.TierStrictlyLocal
public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Linglib.Core.Computability.ShuffleIdeal
public import Mathlib.Computability.DFA
public import Mathlib.Tactic.DeriveFintype

/-!
# Lambert (2023): Relativized adjacency

Lambert characterizes the tier-based strictly local languages by two closure conditions on a
tier: the symbols off it are freely insertable and deletable, and suffixes cross over middles
with one projection. A refutation finds symbols that are not freely insertable and words over
them that violate the crossover, so [the constraint against `a … b … a` is not tier-based
strictly local](##Lambert2023.abaFree_not_isTierStrictlyLocal) though it is strictly piecewise.
On a canonical automaton the freely insertable symbols are those that loop on every state, in
Figure 3 [only `d`](##Lambert2023.fig3_syntacticClass_eq_one_iff). The figure's stringset [is
tier-based strictly local](##Lambert2023.fig3_isTierStrictlyLocal) but [not strictly
local](##Lambert2023.fig3_not_isStrictlyLocal), and [its salient symbols are its least
tier](##Lambert2023.fig3_least_tier).

## Implementation notes

Figure 3 draws the canonical automaton, which leaves out the nonaccepting sink; `fig3DFA`
restores it so that its transition function is total. The figure's stringset is shown tier-based
strictly local through the closure conditions rather than by a grammar, the route Lambert
describes for reading a tier off an automaton.

## References

* [lambert-2023]
-/

@[expose] public section

namespace Lambert2023

open Language
open scoped List

/-- The symbols of Lambert's examples. -/
inductive Sym
  | a | b | c | d
  deriving DecidableEq, Fintype

/-! ## A precedence constraint -/

/-- The words with no subsequence `a … b … a`: sequential but not necessarily adjacent
occurrences of `a`, `b` and `a` are banned. -/
def abaFree : Language Sym := (shuffleIdeal [.a, .b, .a])ᶜ

@[simp] theorem mem_abaFree {w : List Sym} : w ∈ abaFree ↔ ¬ [.a, .b, .a] <+ w := Iff.rfl

instance : DecidablePred (· ∈ abaFree) := fun _ ↦ decidable_of_iff _ mem_abaFree.symm

theorem abaFree_isStrictlyPiecewise : abaFree.IsStrictlyPiecewise 3 :=
  isStrictlyPiecewise_compl_shuffleIdeal le_rfl

/-- **A precedence constraint that is not tier-based strictly local** (p. 715). Since `b` is not
freely insertable it lies on every tier, so suffix substitution across a middle of `b`s carries
`a b⋯b b` and `b b⋯b a` to `a b⋯b a`. Lambert's middle has `k - 1` symbols; it has `k + 1` here
so that the argument covers every width. -/
theorem abaFree_not_isTierStrictlyLocal (k : ℕ) : ¬ abaFree.IsTierStrictlyLocal k := fun h ↦ by
  obtain ⟨T, hinv, hL⟩ := h.exists_tier
  have hb : T .b := by_contra fun hb ↦
    absurd (syntacticClass_eq_one_iff.1 (hinv .b hb) [.a] [.a]) (by decide)
  have hx : (List.replicate (k + 1) Sym.b).filter T = List.replicate (k + 1) .b := by simp [hb]
  have hmem (u v : List Sym) (huv : u.count .a + v.count .a ≤ 1) :
      u ++ List.replicate (k + 1) .b ++ v ∈ abaFree := fun hs ↦ by
    have := hs.count_le .a
    simp [List.count_replicate] at this
    omega
  exact mem_abaFree.1 (hL [.a] (List.replicate (k + 1) .b) [.b] [.b] (List.replicate (k + 1) .b)
    [.a] rfl (by rw [hx, List.length_replicate]; omega) (hmem _ _ (by decide))
    (hmem _ _ (by decide))) (by simp [List.replicate_succ])

/-! ## Salience on an automaton -/

/-- The states of Figure 3, with the nonaccepting sink that its canonical automaton leaves out. -/
inductive State
  | one | two | three | sink
  deriving DecidableEq, Fintype

/-- The automaton of Figure 3. From state 2, the start, `a` leads to state 1 and `b` to state 3,
`c` leads back to state 2, `d` loops on every state, and `b` after state 1 or `a` after state 3
falls into the sink. -/
def fig3DFA : DFA Sym State where
  step
    | .one, .a | .two, .a => .one
    | .two, .b | .three, .b => .three
    | .one, .c | .two, .c | .three, .c => .two
    | s, .d => s
    | _, _ => .sink
  start := .two
  accept := {s | s ≠ .sink}

/-- The stringset of Figure 3. -/
def fig3 : Language Sym := fig3DFA.accepts

theorem mem_fig3 {w : List Sym} : w ∈ fig3 ↔ fig3DFA.eval w ≠ .sink := Iff.rfl

instance : DecidablePred (· ∈ fig3) := fun _ ↦ decidable_of_iff _ mem_fig3.symm

-- Lambert's `∁T = {d}`: the symbols on which every state loops.
theorem fig3_step_eq_self_iff {x : Sym} : (∀ q, fig3DFA.step q x = q) ↔ x = .d := by
  cases x <;> decide

/-- **Only `d` is freely insertable and deletable** (§4.1): the syntactic class of a symbol is
the identity exactly when every state of Figure 3 loops on it. -/
theorem fig3_syntacticClass_eq_one_iff {x : Sym} : fig3.syntacticClass [x] = 1 ↔ x = .d := by
  refine ⟨fun h ↦ ?_, fun h ↦ syntacticClass_eq_one_iff.2 fun u v ↦ ?_⟩
  · have h := syntacticClass_eq_one_iff.1 h
    cases x
    · exact absurd (h [] [.b]) (by decide)
    · exact absurd (h [.a] []) (by decide)
    · exact absurd (h [.a] [.b]) (by decide)
    · rfl
  · simp only [mem_fig3, DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton,
      fig3_step_eq_self_iff.2 h]

private theorem evalFrom_sink (v : List Sym) : fig3DFA.evalFrom .sink v = .sink := by
  induction v with
  | nil => rfl
  | cons x v ih => cases x <;> exact ih

-- After a word whose projection to `{a, b, c}` ends in `t`, the automaton is where `t` leads
-- from state 2, unless it is in the sink.
private theorem evalFrom_eq_of_getLast? (q : State) {x : List Sym} {t : Sym}
    (ht : (x.filter (· ≠ .d)).getLast? = some t) :
    fig3DFA.evalFrom q x = .sink ∨ fig3DFA.evalFrom q x = fig3DFA.step .two t := by
  induction x using List.reverseRecOn generalizing t with
  | nil => simp at ht
  | append_singleton x y ih =>
    rw [DFA.evalFrom_append_singleton]
    by_cases hy : y = .d
    · subst hy
      rw [fig3_step_eq_self_iff.2 rfl]
      exact ih (by simpa [List.filter_append] using ht)
    · obtain rfl : y = t := by simpa [List.filter_append, hy] using ht
      have key : ∀ s y, y ≠ Sym.d →
          fig3DFA.step s y = .sink ∨ fig3DFA.step s y = fig3DFA.step .two y := by decide
      exact key _ _ hy

theorem fig3_preprojectiveSuffixSubstitutionClosed :
    fig3.PreprojectiveSuffixSubstitutionClosed (· ≠ .d) 2 := by
  intro u₁ x₁ v₁ u₂ x₂ v₂ hx hlen h₁ h₂
  obtain ⟨t, ht⟩ : ∃ t, (x₁.filter (· ≠ .d)).getLast? = some t := by
    rw [← Option.isSome_iff_exists, List.getLast?_isSome]
    exact List.ne_nil_of_length_pos (by omega)
  have hmem (u x v : List Sym) :
      u ++ x ++ v ∈ fig3 ↔ fig3DFA.evalFrom (fig3DFA.eval (u ++ x)) v ≠ .sink := by
    rw [mem_fig3, DFA.eval, fig3DFA.evalFrom_of_append _ (u ++ x) v]
  have hstate (u x v : List Sym) (hxt : (x.filter (· ≠ .d)).getLast? = some t)
      (h : u ++ x ++ v ∈ fig3) : fig3DFA.eval (u ++ x) = fig3DFA.step .two t := by
    have he : fig3DFA.eval (u ++ x) = fig3DFA.evalFrom (fig3DFA.eval u) x :=
      fig3DFA.evalFrom_of_append _ _ _
    rcases evalFrom_eq_of_getLast? (fig3DFA.eval u) hxt with hs | hs
    · exact absurd (by rw [he, hs, evalFrom_sink]) ((hmem u x v).1 h)
    · rw [he, hs]
  rw [hmem, hstate u₁ x₁ v₁ ht h₁, ← hstate u₂ x₂ v₂ (hx ▸ ht) h₂]
  exact (hmem u₂ x₂ v₂).1 h₂

/-- **Figure 3's stringset is tier-based strictly 2-local** (§4.1), by Lambert's
characterization: off the tier `{a, b, c}` only `d` remains, which is freely insertable, and
the state after a middle with a tier symbol depends only on its last one, so suffixes cross over
such middles. -/
theorem fig3_isTierStrictlyLocal : fig3.IsTierStrictlyLocal 2 :=
  (isTierStrictlyLocal_iff_exists_tier le_rfl).2
    ⟨(· ≠ .d), fun x hx ↦ fig3_syntacticClass_eq_one_iff.2 (by simpa using hx),
      fig3_preprojectiveSuffixSubstitutionClosed⟩

/-- **The salient symbols are the least tier** (§4.1). Figure 3's stringset is generated at
width 2 on the tier `{a, b, c}`, and every grammar that generates it, at any width, has `a`,
`b` and `c` on its tier. -/
theorem fig3_least_tier :
    (∃ G : TierStrictlyLocalGrammar Sym, G.language 2 = fig3 ∧ ∀ x, G.tier x ↔ x ≠ .d) ∧
      ∀ k (G : TierStrictlyLocalGrammar Sym), G.language k = fig3 → ∀ x ≠ .d, G.tier x := by
  refine ⟨?_, fun k G hG x hx ↦
    G.tier_of_syntacticClass_ne_one (hG ▸ fig3_syntacticClass_eq_one_iff.not.2 hx)⟩
  obtain ⟨G, hG, htier⟩ := fig3_isTierStrictlyLocal.exists_salient_tier
  exact ⟨G, hG, fun x ↦ (htier x).trans fig3_syntacticClass_eq_one_iff.not⟩

/-- **Figure 3's stringset is not strictly local** (Figure 4). A run of `d`s of any length
separates `a` from `b`, so suffix substitution carries `a d⋯d a` and `b d⋯d b` to `a d⋯d b`;
Lambert reads the same fact off a cycle of the powerset graph. -/
theorem fig3_not_isStrictlyLocal (k : ℕ) : ¬ fig3.IsStrictlyLocal k := fun h ↦ by
  have hd (q : State) (n : ℕ) : fig3DFA.evalFrom q (List.replicate n .d) = q := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ', DFA.evalFrom_append_singleton, ih, fig3_step_eq_self_iff.2 rfl]
  have hmem (x y : Sym) : [x] ++ List.replicate (k - 1) .d ++ [y] ∈ fig3 ↔
      fig3DFA.step (fig3DFA.step .two x) y ≠ .sink := by
    rw [mem_fig3, DFA.eval, DFA.evalFrom_append_singleton, DFA.evalFrom_of_append, hd]
    rfl
  exact (hmem .a .b).1 (h.suffixSubstitutionClosed [.a] [.a] [.b] [.b] _ (by simp)
    ((hmem _ _).2 (by decide)) ((hmem _ _).2 (by decide))) rfl

end Lambert2023
