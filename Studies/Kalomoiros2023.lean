module

public import Studies.Schlenker2009
public import Mathlib.Tactic.IntervalCases

/-!
# Kalomoiros (2023): Presupposition and Its (A-)Symmetries

Limited Symmetry is a theory of presupposition projection that checks Transparency at every point
of the parse after a trigger. At a parsing point a sentence is stably true (false) at a world when
every good final of the string up to that point makes it true (false) there. The constraint
requires, at every trigger, every parsing point after it and every assertion, that the worlds of
the context where the sentence is stably true (false) stay so when the trigger is replaced by its
assertion: the presupposition is stably transparent for the good finals at each parsing point
(`Presupposition.StablyTransparent`). This file covers the dissertation's first system, over the
propositional fragment of Schlenker's language.

The good finals at the first parsing point after a trigger are all of Schlenker's incremental ones,
and at the last only the sentence itself, so Limited Symmetry lies between Schlenker's
incremental and symmetric Transparency (`LimitedSymmetry.of_transparency`,
`LimitedSymmetry.transparency`). The constraint is stated on the occurrences of a sentence's
triggers (`Presupposition.Occurrence`), so it applies as it stands wherever a sentence type supplies
its occurrences and their parsing points.

## Main statements

* `limitedSymmetry_and_left`, `limitedSymmetry_and_right`, `limitedSymmetry_or_left`: conjunction
  is asymmetric, a trigger in the first conjunct needing the context to entail its presupposition
  and one in the second only that the first conjunct does, while a first disjunct is filtered by
  the second.
* `limitedSymmetry_not`, `limitedSymmetry_if_not_left_iff_or`: a negated sentence respects the
  constraint iff the sentence does, but a negation inside a coordination changes its polarity, so
  that a conditional with a negated antecedent behaves like a disjunction.
* `limitedSymmetryAt_iff`, `limitedSymmetryAt_iff_funs`: the constraint is checked world by world,
  on the truth functions the good finals realize there, which makes each of the dissertation's
  facts a computation.
* `LimitedSymmetry.of_transparency`, `LimitedSymmetry.transparency`: incremental Transparency
  implies Limited Symmetry, which implies symmetric Transparency.

## Implementation notes

* A trigger `trigger p a` presupposes `p` and asserts `a`. The dissertation writes `p'p` with the
  prime on the presupposition, the reverse of Schlenker's convention.
* The parsing points after a trigger are represented by `SyntacticEnvironment.AgreeUpTo`, which
  counts the connective after a first argument and the second argument as one item each and
  ignores closing brackets. Points inside the second argument add no condition, since the
  constraint is checked world by world and the argument's value at a world is either still open
  or already fixed.
* A context is a set of worlds, and the assertions the constraint quantifies over are
  propositions.

## TODO

* Two conditions printed in the dissertation differ from what the constraint gives, for a
  conditional whose antecedent conjoins a negated trigger
  (`not_limitedSymmetry_if_not_and_of_printed`) and for the second trigger of a conjunction with a
  negated first conjunct
  (`not_limitedSymmetryAt_not_and_second_of_printed`).
* Facts 3.4.7 and 3.4.9, stated for arbitrary sentences, are not formalized, nor is the postposed
  conditional of Fact 3.4.6, which is outside the language.

## References

* [kalomoiros-2023]
* [schlenker-2009]
-/

@[expose] public section

namespace Kalomoiros2023

open Presupposition SyntacticEnvironment

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### The constraint -/

/-- The constraint of Definition 3.4.4 at one trigger, with presupposition `p` at the gap of `K`. At
every parsing point after the trigger and for every assertion `D`, the worlds where the sentence is
stably true (false) are worlds where it is stably true (false) with the presupposition deleted:
the presupposition is stably transparent at every parsing point. -/
def LimitedSymmetryAt (C : Set W) (K : SyntacticEnvironment Atom) (p : Atom) : Prop :=
  ∀ n : ℕ∞, StablyTransparent C (K.continuations I n) (I p)

/-- A sentence satisfies Limited Symmetry in `C` when the constraint holds at every trigger
(Definition 3.4.4). -/
def LimitedSymmetry {α : Type*} [SemilatticeInf α] (C : Set W) (os : List (Occurrence W α)) :
    Prop :=
  ∀ o ∈ os, ∀ n, o.StablyTransparent n C

theorem limitedSymmetry_occurrences_iff {C : Set W} {F : Formula Atom} :
    LimitedSymmetry C (Formula.occurrences I F) ↔
      ∀ t ∈ F.triggers, LimitedSymmetryAt I C t.1 t.2.1 :=
  Formula.forall_mem_occurrences

/-- The parsing points after a trigger are those up to the last item after the gap, as Definition
3.4.4 counts them; from there on only the sentence itself is consulted. -/
theorem limitedSymmetryAt_iff_forall_le {C : Set W} {K : SyntacticEnvironment Atom} {p : Atom} :
    LimitedSymmetryAt I C K p ↔
      ∀ n ≤ K.rightItems, StablyTransparent C (K.continuations I n) (I p) := by
  refine ⟨fun h n _ ↦ h n, fun h n ↦ ?_⟩
  have hlast := h _ le_rfl
  rw [continuations_eq_top_of_le I le_rfl] at hlast
  induction n using ENat.recTopCoe with
  | top => exact hlast
  | coe n =>
    rcases le_or_gt n K.rightItems with hn | hn
    · exact h n hn
    · rwa [continuations_eq_top_of_le I hn.le]

/-- The constraint is checked world by world. At a world where the presupposition fails, whenever
every good final at a parsing point makes the sentence true (false) with a false gap, every good
final makes it true (false) with a true gap. -/
theorem limitedSymmetryAt_iff (C : Set W) (K : SyntacticEnvironment Atom) (p : Atom) :
    LimitedSymmetryAt I C K p ↔ ∀ w ∈ C, w ∉ I p → ∀ n ≤ K.rightItems,
      ((∀ K', AgreeUpTo n K K' → w ∈ K'.truth I ∅) →
          ∀ K', AgreeUpTo n K K' → w ∈ K'.truth I Set.univ) ∧
        ((∀ K', AgreeUpTo n K K' → w ∉ K'.truth I ∅) →
          ∀ K', AgreeUpTo n K K' → w ∉ K'.truth I Set.univ) := by
  have tf (n : ℕ) : ∀ f ∈ K.continuations I n, IsTruthFunctional f :=
    fun _ hf ↦ isTruthFunctional_of_mem_continuations I hf
  rw [limitedSymmetryAt_iff_forall_le]
  refine ⟨fun h w hw hp n hn ↦ ?_, fun h n hn ↦ (stablyTransparent_iff (tf n)).2 fun w hw hp ↦ ?_⟩
  · simpa only [continuations_natCast, Set.forall_mem_image, Set.mem_ofPred_eq] using
      (stablyTransparent_iff (tf n)).1 (h n hn) w hw hp
  · simpa only [continuations_natCast, Set.forall_mem_image, Set.mem_ofPred_eq] using h w hw hp n hn

/-! ### Between incremental and symmetric Transparency -/

section Occurrences

variable {α : Type*} [SemilatticeInf α] {C : Set W} {os : List (Occurrence W α)}

/-- Incremental Transparency implies Limited Symmetry, since every parsing point consults fewer
continuations than the first. -/
theorem LimitedSymmetry.of_transparency (h : Schlenker2009.Transparency .incremental C os) :
    LimitedSymmetry C os :=
  fun o ho _ ↦ ((h o ho).mono bot_le).stablyTransparent

/-- Limited Symmetry implies symmetric Transparency, since at the last parsing point the only
continuation is the sentence's own. -/
theorem LimitedSymmetry.transparency (h : LimitedSymmetry C os) :
    Schlenker2009.Transparency .symmetric C os :=
  fun o ho ↦ Occurrence.stablyTransparent_top_iff.1 (h o ho ⊤)

end Occurrences

/-! ### The truth functions of the good finals -/

open Classical

/-- A connective's truth function on booleans. -/
def evalB : Connective → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .cond, a, b => !a || b
  | .disj, a, b => a || b

theorem decide_eval (c : Connective) (a b : Prop) :
    decide (c.eval a b) = evalB c (decide a) (decide b) := by
  cases c <;> by_cases ha : a <;> by_cases hb : b <;> simp [Connective.eval, evalB, ha, hb]

/-- The truth value at `w` of a formula. -/
noncomputable def val (w : W) (F : Formula Atom) : Bool := decide (w ∈ F.truth I)

/-- The connectives that may follow a first argument when no item after the gap is fixed. -/
def compat : Connective → List Connective
  | .cond => [.cond]
  | _ => [.conj, .disj]

theorem mem_compat {c c' : Connective} : c' ∈ compat c ↔ (c = .cond ↔ c' = .cond) := by
  cases c <;> cases c' <;> decide

/-- The truth functions at `w` of the good finals of a step up to parsing point `n`, as functions of
the gap's truth value. -/
noncomputable def stepFuns (w : W) (n : ℕ) : SyntacticEnvironment.Step Atom → List (Bool → Bool)
  | .not => [not]
  | .right c F => [evalB c (val I w F)]
  | .left c G =>
    if n = 0 then (compat c).flatMap fun c' ↦ [(evalB c' · true), (evalB c' · false)]
    else if n < c.rightItems then [(evalB c · true), (evalB c · false)]
    else [(evalB c · (val I w G))]

/-- The truth functions at `w` of the good finals of an environment up to parsing point `n`. -/
noncomputable def funs (w : W) : ℕ → SyntacticEnvironment Atom → List (Bool → Bool)
  | _, [] => [id]
  | n, s :: K => (stepFuns I w n s).flatMap fun f ↦ (funs w (n - s.rightItems) K).map (· ∘ f)

/-- A formula can be true or false at any world. -/
theorem forall_formula_iff [Nonempty Atom] (w : W) (Q : Prop → Prop) :
    (∀ G : Formula Atom, Q (w ∈ G.truth I)) ↔ Q True ∧ Q False := by
  let a := Classical.arbitrary Atom
  let t : Formula Atom := .bin .cond (.atom a) (.atom a)
  have ht : (w ∈ t.truth I) = True := eq_true fun h ↦ h
  have hf : (w ∈ (Formula.not t).truth I) = False := eq_false fun h ↦ h fun h ↦ h
  refine ⟨fun h ↦ ⟨ht ▸ h t, hf ▸ h (.not t)⟩, fun ⟨h₁, h₀⟩ G ↦ ?_⟩
  by_cases hG : w ∈ G.truth I
  · rwa [eq_true hG]
  · rwa [eq_false hG]

theorem forall_stepAgree_iff [Nonempty Atom] (w : W) (n : ℕ) (s : SyntacticEnvironment.Step Atom)
    (X : Set W) (R : Bool → Prop) :
    (∀ s', s.AgreeUpTo n s' → R (decide (w ∈ s'.truth I X))) ↔
      ∀ f ∈ stepFuns I w n s, R (f (decide (w ∈ X))) := by
  cases s with
  | not => simp [SyntacticEnvironment.Step.AgreeUpTo, stepFuns, SyntacticEnvironment.Step.truth]
  | right c F =>
    simp [SyntacticEnvironment.Step.AgreeUpTo, stepFuns, SyntacticEnvironment.Step.truth,
      decide_eval, val]
  | left c G =>
    have key (c' : Connective) : (∀ G' : Formula Atom,
        R (decide (w ∈ (SyntacticEnvironment.Step.left c' G').truth I X))) ↔
          R (evalB c' (decide (w ∈ X)) true) ∧
          R (evalB c' (decide (w ∈ X)) false) := by
      simp only [SyntacticEnvironment.Step.truth, Set.mem_ofPred_eq, decide_eval]
      exact forall_formula_iff I w (fun b ↦ R (evalB c' (decide (w ∈ X)) (decide b))) |>.trans
        (by simp)
    simp only [SyntacticEnvironment.Step.AgreeUpTo, stepFuns]
    split_ifs
    · simp only [forall_exists_index, and_imp, List.forall_mem_flatMap, List.forall_mem_cons,
        List.mem_nil_iff, false_imp_iff, implies_true, and_true, ← mem_compat]
      exact ⟨fun h c' hc ↦ (key c').1 fun G' ↦ h _ c' G' rfl hc,
        fun h _ c' G' he hc ↦ he ▸ (key c').2 (h c' hc) G'⟩
    · simp only [forall_exists_index, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff,
        implies_true, and_true]
      exact ⟨fun h ↦ (key c).1 fun G' ↦ h _ G' rfl, fun h _ G' he ↦ he ▸ (key c).2 h G'⟩
    · simp [SyntacticEnvironment.Step.truth, decide_eval, val]

/-- The good finals at a parsing point realize, at each world, the truth functions `funs`. -/
theorem forall_agreeUpTo_iff [Nonempty Atom] (w : W) (n : ℕ) (K : SyntacticEnvironment Atom)
    (X : Set W) (R : Bool → Prop) :
    (∀ K', AgreeUpTo n K K' → R (decide (w ∈ K'.truth I X))) ↔
      ∀ f ∈ funs I w n K, R (f (decide (w ∈ X))) := by
  induction K generalizing n X R with
  | nil => simp [AgreeUpTo, funs, SyntacticEnvironment.truth]
  | cons s K ih =>
    have lhs : (∀ K', AgreeUpTo n (s :: K) K' → R (decide (w ∈ K'.truth I X))) ↔
        ∀ s', s.AgreeUpTo n s' → ∀ K'', AgreeUpTo (n - s.rightItems) K K'' →
          R (decide (w ∈ K''.truth I (s'.truth I X))) :=
      ⟨fun h s' hs K'' hK ↦ h (s' :: K'') ⟨s', K'', rfl, hs, hK⟩,
        fun h K' ⟨s', K'', he, hs, hK⟩ ↦ by subst he; exact h s' hs K'' hK⟩
    rw [lhs]
    simp only [funs, List.forall_mem_flatMap, List.forall_mem_map, Function.comp_apply]
    exact (forall_congr' fun s' ↦ imp_congr_right fun _ ↦ ih _ _ _).trans
      (forall_stepAgree_iff I w n s X fun b ↦ ∀ g ∈ funs I w (n - s.rightItems) K, R (g b))

/-- Definition 3.4.4 world by world, as a condition on the truth functions of the good finals. -/
theorem limitedSymmetryAt_iff_funs (C : Set W) (K : SyntacticEnvironment Atom) (p : Atom) :
    LimitedSymmetryAt I C K p ↔ ∀ w ∈ C, w ∉ I p → ∀ n ≤ K.rightItems,
      ((∀ f ∈ funs I w n K, f false = true) → ∀ f ∈ funs I w n K, f true = true) ∧
        ((∀ f ∈ funs I w n K, f false = false) → ∀ f ∈ funs I w n K, f true = false) := by
  have : Nonempty Atom := ⟨p⟩
  rw [limitedSymmetryAt_iff]
  refine forall₂_congr fun w _ ↦ imp_congr_right fun _ ↦ forall₂_congr fun n _ ↦ ?_
  have e₁ (X : Set W) := forall_agreeUpTo_iff I w n K X (· = true)
  have e₀ (X : Set W) := forall_agreeUpTo_iff I w n K X (· = false)
  simp only [decide_eq_true_iff, decide_eq_false_iff_not] at e₁ e₀
  simp only [e₁, e₀]
  simp

/-! ### What the constraint requires -/

variable {C : Set W} {p a q b r : Atom}

theorem limitedSymmetry_of_triggers {F : Formula Atom} {K : SyntacticEnvironment Atom}
    {p a : Atom} (h : F.triggers = [(K, p, a)]) :
    LimitedSymmetry C (Formula.occurrences I F) ↔ LimitedSymmetryAt I C K p := by
  simp [limitedSymmetry_occurrences_iff, h]

/-- A trigger standing alone requires the context to entail its presupposition. -/
theorem limitedSymmetry_trigger :
    LimitedSymmetry C (Formula.occurrences I (.trigger p a)) ↔ C ⊆ I p := by
  rw [limitedSymmetry_of_triggers I (K := []) (a := a) rfl, limitedSymmetryAt_iff]
  simp [AgreeUpTo, SyntacticEnvironment.truth, Set.subset_def]

/-- `(p'p and q)` requires the context to entail `p'` (Fact 3.4.1, p. 124). -/
theorem limitedSymmetry_and_left :
    LimitedSymmetry C (Formula.occurrences I (.bin .conj (.trigger p a) (.atom q))) ↔ C ⊆ I p := by
  rw [limitedSymmetry_of_triggers I (K := [.left .conj (.atom q)]) (a := a) rfl,
    limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
  simp [funs, stepFuns, evalB, Connective.rightItems] at this

/-- Evaluate the constraint at every parsing point of a concrete environment. -/
local macro "ls_points" : tactic =>
  `(tactic| (intro n hn
             simp only [rightItems_cons, rightItems_nil, Step.rightItems, Connective.rightItems]
               at hn
             interval_cases n <;>
               simp_all [funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
                 Connective.rightItems, compat, Connective.eval]))

/-- Evaluate the constraint at one parsing point of a concrete environment. -/
local macro "ls_at " h:term : tactic =>
  `(tactic| (simp [funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
               Connective.rightItems, compat, Connective.eval, *] at $h:term))

/-- `(q and p'p)` requires the context to entail `q → p'` (Fact 3.4.2, p. 126). -/
theorem limitedSymmetry_and_right :
    LimitedSymmetry C (Formula.occurrences I (.bin .conj (.atom q) (.trigger p a))) ↔
      C ⊆ {w | w ∈ I q → w ∈ I p} := by
  rw [limitedSymmetry_of_triggers I (K := [.right .conj (.atom q)]) (a := a) rfl,
    limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 0 le_rfl
    ls_at this
  · have hq : w ∉ I q := fun hq ↦ hp (h hw hq)
    ls_points

/-- `(p'p or q)` requires the context to entail `¬q → p'` (Fact 3.4.3, p. 127). -/
theorem limitedSymmetry_or_left :
    LimitedSymmetry C (Formula.occurrences I (.bin .disj (.trigger p a) (.atom q))) ↔
      C ⊆ {w | w ∉ I q → w ∈ I p} := by
  rw [limitedSymmetry_of_triggers I (K := [.left .disj (.atom q)]) (a := a) rfl,
    limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 2 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · have hq : w ∈ I q := by_contra fun hq ↦ hp (h hw hq)
    ls_points

/-- `(if p'p. q)` requires the context to entail `p'` (Fact 3.4.4, p. 128). -/
theorem limitedSymmetry_if_left :
    LimitedSymmetry C (Formula.occurrences I (.bin .cond (.trigger p a) (.atom q))) ↔ C ⊆ I p := by
  rw [limitedSymmetry_of_triggers I (K := [.left .cond (.atom q)]) (a := a) rfl,
    limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 0 (Nat.zero_le _)
  ls_at this

/-- `(if q. p'p)` requires the context to entail `q → p'` (Fact 3.4.5, p. 129). -/
theorem limitedSymmetry_if_right :
    LimitedSymmetry C (Formula.occurrences I (.bin .cond (.atom q) (.trigger p a))) ↔
      C ⊆ {w | w ∈ I q → w ∈ I p} := by
  rw [limitedSymmetry_of_triggers I (K := [.right .cond (.atom q)]) (a := a) rfl,
    limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 0 le_rfl
    ls_at this
  · have hq : w ∉ I q := fun hq ↦ hp (h hw hq)
    ls_points

/-- `(if (not p'p). q)` requires the context to entail `¬q → p'`, as `(p'p or q)` does (the first
half of Fact 3.4.10, p. 136). -/
theorem limitedSymmetry_if_not_left :
    LimitedSymmetry C (Formula.occurrences I (.bin .cond (.not (.trigger p a)) (.atom q))) ↔
      C ⊆ {w | w ∉ I q → w ∈ I p} := by
  rw [limitedSymmetry_of_triggers I (K := [.not, .left .cond (.atom q)]) (a := a) rfl,
    limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · have hq : w ∈ I q := by_contra fun hq ↦ hp (h hw hq)
    ls_points

/-- `(if (not p'p). q)` respects the constraint iff `(p'p or q)` does (Fact 3.4.10, p. 136). -/
theorem limitedSymmetry_if_not_left_iff_or :
    LimitedSymmetry C (Formula.occurrences I (.bin .cond (.not (.trigger p a)) (.atom q))) ↔
      LimitedSymmetry C (Formula.occurrences I (.bin .disj (.trigger p a) (.atom q))) := by
  rw [limitedSymmetry_if_not_left, limitedSymmetry_or_left]

/-- `(if ((not p'p) and q). r)` requires the context to entail `(q ∧ ¬r) → p'`. Fact 3.4.8 (p. 134)
prints `(q ∧ r) → p'` and omits the derivation (`not_limitedSymmetry_if_not_and_of_printed`). -/
theorem limitedSymmetry_if_not_and :
    LimitedSymmetry C (Formula.occurrences I
        (.bin .cond (.bin .conj (.not (.trigger p a)) (.atom q)) (.atom r))) ↔
      C ⊆ {w | w ∈ I q → w ∉ I r → w ∈ I p} := by
  rw [limitedSymmetry_of_triggers I (K := [.not, .left .conj (.atom q), .left .cond (.atom r)])
    (a := a) rfl, limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq hr ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 3 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · by_cases hq : w ∈ I q
    · have hr : w ∈ I r := by_contra fun hr ↦ hp (h hw hq hr)
      ls_points
    · ls_points

/-- The condition printed in Fact 3.4.8 is not the constraint's, since a context where `q` holds and
`r` and `p'` fail entails `(q ∧ r) → p'` but violates the constraint. -/
theorem not_limitedSymmetry_if_not_and_of_printed {w : W} (hq : w ∈ I q) (hr : w ∉ I r)
    (hp : w ∉ I p) :
    {w} ⊆ {w | w ∈ I q → w ∈ I r → w ∈ I p} ∧
      ¬ LimitedSymmetry {w} (Formula.occurrences I
        (.bin .cond (.bin .conj (.not (.trigger p a)) (.atom q)) (.atom r))) := by
  rw [limitedSymmetry_if_not_and]
  refine ⟨fun v hv ↦ ?_, fun h ↦ hp (h rfl hq hr)⟩
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact fun _ hr' ↦ absurd hr' hr

/-- In `(p'p and q'q)` the first trigger requires the context to entail `p'` (Fact 3.4.11, p.
137). -/
theorem limitedSymmetryAt_and_first :
    LimitedSymmetryAt I C [.left .conj (.trigger q b)] p ↔ C ⊆ I p := by
  rw [limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
  ls_at this

/-- In `((not p'p) and q'q)` the first trigger requires the context to entail `q'q → p'` (Fact
3.4.12, p. 137). -/
theorem limitedSymmetryAt_not_and_first :
    LimitedSymmetryAt I C [.not, .left .conj (.trigger q b)] p ↔
      C ⊆ {w | w ∈ I q → w ∈ I b → w ∈ I p} := by
  rw [limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq hb ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 2 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · by_cases hq : w ∈ I q
    · have hb : w ∉ I b := fun hb ↦ hp (h hw hq hb)
      ls_points
    · ls_points

/-- In `((not p'p) and q'q)` the second trigger requires the context to entail `(not p'p) → q'`,
filtering by the first conjunct. Fact 3.4.12 (p. 137) prints `p'p → q'`. -/
theorem limitedSymmetryAt_not_and_second :
    LimitedSymmetryAt I C [.right .conj (.not (.trigger p a))] q ↔
      C ⊆ {w | w ∉ I p ∩ I a → w ∈ I q} := by
  rw [limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hpa ↦ by_contra fun hq ↦ ?_, fun h w hw hq ↦ ?_⟩
  · have := h w hw hq 0 le_rfl
    ls_at this
  · have hpa : w ∈ I p ∩ I a := by_contra fun hpa ↦ hq (h hw hpa)
    obtain ⟨hp, ha⟩ := hpa
    ls_points

/-- In `(p'p or q'q)` the first trigger requires the context to entail `p' or q'q` (Fact 3.4.13, p.
138). -/
theorem limitedSymmetryAt_or_first :
    LimitedSymmetryAt I C [.left .disj (.trigger q b)] p ↔ C ⊆ {w | w ∈ I p ∨ w ∈ I q ∩ I b} := by
  rw [limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hn ↦ ?_, fun h w hw hp ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, not_or, Set.mem_inter_iff, not_and] at hn
    obtain ⟨hp, hqb⟩ := hn
    have := h w hw hp 2 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    by_cases hq : w ∈ I q
    · have hb := hqb hq; ls_at this
    · ls_at this
  · obtain ⟨hq, hb⟩ := (h hw).resolve_left hp
    ls_points

/-- In `(p'p or q'q)` the second trigger requires the context to entail `q' or p'p` (Fact 3.4.13, p.
138). -/
theorem limitedSymmetryAt_or_second :
    LimitedSymmetryAt I C [.right .disj (.trigger p a)] q ↔ C ⊆ {w | w ∈ I q ∨ w ∈ I p ∩ I a} := by
  rw [limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hn ↦ ?_, fun h w hw hq ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, not_or, Set.mem_inter_iff, not_and] at hn
    obtain ⟨hq, hpa⟩ := hn
    have := h w hw hq 0 le_rfl
    by_cases hp : w ∈ I p
    · have ha := hpa hp; ls_at this
    · ls_at this
  · obtain ⟨hp, ha⟩ := (h hw).resolve_left hq
    ls_points

/-- In `((not p'p) or q'q)` the first trigger requires the context to entail `p'` (Fact 3.4.14, p.
138). -/
theorem limitedSymmetryAt_not_or_first :
    LimitedSymmetryAt I C [.not, .left .disj (.trigger q b)] p ↔ C ⊆ I p := by
  rw [limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
  ls_at this

/-- `((p'p and q) or r)` requires the context to entail `q → (p' ∨ r)`, the second conjunct
filtering symmetrically, before the highest connective (Fact 3.4.15, p. 138). -/
theorem limitedSymmetry_and_or :
    LimitedSymmetry C
        (Formula.occurrences I (.bin .disj (.bin .conj (.trigger p a) (.atom q)) (.atom r))) ↔
      C ⊆ {w | w ∈ I q → w ∈ I p ∨ w ∈ I r} := by
  rw [limitedSymmetry_of_triggers I (K := [.left .conj (.atom q), .left .disj (.atom r)])
    (a := a) rfl, limitedSymmetryAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hn ↦ ?_, fun h w hw hp ↦ ?_⟩
  · simp only [not_or] at hn
    obtain ⟨hp, hr⟩ := hn
    have := h w hw hp 4 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · by_cases hq : w ∈ I q
    · have hr : w ∈ I r := ((h hw) hq).resolve_left hp
      ls_points
    · ls_points

/-- The condition printed in Fact 3.4.12 for the second trigger is not the constraint's, since a
context where `p'` and `q'` fail entails `p'p → q'` but violates the constraint. -/
theorem not_limitedSymmetryAt_not_and_second_of_printed {w : W} (hp : w ∉ I p) (hq : w ∉ I q) :
    {w} ⊆ {w | w ∈ I p ∩ I a → w ∈ I q} ∧
      ¬ LimitedSymmetryAt I {w} [.right .conj (.not (.trigger p a))] q := by
  rw [limitedSymmetryAt_not_and_second]
  refine ⟨fun v hv hpa ↦ ?_, fun h ↦ hq (h rfl fun hpa ↦ hp hpa.1)⟩
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact absurd hpa.1 hp

/-! ### Negation -/

theorem forall_agreeUpTo_append_not {n : ℕ} {K : SyntacticEnvironment Atom} {w : W} {X : Set W}
    (P : Prop → Prop) :
    (∀ L, AgreeUpTo n (K ++ [.not]) L → P (w ∈ L.truth I X)) ↔
      ∀ K', AgreeUpTo n K K' → P (w ∉ K'.truth I X) := by
  simp only [agreeUpTo_append_singleton, Step.AgreeUpTo, forall_exists_index, and_imp]
  refine ⟨fun h K' hK ↦ ?_, fun h L K' s' he hK hs ↦ ?_⟩
  · have := h _ K' .not rfl hK rfl
    rwa [truth_append] at this
  · subst he hs
    rw [truth_append]
    exact h K' hK

/-- A sentence respects the constraint iff its negation does (Proposition 3.4.1, p. 130). -/
theorem limitedSymmetry_not (A : Formula Atom) :
    LimitedSymmetry C (Formula.occurrences I (.not A)) ↔
      LimitedSymmetry C (Formula.occurrences I A) := by
  simp only [limitedSymmetry_occurrences_iff, Formula.triggers, List.forall_mem_map]
  refine forall₂_congr fun o _ ↦ ?_
  rw [limitedSymmetryAt_iff, limitedSymmetryAt_iff, rightItems_append]
  refine forall₂_congr fun w _ ↦ imp_congr_right fun _ ↦ forall₂_congr fun n _ ↦ ?_
  simp only [forall_agreeUpTo_append_not I (fun x ↦ x), forall_agreeUpTo_append_not I Not,
    not_not]
  exact and_comm

end Kalomoiros2023
