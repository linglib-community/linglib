/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.ISL

/-!
# Output strictly local functions

This file defines the output strictly local functions. A function `f : List α → List β` is
*`k`-output strictly local* (`k`-OSL) when the block it emits for each input symbol depends only
on that symbol and the last `k - 1` symbols already emitted. Progressive spreading is the
motivating case, since its trigger is adjacent in the output however far back it lies in the
input. Chandlee, Eyraud and Heinz characterize the class by tails and show it incomparable with
the input strictly local functions, and Burness and McMullin relativize the window to a tier of
the output alphabet.

We compute OSL functions by rules, characterize them by residuals, and prove that the classes
nest in `k` and are subsequential over a finite alphabet. Dissimilation after an input symbol is
ISL and not OSL, progressive spreading is OSL and neither ISL nor right-OSL, and long-distance
assimilation across transparent symbols is Mealy-computable and neither ISL nor OSL.

## Main definitions

* `OSLRule k α β`: a rule emitting a block from a window of `k - 1` output symbols
* `OSLRule.apply`: the function a rule computes
* `OSLRule.applyOnTier`: a rule run with its window over the tier projection of its output
* `IsLeftOutputStrictlyLocal k f`, `IsRightOutputStrictlyLocal k f`: some rule computes `f`,
  scanning left to right or right to left

## Main results

* `isLeftOutputStrictlyLocal_iff_factorsThrough_residual`: characterization by residuals
* `IsLeftOutputStrictlyLocal.weaken`: `k`-OSL functions are `k'`-OSL for `k ≤ k'`
* `isLeftOutputStrictlyLocal_one_iff`: the `1`-OSL functions are the letterwise homomorphisms
* `IsLeftOutputStrictlyLocal.isLeftSubsequential`: OSL functions are subsequential
* `ISLRule.dissimilate_not_isLeftOutputStrictlyLocal`,
  `OSLRule.spread_not_isLeftInputStrictlyLocal`: ISL and OSL are incomparable
* `longDistanceAgree_not_isLeftInputStrictlyLocal`,
  `longDistanceAgree_not_isLeftOutputStrictlyLocal`: a Mealy-computable function in neither

## Implementation notes

Rules carry neither the initial nor the final output of Chandlee, Eyraud and Heinz's
transducers, so the classes are the sequential ones with `f [] = []`; progressive spreading fails
right-OSL here for want of a final output. `0`-OSL and `1`-OSL coincide, and `k` indexes `apply`
alone.

## TODO

* Final outputs, recovering Chandlee, Eyraud and Heinz's classes through
  `Function.prefixFunction`.
* The output tier-based class as a predicate, characterized by residuals.

## References

* [J. Chandlee, R. Eyraud and J. Heinz, *Learning Strictly Local Subsequential Functions*
  (2014)][chandlee-eyraud-heinz-2014]
* [J. Chandlee, R. Eyraud and J. Heinz, *Output Strictly Local Functions*
  (2015)][chandlee-eyraud-heinz-2015]
* [P. Burness and K. McMullin, *Multi-Tiered Strictly Local Functions*
  (2020)][burness-mcmullin-2020]
-/

@[expose] public section

namespace Subregular

open SubsequentialTransducer Function

variable {α β : Type*} {k k' : ℕ} {f : List α → List β}

/-- A **`k`-output strictly local rule** emits, for each input symbol, a block computed from
the last `k - 1` symbols it has emitted and the input symbol itself. -/
structure OSLRule (k : ℕ) (α β : Type*) where
  /-- The block emitted for the current input symbol after the given window of output. -/
  windowOutput : List β → α → List β

namespace OSLRule

variable (r : OSLRule k α β)

/-- The rule applied from a given window, the window recursion `windowRun` that accumulates what
the rule emits truncated to `k - 1` symbols. -/
def applyAux : (outputWindow : List β) → (rest : List α) → List β :=
  windowRun (k - 1) r.windowOutput r.windowOutput

/-- The string function computed by the rule, scanning left to right from the empty window. -/
def apply (input : List α) : List β :=
  r.applyAux [] input

@[simp] lemma applyAux_nil (outputWindow : List β) : r.applyAux outputWindow [] = [] := rfl

@[simp] lemma applyAux_cons (outputWindow : List β) (x : α) (xs : List α) :
    r.applyAux outputWindow (x :: xs)
      = r.windowOutput outputWindow x
          ++ r.applyAux ((outputWindow ++ r.windowOutput outputWindow x).rtake (k - 1)) xs :=
  rfl

@[simp] lemma apply_nil : r.apply [] = [] := rfl

@[simp] lemma apply_singleton (x : α) : r.apply [x] = r.windowOutput [] x :=
  List.append_nil _

theorem apply_append_singleton (u : List α) (x : α) :
    r.apply (u ++ [x]) = r.apply u ++ r.windowOutput ((r.apply u).rtake (k - 1)) x := by
  have h := windowRun_append_singleton (out := r.windowOutput) (upd := r.windowOutput)
    (w := []) (Nat.zero_le (k - 1)) u x
  rwa [List.nil_append] at h

end OSLRule

/-- `f` is **`k`-left-output strictly local** if some `k`-OSL rule computes it. -/
def IsLeftOutputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  ∃ r : OSLRule k α β, r.apply = f

/-- `f` is **`k`-right-output strictly local** if its reverse-conjugate is `k`-left-OSL, that is,
if some `k`-OSL rule computes it scanning right to left. -/
def IsRightOutputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  IsLeftOutputStrictlyLocal k (List.revConj f)

lemma OSLRule.isLeftOutputStrictlyLocal_apply (r : OSLRule k α β) :
    IsLeftOutputStrictlyLocal k r.apply :=
  ⟨r, rfl⟩

/-! ### Residuals -/

lemma IsLeftOutputStrictlyLocal.map_nil (hf : IsLeftOutputStrictlyLocal k f) : f [] = [] := by
  obtain ⟨r, rfl⟩ := hf
  rfl

theorem IsLeftOutputStrictlyLocal.isPrefix (hf : IsLeftOutputStrictlyLocal k f) (u v : List α) :
    f u <+: f (u ++ v) := by
  obtain ⟨r, rfl⟩ := hf
  exact isPrefix_append_of_append_singleton (fun u x ↦ ⟨_, (r.apply_append_singleton u x).symm⟩)
    u v

theorem IsLeftOutputStrictlyLocal.factorsThrough_residual (hf : IsLeftOutputStrictlyLocal k f) :
    f.residual.FactorsThrough fun u ↦ (f u).rtake (k - 1) := by
  obtain ⟨r, rfl⟩ := hf
  refine factorsThrough_residual_of_append_singleton
    (fun w x ↦ (w ++ r.windowOutput w x).rtake (k - 1)) r.windowOutput (fun u x ↦ ?_)
    r.apply_append_singleton
  rw [r.apply_append_singleton, List.rtake_append_rtake]

theorem IsLeftOutputStrictlyLocal.of_factorsThrough_residual (h₀ : f [] = [])
    (hpre : ∀ u v, f u <+: f (u ++ v))
    (hf : f.residual.FactorsThrough fun u ↦ (f u).rtake (k - 1)) :
    IsLeftOutputStrictlyLocal k f := by
  obtain ⟨g, hg⟩ := exists_append_singleton_of_factorsThrough_residual hpre hf
  refine ⟨⟨g⟩, funext fun u ↦ ?_⟩
  induction u using List.reverseRecOn with
  | nil => exact h₀.symm
  | append_singleton u x ih => rw [OSLRule.apply_append_singleton, hg, ih]

/-- A function is `k`-OSL if and only if it fixes `[]`, is prefix-preserving, and has residuals
factoring through the last `k - 1` output symbols. -/
theorem isLeftOutputStrictlyLocal_iff_factorsThrough_residual :
    IsLeftOutputStrictlyLocal k f ↔ f [] = [] ∧ (∀ u v, f u <+: f (u ++ v)) ∧
      f.residual.FactorsThrough fun u ↦ (f u).rtake (k - 1) :=
  ⟨fun hf ↦ ⟨hf.map_nil, hf.isPrefix, hf.factorsThrough_residual⟩,
    fun h ↦ .of_factorsThrough_residual h.1 h.2.1 h.2.2⟩

/-! ### The hierarchy in `k` -/

/-- A `k`-OSL function is `k'`-OSL for every `k' ≥ k`. -/
protected theorem IsLeftOutputStrictlyLocal.weaken (hf : IsLeftOutputStrictlyLocal k f)
    (hk : k ≤ k') : IsLeftOutputStrictlyLocal k' f :=
  .of_factorsThrough_residual hf.map_nil hf.isPrefix fun u₁ u₂ h ↦
    hf.factorsThrough_residual <| by
      simpa [List.rtake_rtake, Nat.min_eq_left (Nat.sub_le_sub_right hk 1)] using
        congrArg (List.rtake · (k - 1)) h

protected theorem IsRightOutputStrictlyLocal.weaken (hf : IsRightOutputStrictlyLocal k f)
    (hk : k ≤ k') : IsRightOutputStrictlyLocal k' f :=
  IsLeftOutputStrictlyLocal.weaken hf hk

/-- The `1`-OSL functions are the letterwise homomorphisms `List.flatMap h`, which are also the
`1`-ISL functions. -/
theorem isLeftOutputStrictlyLocal_one_iff :
    IsLeftOutputStrictlyLocal 1 f ↔ ∃ h : α → List β, List.flatMap h = f := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨fun x ↦ r.windowOutput [] x, funext fun u ↦ ?_⟩,
    fun ⟨h, hh⟩ ↦ ⟨⟨fun _ x ↦ h x⟩, hh ▸ funext fun u ↦ ?_⟩⟩
  · subst hr
    induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u x ih => simp [OSLRule.apply_append_singleton, ← ih]
  · induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u x ih => simp [OSLRule.apply_append_singleton, ih]

/-! ### OSL ⊆ Subsequential

An OSL rule is a window recursion accumulating its own output, so over a finite output alphabet
the bounded output window is a finite state space (`isLeftSubsequential_windowRun`). -/

/-- Over a finite output alphabet, left-OSL functions are left-subsequential. -/
theorem IsLeftOutputStrictlyLocal.isLeftSubsequential [Fintype β]
    (hf : IsLeftOutputStrictlyLocal k f) : IsLeftSubsequential f := by
  obtain ⟨r, rfl⟩ := hf
  exact isLeftSubsequential_windowRun _ _ _

theorem OSLRule.isMealyComputable_apply [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  isMealyComputable_windowRun _ _ _ hs

theorem IsRightOutputStrictlyLocal.isRightSubsequential [Fintype β]
    (hf : IsRightOutputStrictlyLocal k f) : IsRightSubsequential f :=
  IsLeftOutputStrictlyLocal.isLeftSubsequential hf

/-! ### Output tiers -/

namespace OSLRule

variable (r : OSLRule k α β) (p : β → Prop) [DecidablePred p]

/-- The rule run with its window over the tier `p` of the output alphabet, so that each block
depends on the last `k - 1` on-tier symbols emitted ([burness-mcmullin-2020], Definition 8). -/
def applyOnTier : List α → List β :=
  windowRun (k - 1) r.windowOutput (fun w x ↦ (r.windowOutput w x).filter (p ·)) []

private lemma windowRun_filter {n : ℕ} {out : List β → α → List β} (w : List β) (u : List α) :
    windowRun n (fun w x ↦ (out w x).filter (p ·)) (fun w x ↦ (out w x).filter (p ·)) w u =
      (windowRun n out (fun w x ↦ (out w x).filter (p ·)) w u).filter (p ·) := by
  induction u generalizing w with
  | nil => rfl
  | cons y ys ih => simp [windowRun, ih, List.filter_append]

@[simp] lemma applyOnTier_nil : r.applyOnTier p [] = [] := rfl

theorem applyOnTier_append_singleton (u : List α) (x : α) :
    r.applyOnTier p (u ++ [x]) = r.applyOnTier p u
      ++ r.windowOutput (((r.applyOnTier p u).filter (p ·)).rtake (k - 1)) x := by
  have h := windowRun_append_singleton (out := r.windowOutput)
    (upd := fun w x ↦ (r.windowOutput w x).filter (p ·)) (w := []) (Nat.zero_le (k - 1)) u x
  rwa [windowRun_filter, List.nil_append] at h

theorem applyOnTier_true : r.applyOnTier (fun _ ↦ True) = r.apply := by
  simp [applyOnTier]
  rfl

theorem filter_applyOnTier (r : OSLRule k α α) {p : α → Prop} [DecidablePred p]
    (hr : ∀ w x, ∀ y ∈ r.windowOutput w x, p y ↔ p x) (l : List α) :
    (r.applyOnTier p l).filter (p ·) = r.apply (l.filter (p ·)) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
    rw [applyOnTier_append_singleton, List.filter_append, ih, List.filter_append]
    set W := (r.apply (u.filter (p ·))).rtake (k - 1)
    by_cases hx : p x
    · rw [(List.filter_eq_self (l := r.windowOutput W x)).2 fun y hy ↦
        decide_eq_true ((hr W x y hy).2 hx), List.filter_singleton, decide_eq_true hx,
        Bool.cond_true, apply_append_singleton]
    · rw [(List.filter_eq_nil_iff (l := r.windowOutput W x)).2 fun y hy ↦
        by simpa using mt (hr W x y hy).1 hx, List.filter_singleton, decide_eq_false hx,
        Bool.cond_false, List.append_nil, List.append_nil]

theorem isLeftSubsequential_applyOnTier [Fintype β] :
    IsLeftSubsequential (r.applyOnTier p) :=
  isLeftSubsequential_windowRun _ _ _

end OSLRule

/-! ### ISL and OSL are incomparable

Chandlee, Eyraud and Heinz separate the two classes and place a subsequential function outside
both. Over the residual characterizations each separation is one pair of inputs with the same
window and different continuations. -/

private theorem rtake_cons_replicate (n : ℕ) (x y : α) :
    (x :: List.replicate n y).rtake n = List.replicate n y := by
  simpa using List.rtake_append_length (l₁ := [x]) (l₂ := List.replicate n y)

section Incomparable

variable [DecidableEq α] {a b c : α}

/-- Dissimilation of `a` to `b` after an input `a` (the function `f₂` of
[chandlee-eyraud-heinz-2014], Theorem 5). -/
def ISLRule.dissimilate (a b : α) : ISLRule 2 α α where
  windowOutput w x := if w = [a] ∧ x = a then [b] else [x]

/-- Dissimilation is not OSL, since `aa` and `ab` have the same output `ab` but continue
differently on `a`. -/
theorem ISLRule.dissimilate_not_isLeftOutputStrictlyLocal (hab : a ≠ b) (k : ℕ) :
    ¬ IsLeftOutputStrictlyLocal k (dissimilate a b).apply := fun h ↦ by
  have e := congrFun (h.factorsThrough_residual (a := [a, a]) (b := [a, b])
    (by simp [ISLRule.apply, ISLRule.applyAux, windowRun, dissimilate, List.rtake, hab.symm]))
    [a]
  rw [residual_eq_drop (h.isPrefix _), residual_eq_drop (h.isPrefix _)] at e
  simp [ISLRule.apply, ISLRule.applyAux, windowRun, dissimilate, List.rtake, hab.symm] at e

/-- Unbounded progressive spreading of `a`, under which every symbol after an `a` surfaces as
`a`. -/
def OSLRule.spread (a : α) : OSLRule 2 α α where
  windowOutput w x := if w = [a] then [a] else [x]

private theorem spread_apply_cons_replicate (n : ℕ) :
    (OSLRule.spread a).apply (a :: List.replicate n b) = List.replicate (n + 1) a := by
  induction n with
  | zero => simp [OSLRule.spread]
  | succ n ih =>
    rw [List.replicate_succ', ← List.cons_append, OSLRule.apply_append_singleton, ih,
      List.replicate_succ' (n := n + 1)]
    simp [OSLRule.spread, List.replicate_succ', List.rtake_concat_succ]

private theorem spread_apply_replicate (hab : a ≠ b) (n : ℕ) :
    (OSLRule.spread a).apply (List.replicate n b) = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', OSLRule.apply_append_singleton, ih]
    have : (List.replicate n b).rtake (2 - 1) ≠ [a] := fun h ↦ hab <|
      List.eq_of_mem_replicate ((List.rtake_suffix _ _).subset (h ▸ List.mem_singleton_self a))
    simp [OSLRule.spread, this]

/-- Spreading is not ISL, since `a bᵏ⁻¹` and `bᵏ` end in the same `k - 1` input symbols while a
further `b` surfaces as `a` after the first and as `b` after the second. -/
theorem OSLRule.spread_not_isLeftInputStrictlyLocal (hab : a ≠ b) (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k (spread a).apply := fun h ↦ by
  have e := congrFun (h.factorsThrough_residual (a := a :: List.replicate (k - 1) b)
    (b := b :: List.replicate (k - 1) b) (by simp only [rtake_cons_replicate])) [b]
  rw [residual_eq_drop (h.isPrefix _), residual_eq_drop (h.isPrefix _)] at e
  simp only [List.cons_append, ← List.replicate_succ', spread_apply_cons_replicate,
    ← List.replicate_succ, spread_apply_replicate hab, List.length_replicate,
    List.drop_replicate, Nat.add_sub_cancel_left] at e
  exact hab (List.singleton_inj.mp e)

theorem OSLRule.spread_not_isRightOutputStrictlyLocal (hab : a ≠ b) (k : ℕ) :
    ¬ IsRightOutputStrictlyLocal k (spread a).apply := fun h ↦ by
  have e := IsLeftOutputStrictlyLocal.isPrefix h [b] [a]
  simp [List.revConj, OSLRule.apply, OSLRule.applyAux, windowRun, spread, List.rtake,
    hab.symm] at e

/-- The flag machine for long-distance assimilation of `b` to `a`, under which `b` surfaces as `a`
after an `a` however far back (the function `f₁` of [chandlee-eyraud-heinz-2014], Theorem 4). -/
def longDistanceAgree (a b : α) : Mealy Bool α α :=
  Mealy.ofFlag (· = a) fun s x ↦ if s ∧ x = b then a else x

private theorem longDistanceAgree_runFrom_replicate (hcb : c ≠ b) (s : Bool) (n : ℕ) :
    (longDistanceAgree a b).runFrom s (List.replicate n c) = List.replicate n c := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Mealy.runFrom_cons, ih]
    simp [longDistanceAgree, hcb]

private theorem longDistanceAgree_run_cons_replicate (hcb : c ≠ b) (x : α) (n : ℕ) :
    (longDistanceAgree a b).run (x :: List.replicate n c) = x :: List.replicate n c := by
  rw [Mealy.run, Mealy.runFrom_cons, longDistanceAgree_runFrom_replicate hcb]
  simp [longDistanceAgree]

/-- Long-distance assimilation is not ISL, since `acᵏ⁻¹` and `bcᵏ⁻¹` end alike while a further
`b` surfaces as `a` only after the first. -/
theorem longDistanceAgree_not_isLeftInputStrictlyLocal (hab : a ≠ b) (hca : c ≠ a) (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k (longDistanceAgree a b).run := fun h ↦ by
  have e := congrFun (h.factorsThrough_residual (a := a :: List.replicate (k - 1) c)
    (b := b :: List.replicate (k - 1) c) (by simp only [rtake_cons_replicate])) [b]
  simp [Mealy.residual_run, longDistanceAgree, List.any_replicate, hca, hab.symm] at e
  exact hab e

/-- Long-distance assimilation is not OSL, since `acᵏ⁻¹` and `bcᵏ⁻¹` are output unchanged and
end alike while a further `b` surfaces as `a` only after the first. -/
theorem longDistanceAgree_not_isLeftOutputStrictlyLocal (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) (k : ℕ) : ¬ IsLeftOutputStrictlyLocal k (longDistanceAgree a b).run := by
  intro h
  have e := congrFun (h.factorsThrough_residual (a := a :: List.replicate (k - 1) c)
    (b := b :: List.replicate (k - 1) c) (by
      simp only [longDistanceAgree_run_cons_replicate hcb, rtake_cons_replicate])) [b]
  simp [Mealy.residual_run, longDistanceAgree, List.any_replicate, hca, hab.symm] at e
  exact hab e

end Incomparable

end Subregular
