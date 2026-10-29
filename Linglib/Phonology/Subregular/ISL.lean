/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.DropRight
public import Linglib.Core.Computability.Subsequential
public import Linglib.Core.Computability.Residual

/-!
# Input strictly local functions

This file defines the input strictly local functions. A function `f : List α → List β` is
*`k`-input strictly local* (`k`-ISL) when the block it emits for each input symbol depends only
on that symbol and the `k - 1` input symbols before it. Chandlee introduced ISL functions for the
local phonological processes that apply simultaneously, and Chandlee, Eyraud and Heinz
characterize them by tails: `f` is `k`-ISL when its residuals factor through the last `k - 1`
input symbols. We compute ISL functions by rules, show that a function is computed by a rule
exactly when it fixes `[]`, preserves prefixes, and meets that tail condition, and prove that the
classes nest in `k`, begin at `k = 1` with the letterwise homomorphisms, and are subsequential
over a finite alphabet.

A rule emits one block per input symbol and nothing at the end of the word, so the classes here
are the sequential functions with `f [] = []` that meet the tail condition. Chandlee, Eyraud and
Heinz's transducers also write a final output at the end of the word, which settles any output
still pending there, so their class is strictly larger. A process whose context lies to the right
of its target can be ISL here only scanning right to left, as final devoicing is right-ISL. A
process with context on both sides, such as intervocalic voicing, which maps `at` to `at` but
`ata` to `ada`, preserves prefixes in neither direction, and neither does local metathesis, so
both lie outside the left and the right class here, although both meet the tail condition with a
final output.

## Main definitions

* `ISLRule k α β`: a rule emitting a block from a window of `k - 1` input symbols
* `ISLRule.apply`: the function a rule computes
* `ISLRule.applyOnTier`: a rule run with its window over the tier projection of its input
* `IsLeftInputStrictlyLocal k f`, `IsRightInputStrictlyLocal k f`: some rule computes `f`,
  scanning left to right or right to left

## Main results

* `isLeftInputStrictlyLocal_iff_factorsThrough_residual`: the class is the prefix-preserving
  functions fixing `[]` whose residuals meet the tail condition
* `IsLeftInputStrictlyLocal.weaken`: `k`-ISL functions are `k'`-ISL for `k ≤ k'`
* `isLeftInputStrictlyLocal_one_iff`: the `1`-ISL functions are the letterwise homomorphisms
* `IsLeftInputStrictlyLocal.isLeftSubsequential`: ISL functions are subsequential

## Implementation notes

Rules carry neither the initial nor the final output of Chandlee, Eyraud and Heinz's
transducers. A theorem refuting membership in the class here therefore refutes their ISL only
when it refutes the tail condition itself, as the separations in `Subregular.OSL` do.
`0`-ISL and `1`-ISL coincide, and `k` indexes `apply` alone.

## References

* [J. Chandlee, *Strictly Local Phonological Processes* (2014)][chandlee-2014]
* [J. Chandlee, R. Eyraud and J. Heinz, *Learning Strictly Local Subsequential Functions*
  (2014)][chandlee-eyraud-heinz-2014]
* [J. Chandlee and J. Heinz, *Strict Locality and Phonological Maps* (2018)][chandlee-heinz-2018]
* [S. Andersson, H. Dolatian and Y. Hao, *Computing Vowel Harmony: The Generative Capacity of
  Search & Copy* (2020)][andersson-dolatian-hao-2020]
-/

@[expose] public section

namespace Subregular

open SubsequentialTransducer Function

variable {α β : Type*} {k k' : ℕ} {f : List α → List β}

/-- A **`k`-input strictly local rule** emits, for each input symbol, a block of output symbols
computed from the last `k - 1` input symbols and the symbol itself. -/
structure ISLRule (k : ℕ) (α β : Type*) where
  /-- The block emitted for the current symbol after the given window of preceding input. -/
  windowOutput : List α → α → List β

namespace ISLRule

variable (r : ISLRule k α β)

/-- The rule applied from a given window, the window recursion `windowRun` that accumulates the
input truncated to `k - 1` symbols. -/
def applyAux : (window : List α) → (rest : List α) → List β :=
  windowRun (k - 1) r.windowOutput fun _ x ↦ [x]

/-- The string function computed by the rule, scanning left to right from the empty window. -/
def apply (input : List α) : List β :=
  r.applyAux [] input

@[simp] lemma applyAux_nil (window : List α) : r.applyAux window [] = [] := rfl

@[simp] lemma applyAux_cons (window : List α) (x : α) (xs : List α) :
    r.applyAux window (x :: xs)
      = r.windowOutput window x ++ r.applyAux ((window ++ [x]).rtake (k - 1)) xs :=
  rfl

@[simp] lemma apply_nil : r.apply [] = [] := rfl

@[simp] lemma apply_singleton (x : α) : r.apply [x] = r.windowOutput [] x :=
  List.append_nil _

private lemma windowRun_input (n : ℕ) (w u : List α) :
    windowRun n (fun _ x ↦ [x]) (fun _ x ↦ [x]) w u = u := by
  induction u generalizing w with
  | nil => rfl
  | cons y ys ih => simp [windowRun, ih]

theorem apply_append_singleton (u : List α) (x : α) :
    r.apply (u ++ [x]) = r.apply u ++ r.windowOutput (u.rtake (k - 1)) x := by
  have h := windowRun_append_singleton (out := r.windowOutput) (upd := fun _ x ↦ [x])
    (w := []) (Nat.zero_le (k - 1)) u x
  rwa [windowRun_input, List.nil_append] at h

end ISLRule

/-- `f` is **`k`-left-input strictly local** if some `k`-ISL rule computes it. -/
def IsLeftInputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  ∃ r : ISLRule k α β, r.apply = f

/-- `f` is **`k`-right-input strictly local** if its reverse-conjugate is `k`-left-ISL, that is,
if some `k`-ISL rule computes it scanning right to left. -/
def IsRightInputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  IsLeftInputStrictlyLocal k (List.revConj f)

lemma ISLRule.isLeftInputStrictlyLocal_apply (r : ISLRule k α β) :
    IsLeftInputStrictlyLocal k r.apply :=
  ⟨r, rfl⟩

/-! ### Residuals -/

lemma IsLeftInputStrictlyLocal.map_nil (hf : IsLeftInputStrictlyLocal k f) : f [] = [] := by
  obtain ⟨r, rfl⟩ := hf
  rfl

theorem IsLeftInputStrictlyLocal.isPrefix (hf : IsLeftInputStrictlyLocal k f) (u v : List α) :
    f u <+: f (u ++ v) := by
  obtain ⟨r, rfl⟩ := hf
  exact isPrefix_append_of_append_singleton (fun u x ↦ ⟨_, (r.apply_append_singleton u x).symm⟩)
    u v

theorem IsLeftInputStrictlyLocal.factorsThrough_residual (hf : IsLeftInputStrictlyLocal k f) :
    f.residual.FactorsThrough fun u ↦ u.rtake (k - 1) := by
  obtain ⟨r, rfl⟩ := hf
  exact factorsThrough_residual_of_append_singleton (fun w x ↦ (w ++ [x]).rtake (k - 1))
    r.windowOutput (fun u x ↦ (List.rtake_append_rtake _ _ _).symm) r.apply_append_singleton

theorem IsLeftInputStrictlyLocal.of_factorsThrough_residual (h₀ : f [] = [])
    (hpre : ∀ u v, f u <+: f (u ++ v))
    (hf : f.residual.FactorsThrough fun u ↦ u.rtake (k - 1)) :
    IsLeftInputStrictlyLocal k f := by
  obtain ⟨g, hg⟩ := exists_append_singleton_of_factorsThrough_residual hpre hf
  refine ⟨⟨g⟩, funext fun u ↦ ?_⟩
  induction u using List.reverseRecOn with
  | nil => exact h₀.symm
  | append_singleton u x ih => rw [ISLRule.apply_append_singleton, hg, ih]

/-- A function is `k`-ISL if and only if it fixes `[]`, is prefix-preserving, and has residuals
factoring through the last `k - 1` input symbols. -/
theorem isLeftInputStrictlyLocal_iff_factorsThrough_residual :
    IsLeftInputStrictlyLocal k f ↔ f [] = [] ∧ (∀ u v, f u <+: f (u ++ v)) ∧
      f.residual.FactorsThrough fun u ↦ u.rtake (k - 1) :=
  ⟨fun hf ↦ ⟨hf.map_nil, hf.isPrefix, hf.factorsThrough_residual⟩,
    fun h ↦ .of_factorsThrough_residual h.1 h.2.1 h.2.2⟩

/-! ### The hierarchy in `k` -/

/-- A `k`-ISL function is `k'`-ISL for every `k' ≥ k`. -/
protected theorem IsLeftInputStrictlyLocal.weaken (hf : IsLeftInputStrictlyLocal k f)
    (hk : k ≤ k') : IsLeftInputStrictlyLocal k' f :=
  .of_factorsThrough_residual hf.map_nil hf.isPrefix fun u₁ u₂ h ↦
    hf.factorsThrough_residual <| by
      simpa [List.rtake_rtake, Nat.min_eq_left (Nat.sub_le_sub_right hk 1)] using
        congrArg (List.rtake · (k - 1)) h

protected theorem IsRightInputStrictlyLocal.weaken (hf : IsRightInputStrictlyLocal k f)
    (hk : k ≤ k') : IsRightInputStrictlyLocal k' f :=
  IsLeftInputStrictlyLocal.weaken hf hk

/-- The `1`-ISL functions are the letterwise homomorphisms `List.flatMap h`, among them the
erasing projections `List.filterMap g`. -/
theorem isLeftInputStrictlyLocal_one_iff :
    IsLeftInputStrictlyLocal 1 f ↔ ∃ h : α → List β, List.flatMap h = f := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨fun x ↦ r.windowOutput [] x, funext fun u ↦ ?_⟩,
    fun ⟨h, hh⟩ ↦ ⟨⟨fun _ x ↦ h x⟩, hh ▸ funext fun u ↦ ?_⟩⟩
  · subst hr
    induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u x ih => simp [ISLRule.apply_append_singleton, ← ih]
  · induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u x ih => simp [ISLRule.apply_append_singleton, ih]

/-! ### ISL ⊆ Subsequential

An ISL rule is a window recursion accumulating the input, so over a finite input alphabet the
bounded input window is a finite state space (`isLeftSubsequential_windowRun`). -/

/-- Over a finite input alphabet, left-ISL functions are left-subsequential. -/
theorem IsLeftInputStrictlyLocal.isLeftSubsequential [Fintype α]
    (hf : IsLeftInputStrictlyLocal k f) : IsLeftSubsequential f := by
  obtain ⟨r, rfl⟩ := hf
  exact isLeftSubsequential_windowRun _ _ _

theorem ISLRule.isMealyComputable_apply [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  isMealyComputable_windowRun _ _ _ hs

theorem IsRightInputStrictlyLocal.isRightSubsequential [Fintype α]
    (hf : IsRightInputStrictlyLocal k f) : IsRightSubsequential f :=
  IsLeftInputStrictlyLocal.isLeftSubsequential hf

/-! ### Input tiers -/

namespace ISLRule

variable (r : ISLRule k α β) (p : α → Prop) [DecidablePred p]

/-- The rule run with its window over the tier `p` of the input alphabet, so that each block
depends on the last `k - 1` on-tier symbols read ([andersson-dolatian-hao-2020]). -/
def applyOnTier : List α → List β :=
  windowRun (k - 1) r.windowOutput (fun _ x ↦ [x].filter (p ·)) []

private lemma windowRun_filter (n : ℕ) (w u : List α) :
    windowRun n (fun _ x ↦ [x].filter (p ·)) (fun _ x ↦ [x].filter (p ·)) w u =
      u.filter (p ·) := by
  induction u generalizing w with
  | nil => rfl
  | cons y ys ih => by_cases hy : p y <;> simp [windowRun, ih, hy]

@[simp] lemma applyOnTier_nil : r.applyOnTier p [] = [] := rfl

theorem applyOnTier_append_singleton (u : List α) (x : α) :
    r.applyOnTier p (u ++ [x]) =
      r.applyOnTier p u ++ r.windowOutput ((u.filter (p ·)).rtake (k - 1)) x := by
  have h := windowRun_append_singleton (out := r.windowOutput)
    (upd := fun _ x ↦ [x].filter (p ·)) (w := []) (Nat.zero_le (k - 1)) u x
  rwa [windowRun_filter, List.nil_append] at h

theorem applyOnTier_true : r.applyOnTier (fun _ ↦ True) = r.apply := by
  simp [applyOnTier]
  rfl

theorem isLeftSubsequential_applyOnTier [Fintype α] :
    IsLeftSubsequential (r.applyOnTier p) :=
  isLeftSubsequential_windowRun _ _ _

end ISLRule

end Subregular
