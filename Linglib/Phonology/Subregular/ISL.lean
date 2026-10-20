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
on that symbol and the `k - 1` input symbols before it. Chandlee introduced the class for the
local phonological processes that apply simultaneously, such as substitution, epenthesis,
deletion and metathesis, and Chandlee, Eyraud and Heinz characterize it by tails. We compute ISL
functions by rules, show that a function is `k`-ISL exactly when its residuals factor through
the last `k - 1` input symbols, and prove that the classes nest in `k`, begin at `k = 1` with the
letterwise homomorphisms, and are subsequential over a finite alphabet.

## Main definitions

* `ISLRule k α β`: a rule emitting a block from a window of `k - 1` input symbols
* `ISLRule.apply`: the function a rule computes
* `IsLeftInputStrictlyLocal k f`, `IsRightInputStrictlyLocal k f`: some rule computes `f`,
  scanning left to right or right to left

## Main results

* `isLeftInputStrictlyLocal_iff_factorsThrough_residual`: characterization by residuals
* `IsLeftInputStrictlyLocal.weaken`: `k`-ISL functions are `k'`-ISL for `k ≤ k'`
* `isLeftInputStrictlyLocal_one_iff`: the `1`-ISL functions are the letterwise homomorphisms
* `IsLeftInputStrictlyLocal.isLeftSubsequential`: ISL functions are subsequential

## Implementation notes

Rules carry neither the initial nor the final output of Chandlee, Eyraud and Heinz's
transducers, so the classes are the sequential ones with `f [] = []`; final devoicing, left-ISL
there through a final output, is right-ISL here. `0`-ISL and `1`-ISL coincide, and `k` indexes
`apply` alone.

## References

* [J. Chandlee, *Strictly Local Phonological Processes* (2014)][chandlee-2014]
* [J. Chandlee, R. Eyraud and J. Heinz, *Learning Strictly Local Subsequential Functions*
  (2014)][chandlee-eyraud-heinz-2014]
* [J. Chandlee and J. Heinz, *Strict Locality and Phonological Maps* (2018)][chandlee-heinz-2018]
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

/-- The window before each symbol is the last `k - 1` symbols of the input read so far. -/
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

/-- The residuals of a `k`-ISL function factor through the last `k - 1` input symbols, so inputs
ending alike have the same continuations. -/
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

/-- A rule emitting one symbol per input symbol is Mealy-computable, the bounded input window
being the state. -/
theorem ISLRule.isMealyComputable_apply [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  isMealyComputable_windowRun _ _ _ hs

/-- Over a finite input alphabet, right-ISL functions are right-subsequential. -/
theorem IsRightInputStrictlyLocal.isRightSubsequential [Fintype α]
    (hf : IsRightInputStrictlyLocal k f) : IsRightSubsequential f :=
  IsLeftInputStrictlyLocal.isLeftSubsequential hf

end Subregular
