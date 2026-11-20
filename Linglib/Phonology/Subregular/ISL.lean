/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Fintype.List
public import Linglib.Core.Data.List.DropRight
public import Linglib.Core.Computability.Subsequential
public import Linglib.Core.Computability.Residual

/-!
# Input strictly local functions

A function `f : List α → List β` is *`k`-input strictly local* (`k`-ISL) when its residuals
factor through the last `k - 1` symbols of the input, so that two inputs ending alike are
continued alike. This is the tail condition by which Chandlee, Eyraud and Heinz define the class
that Chandlee introduced for the local phonological processes applying simultaneously.

An `ISLRule k α β` emits, for each input symbol, a block computed from that symbol and the
`k - 1` symbols before it, and `ISLRule.apply` is the function it computes. A rule writes nothing
before the first symbol and nothing at the end of the word. A function is `k`-ISL exactly when it
is a rule between an initial output and a final output read off the last `k - 1` input symbols
(`isLeftInputStrictlyLocal_iff_exists_rule`), and the functions of the rules themselves are the
`k`-ISL functions that fix `[]` and preserve prefixes (`exists_islRule_apply_eq_iff`).

The classes nest in `k` (`IsLeftInputStrictlyLocal.mono`), begin at `k = 1` with the letterwise
homomorphisms between two fixed blocks (`isLeftInputStrictlyLocal_one_iff`), and are
subsequential over a finite input alphabet (`IsLeftInputStrictlyLocal.isLeftSubsequential`).
`ISLRule.applyOnTier` runs a rule with its window over the tier projection of the input.

## Implementation notes

The definition is the tail condition alone. It does not ask that `f` be subsequential, which
follows over a finite input alphabet since the windows are then finitely many. `0`-ISL and
`1`-ISL coincide.

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

/-! ### Window transducers -/

section Window

variable {γ : Type*}

/-- The transducer whose state is a window of the last `n` accumulated symbols. `out`
emits from the window and the current symbol, and `upd` chooses what the window accumulates
(`fun _ x ↦ [x]` for the input of ISL, `out` for the output of OSL). -/
@[simps]
def ofWindow (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    SubsequentialTransducer {l : List γ // l.length ≤ n} α β where
  start := ⟨[], Nat.zero_le _⟩
  step w x := ⟨(w.val ++ upd w.val x).rtake n, List.length_rtake_le _ _⟩
  output w x := out w.val x
  finalOutput _ := []

/-- The window recursion computed by `ofWindow`, each step of which emits `out` and extends the
window by `upd`, truncated to length `n`. -/
def windowRun (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    List γ → List α → List β
  | _, [] => []
  | w, x :: xs => out w x ++ windowRun n out upd ((w ++ upd w x).rtake n) xs

variable {n : ℕ} {out : List γ → α → List β} {upd : List γ → α → List γ}

theorem runFrom_ofWindow (w : {l : List γ // l.length ≤ n}) (xs : List α) :
    (ofWindow n out upd).runFrom w xs = windowRun n out upd w.val xs := by
  induction xs generalizing w with
  | nil => simp [windowRun]
  | cons x xs ih => rw [runFrom_cons, windowRun]; exact congrArg _ (ih _)

theorem run_ofWindow : (ofWindow n out upd).run = windowRun n out upd [] :=
  funext fun xs ↦ runFrom_ofWindow ⟨[], Nat.zero_le _⟩ xs

theorem windowRun_append_singleton {w : List γ} (hw : w.length ≤ n) (u : List α) (x : α) :
    windowRun n out upd w (u ++ [x]) =
      windowRun n out upd w u ++ out ((w ++ windowRun n upd upd w u).rtake n) x := by
  induction u generalizing w with
  | nil => simp [windowRun, List.rtake_of_length_le hw]
  | cons y ys ih =>
    simp only [List.cons_append, windowRun, List.append_assoc, ih (List.length_rtake_le _ _),
      List.rtake_rtake_append]

theorem isLeftSubsequential_windowRun [Fintype γ] (n : ℕ) (out : List γ → α → List β)
    (upd : List γ → α → List γ) : IsLeftSubsequential (windowRun n out upd []) :=
  run_ofWindow (n := n) (out := out) (upd := upd) ▸ (ofWindow n out upd).isLeftSubsequential

theorem isMealyComputable_windowRun [Fintype γ] (n : ℕ) (out : List γ → α → List β)
    (upd : List γ → α → List γ) (hs : ∀ w x, (out w x).length = 1) :
    IsMealyComputable (windowRun n out upd []) :=
  run_ofWindow (n := n) (out := out) (upd := upd) ▸
    (ofWindow n out upd).isMealyComputable_run (fun w x ↦ hs w.val x) fun _ ↦ rfl

end Window

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

theorem isPrefix_apply (u v : List α) : r.apply u <+: r.apply (u ++ v) :=
  isPrefix_append_of_append_singleton (fun u x ↦ ⟨_, (r.apply_append_singleton u x).symm⟩) u v

end ISLRule

/-- `f` is **`k`-left-input strictly local** if its residuals factor through the last `k - 1`
input symbols. -/
def IsLeftInputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  f.residual.FactorsThrough fun u ↦ u.rtake (k - 1)

/-- `f` is **`k`-right-input strictly local** if its reverse-conjugate is `k`-left-ISL. -/
def IsRightInputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  IsLeftInputStrictlyLocal k (List.revConj f)

/-! ### Rules -/

theorem ISLRule.isLeftInputStrictlyLocal_apply (r : ISLRule k α β) :
    IsLeftInputStrictlyLocal k r.apply :=
  factorsThrough_residual_of_append_singleton (fun w x ↦ (w ++ [x]).rtake (k - 1))
    r.windowOutput (fun _ _ ↦ List.rtake_rtake_append.symm) r.apply_append_singleton

/-- A function is `k`-ISL if and only if it is computed by a rule between an initial output and
a final output read off the last `k - 1` input symbols. -/
theorem isLeftInputStrictlyLocal_iff_exists_rule :
    IsLeftInputStrictlyLocal k f ↔ ∃ (p : List β) (r : ISLRule k α β) (t : List α → List β),
      ∀ u, f u = p ++ r.apply u ++ t (u.rtake (k - 1)) := by
  refine ⟨fun hf ↦ ?_, fun ⟨p, r, t, h⟩ ↦ ?_⟩
  · obtain ⟨g, t, hg, ht⟩ := exists_prefixFunction_append_singleton_of_factorsThrough_residual hf
    refine ⟨f.prefixFunction [], ⟨g⟩, t, fun u ↦ ?_⟩
    rw [ht u]
    congr 1
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u x ih => rw [hg, ih, ISLRule.apply_append_singleton, List.append_assoc]
  · exact factorsThrough_residual_of_append_final (P := fun u ↦ p ++ r.apply u)
      (fun w x ↦ (w ++ [x]).rtake (k - 1)) r.windowOutput t
      (fun _ _ ↦ List.rtake_rtake_append.symm)
      (fun u x ↦ by rw [r.apply_append_singleton, List.append_assoc]) h

/-- The functions computed by `k`-ISL rules are the `k`-ISL functions that fix `[]` and
preserve prefixes. -/
theorem exists_islRule_apply_eq_iff :
    (∃ r : ISLRule k α β, r.apply = f) ↔
      f [] = [] ∧ (∀ u v, f u <+: f (u ++ v)) ∧ IsLeftInputStrictlyLocal k f := by
  refine ⟨?_, fun ⟨h₀, hpre, hf⟩ ↦ ?_⟩
  · rintro ⟨r, rfl⟩
    exact ⟨rfl, r.isPrefix_apply, r.isLeftInputStrictlyLocal_apply⟩
  · obtain ⟨g, hg⟩ := exists_append_singleton_of_factorsThrough_residual hpre hf
    refine ⟨⟨g⟩, funext fun u ↦ ?_⟩
    induction u using List.reverseRecOn with
    | nil => exact h₀.symm
    | append_singleton u x ih => rw [ISLRule.apply_append_singleton, hg, ih]

/-! ### The hierarchy in `k` -/

/-- A `k`-ISL function is `k'`-ISL for every `k' ≥ k`. -/
protected theorem IsLeftInputStrictlyLocal.mono (hf : IsLeftInputStrictlyLocal k f)
    (hk : k ≤ k') : IsLeftInputStrictlyLocal k' f := fun _ _ h ↦
  hf <| Edge.right.takeAt_eq_of_le (Nat.sub_le_sub_right hk 1) h

protected theorem IsRightInputStrictlyLocal.mono (hf : IsRightInputStrictlyLocal k f)
    (hk : k ≤ k') : IsRightInputStrictlyLocal k' f :=
  IsLeftInputStrictlyLocal.mono hf hk

theorem ISLRule.apply_eq_flatMap (r : ISLRule 1 α β) :
    r.apply = List.flatMap (r.windowOutput []) := by
  funext u
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih => simp [ISLRule.apply_append_singleton, ih]

/-- The `1`-ISL functions are the letterwise homomorphisms `List.flatMap h` between an initial
and a final output. -/
theorem isLeftInputStrictlyLocal_one_iff :
    IsLeftInputStrictlyLocal 1 f ↔
      ∃ (p : List β) (h : α → List β) (t : List β), ∀ u, f u = p ++ u.flatMap h ++ t := by
  rw [isLeftInputStrictlyLocal_iff_exists_rule]
  refine ⟨fun ⟨p, r, t, h⟩ ↦ ⟨p, r.windowOutput [], t [], fun u ↦ ?_⟩,
    fun ⟨p, h, t, hf⟩ ↦ ⟨p, ⟨fun _ ↦ h⟩, fun _ ↦ t, fun u ↦ ?_⟩⟩
  · rw [h, r.apply_eq_flatMap, List.rtake_zero]
  · rw [hf, ISLRule.apply_eq_flatMap]

/-- Appending a fixed block at the end of the word is `1`-ISL, though no rule computes it. -/
example (t : List α) : IsLeftInputStrictlyLocal 1 (· ++ t) :=
  isLeftInputStrictlyLocal_one_iff.mpr ⟨[], fun x ↦ [x], t, fun u ↦ by simp⟩

/-! ### ISL ⊆ Subsequential -/

/-- Over a finite input alphabet, left-ISL functions are left-subsequential. -/
theorem IsLeftInputStrictlyLocal.isLeftSubsequential [Finite α]
    (hf : IsLeftInputStrictlyLocal k f) : IsLeftSubsequential f :=
  .of_factorsThrough_residual hf <| (List.finite_length_le α (k - 1)).subset <|
    Set.range_subset_iff.mpr fun _ ↦ List.length_rtake_le _ _

theorem ISLRule.isMealyComputable_apply [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  isMealyComputable_windowRun _ _ _ hs

theorem IsRightInputStrictlyLocal.isRightSubsequential [Finite α]
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
