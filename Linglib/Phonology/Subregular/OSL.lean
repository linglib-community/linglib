/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.ISL

/-!
# Output strictly local functions

A function `f : List α → List β` is *`k`-output strictly local* (`k`-OSL) when its residuals
factor through the last `k - 1` symbols of its prefix function `f.prefixFunction`, the output
already determined by the input read so far. This is the tail condition by which Chandlee, Eyraud
and Heinz define the class. Progressive spreading is the motivating case, since its trigger is
adjacent in the output however far back it lies in the input.

An `OSLRule k α β` emits, for each input symbol, a block computed from that symbol and the last
`k - 1` symbols emitted, and `OSLRule.apply` is the function it computes. A rule writes nothing
before the first symbol and nothing at the end of the word. A function is `k`-OSL exactly when a
rule computes its prefix function from the initial output `f.prefixFunction []` and the function
appends a final output read off the window (`isLeftOutputStrictlyLocal_iff_exists_rule`), and the
functions of the rules themselves are the `k`-OSL functions that fix `[]` and preserve prefixes
(`exists_oslRule_apply_eq_iff`).

The classes nest in `k` (`IsLeftOutputStrictlyLocal.mono`) and are subsequential over a finite
output alphabet (`IsLeftOutputStrictlyLocal.isLeftSubsequential`). They are compared with the
input strictly local functions in `Linglib.Phonology.Subregular.StrictlyLocalSeparation`.

`OSLRule.applyOnTier` runs a rule with its window over the tier projection of its output, after
Burness and McMullin.

## Implementation notes

The definition is the tail condition alone. It does not ask that `f` be subsequential, which
follows over a finite output alphabet since the windows are then finitely many.

The rule of `isLeftOutputStrictlyLocal_iff_exists_rule` computes the prefix function, not some
other function that `f` extends by a final output. This is the onwardness of Chandlee, Eyraud and
Heinz's transducers, and it is what makes the window of the rule the window of the definition.

`0`-OSL and `1`-OSL coincide.

## TODO

* The output tier-based class as a predicate, with residuals factoring through the last `k - 1`
  on-tier symbols of the prefix function, characterized by `OSLRule.applyOnTier`.

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

open Function

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

theorem applyAux_append_singleton {w : List β} (hw : w.length ≤ k - 1) (u : List α) (x : α) :
    r.applyAux w (u ++ [x])
      = r.applyAux w u ++ r.windowOutput ((w ++ r.applyAux w u).rtake (k - 1)) x :=
  windowRun_append_singleton hw u x

theorem apply_append_singleton (u : List α) (x : α) :
    r.apply (u ++ [x]) = r.apply u ++ r.windowOutput ((r.apply u).rtake (k - 1)) x :=
  r.applyAux_append_singleton (Nat.zero_le _) u x

theorem isPrefix_apply (u v : List α) : r.apply u <+: r.apply (u ++ v) :=
  isPrefix_append_of_append_singleton (fun u x ↦ ⟨_, (r.apply_append_singleton u x).symm⟩) u v

@[simp] theorem prefixFunction_apply (u : List α) : r.apply.prefixFunction u = r.apply u :=
  prefixFunction_eq_self (r.isPrefix_apply u)

end OSLRule

/-- `f` is **`k`-left-output strictly local** if its residuals factor through the last `k - 1`
symbols of its prefix function ([chandlee-eyraud-heinz-2015], Definition 6). -/
def IsLeftOutputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  f.residual.FactorsThrough fun u ↦ (f.prefixFunction u).rtake (k - 1)

/-- `f` is **`k`-right-output strictly local** if its reverse-conjugate is `k`-left-OSL. -/
def IsRightOutputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  IsLeftOutputStrictlyLocal k (List.revConj f)

/-! ### Rules -/

theorem OSLRule.isLeftOutputStrictlyLocal_apply (r : OSLRule k α β) :
    IsLeftOutputStrictlyLocal k r.apply := by
  simp only [IsLeftOutputStrictlyLocal, r.prefixFunction_apply]
  refine factorsThrough_residual_of_append_singleton
    (fun w x ↦ (w ++ r.windowOutput w x).rtake (k - 1)) r.windowOutput (fun u x ↦ ?_)
    r.apply_append_singleton
  rw [r.apply_append_singleton, List.rtake_rtake_append]

/-- A function is `k`-OSL if and only if a rule computes its prefix function from the initial
output, and the function appends to its prefix function a final output read off the window
([chandlee-eyraud-heinz-2015], Theorem 3 and Lemma 4). -/
theorem isLeftOutputStrictlyLocal_iff_exists_rule :
    IsLeftOutputStrictlyLocal k f ↔ ∃ (r : OSLRule k α β) (t : List β → List β), ∀ u,
      f.prefixFunction u
        = f.prefixFunction [] ++ r.applyAux ((f.prefixFunction []).rtake (k - 1)) u ∧
      f u = f.prefixFunction u ++ t ((f.prefixFunction u).rtake (k - 1)) := by
  refine ⟨fun hf ↦ ?_, fun ⟨r, t, h⟩ ↦ ?_⟩
  · obtain ⟨g, t, hg, ht⟩ := exists_prefixFunction_append_singleton_of_factorsThrough_residual hf
    refine ⟨⟨g⟩, t, fun u ↦ ⟨?_, ht u⟩⟩
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u x ih =>
      rw [OSLRule.applyAux_append_singleton _ (List.length_rtake_le _ _), hg,
        List.rtake_rtake_append, ← List.append_assoc, ← ih]
  · have hP (u : List α) (x : α) : f.prefixFunction (u ++ [x]) =
        f.prefixFunction u ++ r.windowOutput ((f.prefixFunction u).rtake (k - 1)) x := by
      rw [(h (u ++ [x])).1, r.applyAux_append_singleton (List.length_rtake_le _ _),
        List.rtake_rtake_append, ← List.append_assoc, ← (h u).1]
    exact factorsThrough_residual_of_append_final
      (fun w x ↦ (w ++ r.windowOutput w x).rtake (k - 1)) r.windowOutput t
      (fun u x ↦ by rw [hP, List.rtake_rtake_append]) hP fun u ↦ (h u).2

/-- The functions computed by `k`-OSL rules are the `k`-OSL functions that fix `[]` and
preserve prefixes. -/
theorem exists_oslRule_apply_eq_iff :
    (∃ r : OSLRule k α β, r.apply = f) ↔
      f [] = [] ∧ (∀ u v, f u <+: f (u ++ v)) ∧ IsLeftOutputStrictlyLocal k f := by
  refine ⟨?_, fun ⟨h₀, hpre, hf⟩ ↦ ?_⟩
  · rintro ⟨r, rfl⟩
    exact ⟨rfl, r.isPrefix_apply, r.isLeftOutputStrictlyLocal_apply⟩
  · simp only [IsLeftOutputStrictlyLocal, prefixFunction_eq_self (hpre _)] at hf
    obtain ⟨g, hg⟩ := exists_append_singleton_of_factorsThrough_residual hpre hf
    refine ⟨⟨g⟩, funext fun u ↦ ?_⟩
    induction u using List.reverseRecOn with
    | nil => exact h₀.symm
    | append_singleton u x ih => rw [OSLRule.apply_append_singleton, hg, ih]

/-! ### The hierarchy in `k` -/

/-- A `k`-OSL function is `k'`-OSL for every `k' ≥ k`. -/
protected theorem IsLeftOutputStrictlyLocal.mono (hf : IsLeftOutputStrictlyLocal k f)
    (hk : k ≤ k') : IsLeftOutputStrictlyLocal k' f := fun _ _ h ↦
  hf <| Edge.right.takeAt_eq_of_le (Nat.sub_le_sub_right hk 1) h

protected theorem IsRightOutputStrictlyLocal.mono (hf : IsRightOutputStrictlyLocal k f)
    (hk : k ≤ k') : IsRightOutputStrictlyLocal k' f :=
  IsLeftOutputStrictlyLocal.mono hf hk

/-! ### OSL ⊆ Subsequential -/

/-- Over a finite output alphabet, left-OSL functions are left-subsequential. -/
theorem IsLeftOutputStrictlyLocal.isLeftSubsequential [Finite β]
    (hf : IsLeftOutputStrictlyLocal k f) : IsLeftSubsequential f :=
  .of_factorsThrough_residual hf <| (List.finite_length_le β (k - 1)).subset <|
    Set.range_subset_iff.mpr fun _ ↦ List.length_rtake_le _ _

theorem OSLRule.isMealyComputable_apply [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  isMealyComputable_windowRun _ _ _ hs

theorem IsRightOutputStrictlyLocal.isRightSubsequential [Finite β]
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

end Subregular
