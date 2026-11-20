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

The classes nest in `k` (`IsLeftOutputStrictlyLocal.mono`), agree with the input strictly local
functions at `k = 1` (`isLeftOutputStrictlyLocal_one_iff`), and are subsequential over a finite
output alphabet (`IsLeftOutputStrictlyLocal.isLeftSubsequential`). The two families are otherwise
incomparable: dissimilation after an input symbol is ISL and not OSL
(`ISLRule.dissimilate_not_isLeftOutputStrictlyLocal`), progressive spreading is OSL and not ISL
(`OSLRule.spread_not_isLeftInputStrictlyLocal`) and, read right to left, not OSL either
(`OSLRule.spread_not_isRightOutputStrictlyLocal`), and long-distance assimilation across
transparent symbols is Mealy-computable and neither
(`longDistanceAgree_not_isLeftInputStrictlyLocal`,
`longDistanceAgree_not_isLeftOutputStrictlyLocal`).

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

/-- The `1`-OSL functions are the `1`-ISL functions, both being the functions with a single
residual. -/
theorem isLeftOutputStrictlyLocal_one_iff :
    IsLeftOutputStrictlyLocal 1 f ↔ IsLeftInputStrictlyLocal 1 f := by
  simp [IsLeftOutputStrictlyLocal, IsLeftInputStrictlyLocal, Function.FactorsThrough]

/-! ### OSL ⊆ Subsequential -/

/-- Over a finite output alphabet, left-OSL functions are left-subsequential. -/
theorem IsLeftOutputStrictlyLocal.isLeftSubsequential [Finite β]
    (hf : IsLeftOutputStrictlyLocal k f) : IsLeftSubsequential f :=
  .of_finite_range_residual <| ((List.finite_length_le β (k - 1)).image
    (Function.extend (fun u ↦ (f.prefixFunction u).rtake (k - 1)) f.residual
      fun _ _ ↦ [])).subset <|
        Set.range_subset_iff.mpr fun u ↦ ⟨_, List.length_rtake_le _ _, hf.extend_apply _ u⟩

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

/-! ### ISL and OSL are incomparable

Chandlee, Eyraud and Heinz separate the two classes and place a subsequential function outside
both. Each separation is one pair of inputs with the same window and different residuals. -/

private theorem rtake_cons_replicate (n : ℕ) (x y : α) :
    (x :: List.replicate n y).rtake n = List.replicate n y :=
  List.rtake_cons_of_length_eq (by simp)

/-- The prefix function vanishes where two continuations begin with different symbols. -/
private theorem prefixFunction_eq_nil {f : List α → List β} {u v w : List α} {x y : β}
    {s t : List β} (hxy : x ≠ y) (hv : f (u ++ v) = x :: s) (hw : f (u ++ w) = y :: t) :
    f.prefixFunction u = [] := by
  rcases h : f.prefixFunction u with _ | ⟨z, p⟩
  · rfl
  · have h₁ := h ▸ prefixFunction_prefix (f := f) u v
    have h₂ := h ▸ prefixFunction_prefix (f := f) u w
    rw [hv, List.cons_prefix_cons] at h₁
    rw [hw, List.cons_prefix_cons] at h₂
    exact absurd (h₁.1.symm.trans h₂.1) hxy

section Incomparable

variable [DecidableEq α] {a b c : α}

/-- Dissimilation of `a` to `b` after an input `a` (the function `f₂` of
[chandlee-eyraud-heinz-2014], Theorem 5). -/
def ISLRule.dissimilate (a b : α) : ISLRule 2 α α where
  windowOutput w x := if w = [a] ∧ x = a then [b] else [x]

/-- Dissimilation is not OSL, since `aa` and `ab` have the same output `ab`
but continue differently on `a`. -/
theorem ISLRule.dissimilate_not_isLeftOutputStrictlyLocal (hab : a ≠ b) (k : ℕ) :
    ¬ IsLeftOutputStrictlyLocal k (dissimilate a b).apply := fun h ↦ by
  have hpre := (dissimilate a b).isPrefix_apply
  have e := congrFun (h (a := [a, a]) (b := [a, b]) (by
    simp only [prefixFunction_eq_self (hpre [a, a]), prefixFunction_eq_self (hpre [a, b])]
    simp [ISLRule.apply, ISLRule.applyAux, windowRun, dissimilate, List.rtake, hab.symm])) [a]
  rw [residual_eq_drop (hpre _), residual_eq_drop (hpre _)] at e
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
    have : List.replicate (min 1 n) b ≠ [a] := fun h ↦ hab <|
      List.eq_of_mem_replicate (h ▸ List.mem_singleton_self a)
    simp [OSLRule.spread, this]

/-- Spreading is not ISL, since `a bᵏ⁻¹` and `bᵏ` end in the same `k - 1`
input symbols while a further `b` surfaces as `a` after the first and as `b` after the second. -/
theorem OSLRule.spread_not_isLeftInputStrictlyLocal (hab : a ≠ b) (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k (spread a).apply := fun h ↦ by
  have hpre := (spread a).isPrefix_apply
  have e := congrFun (h (a := a :: List.replicate (k - 1) b)
    (b := b :: List.replicate (k - 1) b) (by simp only [rtake_cons_replicate])) [b]
  rw [residual_eq_drop (hpre _), residual_eq_drop (hpre _)] at e
  simp only [List.cons_append, ← List.replicate_succ', spread_apply_cons_replicate,
    ← List.replicate_succ, spread_apply_replicate hab, List.length_replicate,
    List.drop_replicate, Nat.add_sub_cancel_left] at e
  exact hab (List.singleton_inj.mp e)

/-- Spreading is not right-OSL: read right to left, nothing is determined before an `a`, so the
prefix functions at `b` and `bb` are both empty, while the residuals there differ on the empty
continuation. -/
theorem OSLRule.spread_not_isRightOutputStrictlyLocal (hab : a ≠ b) (k : ℕ) :
    ¬ IsRightOutputStrictlyLocal k (spread a).apply := fun h ↦ by
  have h₁ : (List.revConj (spread a).apply).prefixFunction [b] = [] :=
    prefixFunction_eq_nil (v := []) (w := [a]) (s := []) (t := [a]) hab.symm
      (by simp [List.revConj, OSLRule.apply, OSLRule.applyAux, windowRun, spread])
      (by simp [List.revConj, OSLRule.apply, OSLRule.applyAux, windowRun, spread, List.rtake])
  have h₂ : (List.revConj (spread a).apply).prefixFunction [b, b] = [] :=
    prefixFunction_eq_nil (v := []) (w := [a]) (s := [b]) (t := [a, a]) hab.symm
      (by simp [List.revConj, OSLRule.apply, OSLRule.applyAux, windowRun, spread, List.rtake,
        hab.symm])
      (by simp [List.revConj, OSLRule.apply, OSLRule.applyAux, windowRun, spread, List.rtake])
  have e := congrFun (h (a := [b]) (b := [b, b]) (by simp only [h₁, h₂])) []
  have r₁ := prefixFunction_append_residual (f := List.revConj (spread a).apply) [b] []
  have r₂ := prefixFunction_append_residual (f := List.revConj (spread a).apply) [b, b] []
  rw [h₁, List.nil_append, e] at r₁
  rw [h₂, List.nil_append, r₁] at r₂
  simp [List.revConj, OSLRule.apply, OSLRule.applyAux, windowRun, spread, List.rtake,
    hab.symm] at r₂

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

/-- Long-distance assimilation is not ISL, since `acᵏ⁻¹` and `bcᵏ⁻¹` end
alike while a further `b` surfaces as `a` only after the first. -/
theorem longDistanceAgree_not_isLeftInputStrictlyLocal (hab : a ≠ b) (hca : c ≠ a) (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k (longDistanceAgree a b).run := fun h ↦ by
  have e := congrFun (h (a := a :: List.replicate (k - 1) c)
    (b := b :: List.replicate (k - 1) c) (by simp only [rtake_cons_replicate])) [b]
  simp [Mealy.residual_run, longDistanceAgree, List.any_replicate, hca, hab.symm] at e
  exact hab e

/-- Long-distance assimilation is not OSL, since `acᵏ⁻¹` and `bcᵏ⁻¹` are
output unchanged and end alike while a further `b` surfaces as `a` only after the first. -/
theorem longDistanceAgree_not_isLeftOutputStrictlyLocal (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) (k : ℕ) : ¬ IsLeftOutputStrictlyLocal k (longDistanceAgree a b).run := fun h ↦ by
  have hpre (u v : List α) :
      (longDistanceAgree a b).run u <+: (longDistanceAgree a b).run (u ++ v) :=
    ⟨_, ((longDistanceAgree a b).runFrom_append _ u v).symm⟩
  have e := congrFun (h (a := a :: List.replicate (k - 1) c)
    (b := b :: List.replicate (k - 1) c) (by
      simp only [prefixFunction_eq_self (hpre (a :: List.replicate (k - 1) c)),
        prefixFunction_eq_self (hpre (b :: List.replicate (k - 1) c)),
        longDistanceAgree_run_cons_replicate hcb, rtake_cons_replicate])) [b]
  simp [Mealy.residual_run, longDistanceAgree, List.any_replicate, hca, hab.symm] at e
  exact hab e

end Incomparable

end Subregular
