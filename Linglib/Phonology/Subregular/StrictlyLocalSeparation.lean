/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Mealy.MyhillNerode
public import Linglib.Phonology.Subregular.OSL

/-!
# Separating the input and output strictly local functions

The input and the output strictly local functions agree at `k = 1`
(`isLeftOutputStrictlyLocal_one_iff`) and are otherwise incomparable. Chandlee, Eyraud and Heinz
separate them by three functions, each refuted by one pair of inputs with the same window and
different residuals:

* dissimilation of `a` after an input `a` is `2`-ISL and not OSL
  (`ISLRule.dissimilate_not_isLeftOutputStrictlyLocal`);
* progressive spreading of `a` is `2`-OSL and not ISL
  (`OSLRule.spread_not_isLeftInputStrictlyLocal`), and read right to left it is not OSL either
  (`OSLRule.spread_not_isRightOutputStrictlyLocal`);
* long-distance assimilation across transparent symbols is Mealy-computable and neither
  (`longDistanceAgree_not_isLeftInputStrictlyLocal`,
  `longDistanceAgree_not_isLeftOutputStrictlyLocal`).

## References

* [J. Chandlee, R. Eyraud and J. Heinz, *Learning Strictly Local Subsequential Functions*
  (2014)][chandlee-eyraud-heinz-2014]
* [J. Chandlee, R. Eyraud and J. Heinz, *Output Strictly Local Functions*
  (2015)][chandlee-eyraud-heinz-2015]
-/

@[expose] public section

namespace Subregular

open Function

variable {α β : Type*} {f : List α → List β}

/-- The `1`-OSL functions are the `1`-ISL functions, both being the functions with a single
residual. -/
theorem isLeftOutputStrictlyLocal_one_iff :
    IsLeftOutputStrictlyLocal 1 f ↔ IsLeftInputStrictlyLocal 1 f := by
  simp [IsLeftOutputStrictlyLocal, IsLeftInputStrictlyLocal, Function.FactorsThrough]

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
