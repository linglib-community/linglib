/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OCP
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# Forbidden-factor constraints

This file defines the [forbidden-factor constraint](##ofForbiddenFactors) of a set `F` of strings,
which assigns a word one violation for each width-`k` window of its boundary-padded form lying in
`F`. A word satisfies it [exactly when it belongs to the strictly `k`-local language forbidding
`F`](##ofForbiddenFactors_eq_zero_iff), and likewise
[on a tier](##comap_filter_ofForbiddenFactors_eq_zero_iff).

We also define the [forbidden-pair constraint](##ofForbiddenPairs) of a relation `R`, the case of
width two forbidding the adjacent pairs `(a, b)` with `R a b`, which a string satisfies
[exactly when it is a chain of `¬ R`](##ofForbiddenPairs_eq_zero_iff), and the
[Obligatory Contour Principle](##ocp), its instance for equality. The principle is Leben's, named
by Goldsmith and stated for any melody by McCarthy. Since it bans $XX$ for a variable $X$, as
Berent argues identity restrictions do,
[no injective relabelling changes its violations](##ocp_map_of_injective).

## Implementation notes

The recursion of `ofForbiddenPairs` on adjacent pairs is proved from
[that of `ofForbiddenFactors`](##ofForbiddenFactors_cons), which holds when no forbidden factor
begins at the left edge. OCP-Feature constraints are `ocp` pulled back along a feature projection,
which [`ofForbiddenPairs_map`](##ofForbiddenPairs_map) rewrites.

## TODO

State Lamont's count, a sum over loci each matched at its own length, as a sum of
forbidden-factor constraints when a study needs loci of several lengths.

## References

* [W. R. Leben, *Suprasegmental Phonology* (1973)][leben-1973]
* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [A. Lamont, *Directional Harmonic Serialism* (2022)][lamont-2022b]
* [I. Berent, *Three arguments for abstraction in phonology* (2026)][berent-2026]
-/

@[expose] public section

namespace OptimalityTheory.Constraint

open Subregular

variable {α β : Type*}

/-! ### The forbidden-factor count -/

/-- The forbidden-factor constraint of width `k`, with one violation for each width-`k` window of
the boundary-padded word that lies in `F`. -/
def ofForbiddenFactors (k : ℕ) (F : Set (Augmented α)) [DecidablePred (· ∈ F)] :
    Constraint (List α) :=
  fun w ↦ (windows k w).countP (· ∈ F)

section ofForbiddenFactors

variable {k : ℕ} {F : Set (Augmented α)} [DecidablePred (· ∈ F)]

/-- A word satisfies the forbidden-factor constraint iff it belongs to the strictly `k`-local
language of the grammar forbidding `F`. -/
theorem ofForbiddenFactors_eq_zero_iff (hk : 1 ≤ k) {w : List α} :
    ofForbiddenFactors k F w = 0 ↔ w ∈ (StrictlyLocalGrammar.ofForbidden F).language k := by
  rw [ofForbiddenFactors, List.countP_eq_zero, StrictlyLocalGrammar.mem_ofForbidden_language]
  simp only [decide_eq_true_eq]
  exact ⟨fun h f hlen hinf ↦ h f ((mem_windows_iff hk).2 ⟨hinf, hlen⟩),
    fun h f hf ↦ h f ((mem_windows_iff hk).1 hf).2 ((mem_windows_iff hk).1 hf).1⟩

/-- A word satisfies the forbidden-factor constraint on the tier `p` iff it belongs to the
tier-based strictly `k`-local language forbidding `F` on that tier. -/
theorem comap_filter_ofForbiddenFactors_eq_zero_iff (hk : 1 ≤ k) (p : α → Prop) [DecidablePred p]
    {w : List α} : (ofForbiddenFactors k F).comap (List.filter (p ·)) w = 0 ↔
      w ∈ (⟨p, .ofForbidden F⟩ : TierStrictlyLocalGrammar α).language k := by
  rw [comap_apply, TierStrictlyLocalGrammar.mem_language]
  exact ofForbiddenFactors_eq_zero_iff hk

private lemma ofForbiddenFactors_eq_countP (hk : 1 ≤ k) (hF : ∀ t, none :: t ∉ F) (w : List α) :
    ofForbiddenFactors k F w =
      ((List.range w.length).map fun j : ℕ ↦ window k w j).countP (· ∈ F) := by
  rw [ofForbiddenFactors, windows_eq_append hk, List.countP_append, List.countP_eq_zero.2,
    zero_add]
  simp only [List.mem_map, List.mem_range, decide_eq_true_eq]
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [window_succ_of_neg (by omega)]
  exact hF _

theorem ofForbiddenFactors_nil (hk : 1 ≤ k) (hF : ∀ t, none :: t ∉ F) :
    ofForbiddenFactors k F ([] : List α) = 0 := by
  rw [ofForbiddenFactors_eq_countP hk hF]
  rfl

/-- When no forbidden factor begins at the left edge, a word has the violations of its tail and
one more if the window at its first symbol is forbidden. -/
theorem ofForbiddenFactors_cons (hk : 1 ≤ k) (hF : ∀ t, none :: t ∉ F) (a : α) (w : List α) :
    ofForbiddenFactors k F (a :: w) =
      (if window k (a :: w) 0 ∈ F then 1 else 0) + ofForbiddenFactors k F w := by
  rw [ofForbiddenFactors_eq_countP hk hF, ofForbiddenFactors_eq_countP hk hF, List.length_cons,
    List.range_succ_eq_map, List.map_cons, List.countP_cons, List.map_map, add_comm]
  simp only [Nat.cast_zero, decide_eq_true_eq]
  congr 2
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Function.comp_apply, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  exact window_cons_add_one a (by omega)

end ofForbiddenFactors

/-! ### Forbidden pairs -/

/-- The forbidden-pair constraint on strings, the forbidden-factor constraint of width two with one
violation for each adjacent pair `(a, b)` satisfying `R a b`. -/
def ofForbiddenPairs (R : α → α → Prop) [DecidableRel R] : Constraint (List α) :=
  ofForbiddenFactors 2 (forbiddenPairs R)

/-- The Obligatory Contour Principle, the forbidden-pair constraint against adjacent identical
elements ((2) of [mccarthy-1986]). -/
def ocp [DecidableEq α] : Constraint (List α) := ofForbiddenPairs (· = ·)

section ofForbiddenPairs

private lemma none_cons_notMem_forbiddenPairs (R : α → α → Prop) (t : Augmented α) :
    none :: t ∉ forbiddenPairs R := by
  simp [forbiddenPairs]

variable (R : α → α → Prop) [DecidableRel R]

@[simp] theorem ofForbiddenPairs_nil : ofForbiddenPairs R [] = 0 :=
  ofForbiddenFactors_nil (by decide) (none_cons_notMem_forbiddenPairs R)

@[simp] theorem ofForbiddenPairs_singleton (a : α) : ofForbiddenPairs R [a] = 0 := by
  rw [ofForbiddenPairs, ofForbiddenFactors_cons (by decide) (none_cons_notMem_forbiddenPairs R),
    ofForbiddenFactors_nil (by decide) (none_cons_notMem_forbiddenPairs R),
    window_succ_cons_zero (k := 1)]
  simp [forbiddenPairs]

@[simp] theorem ofForbiddenPairs_cons_cons (a b : α) (w : List α) :
    ofForbiddenPairs R (a :: b :: w) = (if R a b then 1 else 0) + ofForbiddenPairs R (b :: w) := by
  rw [ofForbiddenPairs, ofForbiddenFactors_cons (by decide) (none_cons_notMem_forbiddenPairs R),
    window_succ_cons_zero (k := 1), window_succ_cons_zero (k := 0), window_zero]
  simp [forbiddenPairs]

/-- A string satisfies the forbidden-pair constraint iff no two adjacent elements are
`R`-related. -/
theorem ofForbiddenPairs_eq_zero_iff {R : α → α → Prop} [DecidableRel R] {w : List α} :
    ofForbiddenPairs R w = 0 ↔ w.IsChain (fun a b ↦ ¬ R a b) := by
  induction w using List.twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b w _ ih => by_cases hab : R a b <;> simp [hab, ih]

/-- The violations split at any element, as `List.isChain_split` splits a chain. -/
theorem ofForbiddenPairs_split (l₁ : List α) (c : α) (l₂ : List α) :
    ofForbiddenPairs R (l₁ ++ c :: l₂) =
      ofForbiddenPairs R (l₁ ++ [c]) + ofForbiddenPairs R (c :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a t ih => cases t with
    | nil => simp
    | cons b t => simp only [List.cons_append, ofForbiddenPairs_cons_cons] at ih ⊢; omega

theorem ofForbiddenPairs_append_cons_cons (l₁ : List α) (b c : α) (l₂ : List α) :
    ofForbiddenPairs R (l₁ ++ b :: c :: l₂) =
      ofForbiddenPairs R (l₁ ++ [b]) + (if R b c then 1 else 0) + ofForbiddenPairs R (c :: l₂) := by
  rw [ofForbiddenPairs_split, ofForbiddenPairs_cons_cons, Nat.add_assoc]

/-- Mapping the elements of a string by `f` pulls the forbidden relation back along `f`, as in
`List.isChain_map`. -/
theorem ofForbiddenPairs_map (f : β → α) (w : List β) :
    ofForbiddenPairs R (w.map f) = ofForbiddenPairs (fun a b ↦ R (f a) (f b)) w := by
  induction w using List.twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b w _ ih => simp only [List.map_cons, ofForbiddenPairs_cons_cons] at ih ⊢; rw [ih]

/-- Two first elements related alike give a string the same violations. -/
theorem ofForbiddenPairs_congr_head {a b : α} (h : ∀ x, R a x ↔ R b x) (w : List α) :
    ofForbiddenPairs R (a :: w) = ofForbiddenPairs R (b :: w) := by
  cases w <;> simp [h]

/-- Two last elements related alike give a string the same violations. -/
theorem ofForbiddenPairs_congr_last {a b : α} (h : ∀ x, R x a ↔ R x b) (w : List α) :
    ofForbiddenPairs R (w ++ [a]) = ofForbiddenPairs R (w ++ [b]) := by
  induction w with
  | nil => simp
  | cons c t ih => cases t with
    | nil => simp [h]
    | cons d t => simpa using ih

end ofForbiddenPairs

section ocp

variable [DecidableEq α]

@[simp] theorem ocp_nil : ocp ([] : List α) = 0 := ofForbiddenPairs_nil _

@[simp] theorem ocp_singleton (a : α) : ocp [a] = 0 := ofForbiddenPairs_singleton _ a

@[simp] theorem ocp_cons_cons (a b : α) (w : List α) :
    ocp (a :: b :: w) = (if a = b then 1 else 0) + ocp (b :: w) :=
  ofForbiddenPairs_cons_cons _ a b w

/-- A string satisfies the OCP iff no two adjacent elements are identical. -/
theorem ocp_eq_zero_iff {w : List α} : ocp w = 0 ↔ OCP.IsClean w :=
  ofForbiddenPairs_eq_zero_iff

/-- An injective relabelling of the elements preserves the OCP's violations, as
`List.map_destutter_ne` preserves the fusion of identical neighbours. -/
theorem ocp_map_of_injective [DecidableEq β] {f : β → α} (hf : Function.Injective f)
    (w : List β) : ocp (w.map f) = ocp w := by
  simp only [ocp, ofForbiddenPairs_map, hf.eq_iff]

end ocp

end OptimalityTheory.Constraint
