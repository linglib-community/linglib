/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.WindowFormula
public import Linglib.Core.Data.List.TakeDrop
public import Mathlib.Data.Fintype.Prod

/-!
# Boolean monadic recursive schemes

A **boolean monadic recursive scheme** (BMRS) is a program of mutually recursive boolean-valued
unary predicates over words, built from `if…then…else`, the edge tests `min` and `max`, input
class tests, and calls of the program's rule heads. Its one-sided fragments characterize the
left- and right-subsequential functions, a characterization later extended to the rational
functions and applied to phonological analysis.

Input labels `α` get the lookup rule and rule heads `F` the unfolding rule, so a `Program` is a
total map `F → Expr α F`. `Eval` is the derivation system `w, i ⊢_P e → b`. It is partial: a
program that does not halt derives nothing. `Program.approx` computes it in rounds, each rerunning
every rule body against the values the previous rounds found, and on a word of length `n` the
rounds settle by round `card F * n`, so evaluation is decidable.

## Main definitions

* `BMRS.Expr`, `BMRS.Program`: syntax.
* `BMRS.Eval`: the derivation system.
* `Program.approx`, `Program.eval`: the rounds of evaluation and the value they settle on.
* `Program.Backward` / `Program.Forward`: the one-sided fragments `BMRSᵖ` and `BMRSˢ`, in which
  the successor (dually, the predecessor) occurs in no rule.

## Main statements

* `Program.eval_eq_some_iff`: the rounds settle on the derivation system, so `Eval` is decidable.
* `Eval.congr_take` / `Eval.congr_drop`: one-sided locality: a backward program evaluated at `i`
  reads only the prefix through `i` (dually, the suffix from `i`).

## Implementation notes

* `Eval` is the derivation system of Yolyan and Comer (2026, Figs. 6–7), in which a term
  stepping off the word denotes nothing and an expression reading it is undefined. Bhaskar,
  Chandlee and Jardine (2023) instead let successor and predecessor fix the last and first
  positions, and Yolyan (2025) evaluates a predicate of an undefined term as false. Programs
  that test `min`/`max` before stepping past an edge evaluate alike under all three.
* The rounds are those of Yolyan and Comer (Fig. 4) and Yolyan (3.14). A head gets a value at a
  position once its body evaluates against the values already found.

## References

* [bhaskar-jardine-chandlee-oakden-2020]
* [bhaskar-chandlee-jardine-2023]
* [chandlee-jardine-2021]
* [yolyan-2025]
* [yolyan-comer-2026]
-/

@[expose] public section

namespace Subregular.BMRS

open Set (EqOn Iic Ici)

variable {α F : Type*}

/-! ### Syntax -/

/-- A BMRS expression is an edge test `initial` or `final` (the literature's `min(T)`,
`max(T)`), an input class test `label` (the lookup rule, over a `Finset` of symbols, so that
featural predicates like V or N are single atoms), a rule-head call `call` (the unfolding rule),
or an `if…then…else`. -/
inductive Expr (α F : Type*) where
  | tru
  | fls
  | initial (t : Walk)
  | final (t : Walk)
  | label (s : Finset α) (t : Walk)
  | call (f : F) (t : Walk)
  | ite (c e₁ e₂ : Expr α F)
  deriving DecidableEq

/-- A BMRS program assigns one defining expression to each rule head. -/
abbrev Program (α F : Type*) := F → Expr α F

namespace Expr

/-- Conjunction as `if…then…else`. -/
def and (e₁ e₂ : Expr α F) : Expr α F := .ite e₁ e₂ .fls

/-- Disjunction as `if…then…else`. -/
def or (e₁ e₂ : Expr α F) : Expr α F := .ite e₁ .tru e₂

/-- Negation as `if…then…else`. -/
def not (e : Expr α F) : Expr α F := .ite e .fls .tru

/-- `e.subst u` substitutes the term `u` for the variable throughout `e`, the `e[u/x]` that the
μ-calculus translation writes `tr(φ)[s(x)]`. -/
def subst : Expr α F → Walk → Expr α F
  | .tru, _ => .tru
  | .fls, _ => .fls
  | .initial t, u => .initial (t.comp u)
  | .final t, u => .final (t.comp u)
  | .label s t, u => .label s (t.comp u)
  | .call f t, u => .call f (t.comp u)
  | .ite c e₁ e₂, u => .ite (c.subst u) (e₁.subst u) (e₂.subst u)

/-- `e.AllWalks p` holds when every walk occurring in `e` satisfies `p`. -/
def AllWalks (p : Walk → Prop) : Expr α F → Prop
  | .tru | .fls => True
  | .initial t | .final t | .label _ t | .call _ t => p t
  | .ite c e₁ e₂ => c.AllWalks p ∧ e₁.AllWalks p ∧ e₂.AllWalks p

instance instDecidableAllWalks (p : Walk → Prop) [DecidablePred p] :
    ∀ e : Expr α F, Decidable (e.AllWalks p)
  | .tru | .fls => .isTrue trivial
  | .initial t | .final t | .label _ t | .call _ t => inferInstanceAs (Decidable (p t))
  | .ite c e₁ e₂ =>
      @instDecidableAnd _ _ (instDecidableAllWalks p c)
        (@instDecidableAnd _ _ (instDecidableAllWalks p e₁) (instDecidableAllWalks p e₂))

end Expr

namespace Program

/-- A program is backward, `BMRSᵖ`, when the successor occurs in none of its rules. -/
def Backward (P : Program α F) : Prop := ∀ f, (P f).AllWalks Walk.Backward

/-- A program is forward, `BMRSˢ`, when the predecessor occurs in none of its rules. -/
def Forward (P : Program α F) : Prop := ∀ f, (P f).AllWalks Walk.Forward

instance [Fintype F] (P : Program α F) : Decidable P.Backward :=
  inferInstanceAs (Decidable (∀ f, (P f).AllWalks _))

instance [Fintype F] (P : Program α F) : Decidable P.Forward :=
  inferInstanceAs (Decidable (∀ f, (P f).AllWalks _))

end Program

/-! ### The derivation system -/

/-- `Eval P w i e b` is the derivation `w, i ⊢_P e → b` of a BMRS expression. It is partial by
design, a non-halting program deriving nothing. -/
inductive Eval (P : Program α F) (w : List α) : ℕ → Expr α F → Bool → Prop
  | tru {i} : Eval P w i .tru true
  | fls {i} : Eval P w i .fls false
  | initial_true {i t} (h : t.eval w i = some 0) : Eval P w i (.initial t) true
  | initial_false {i t v} (h : t.eval w i = some v) (hv : 0 < v) :
      Eval P w i (.initial t) false
  | final_true {i t} (h : t.eval w i = some (w.length - 1)) : Eval P w i (.final t) true
  | final_false {i t v} (h : t.eval w i = some v) (hv : v < w.length - 1) :
      Eval P w i (.final t) false
  | label_true {i s t v a} (h : t.eval w i = some v) (hl : w[v]? = some a) (has : a ∈ s) :
      Eval P w i (.label s t) true
  | label_false {i s t v a} (h : t.eval w i = some v) (hl : w[v]? = some a) (has : a ∉ s) :
      Eval P w i (.label s t) false
  | call {i f t v b} (h : t.eval w i = some v) (he : Eval P w v (P f) b) :
      Eval P w i (.call f t) b
  | ite_true {i c e₁ e₂ b} (hc : Eval P w i c true) (h₁ : Eval P w i e₁ b) :
      Eval P w i (.ite c e₁ e₂) b
  | ite_false {i c e₁ e₂ b} (hc : Eval P w i c false) (h₂ : Eval P w i e₂ b) :
      Eval P w i (.ite c e₁ e₂) b

variable {P : Program α F} {w w' : List α} {i v : ℕ} {t u : Walk}
  {e e₁ e₂ : Expr α F} {b b' b₁ b₂ : Bool}

/-- Boolean-form introduction for the initial test. -/
theorem Eval.initial (h : t.eval w i = some v) : Eval P w i (.initial t) (decide (v = 0)) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simpa using Eval.initial_true (P := P) h
  · simpa [hv.ne'] using Eval.initial_false (P := P) h hv

/-- Boolean-form introduction for the final test. -/
theorem Eval.final (h : t.eval w i = some v) :
    Eval P w i (.final t) (decide (v = w.length - 1)) := by
  rcases eq_or_ne v (w.length - 1) with rfl | hne
  · simpa using Eval.final_true (P := P) h
  · simpa [hne] using Eval.final_false (P := P) h (by have := Walk.eval_lt h; omega)

/-- Boolean-form introduction for the class test. -/
theorem Eval.label [DecidableEq α] {s : Finset α} {a : α} (h : t.eval w i = some v)
    (hl : w[v]? = some a) : Eval P w i (.label s t) (decide (a ∈ s)) := by
  by_cases has : a ∈ s
  · exact decide_eq_true has ▸ .label_true h hl has
  · exact decide_eq_false has ▸ .label_false h hl has

/-- Boolean-form introduction for conjunction. -/
theorem Eval.and (h₁ : Eval P w i e₁ b₁) (h₂ : Eval P w i e₂ b₂) :
    Eval P w i (e₁.and e₂) (b₁ && b₂) := by
  cases b₁
  exacts [.ite_false h₁ .fls, .ite_true h₁ h₂]

/-- Boolean-form introduction for disjunction. -/
theorem Eval.or (h₁ : Eval P w i e₁ b₁) (h₂ : Eval P w i e₂ b₂) :
    Eval P w i (e₁.or e₂) (b₁ || b₂) := by
  cases b₁
  exacts [.ite_false h₁ h₂, .ite_true h₁ .tru]

/-- Boolean-form introduction for negation. -/
theorem Eval.not (h : Eval P w i e b) : Eval P w i e.not (!b) := by
  cases b
  exacts [.ite_false h .tru, .ite_true h .fls]

/-- The derivation system is deterministic, giving an expression at most one value. -/
theorem Eval.deterministic (h : Eval P w i e b) (h' : Eval P w i e b') : b = b' := by
  induction h generalizing b' with
  | call h he ih => cases h' with
    | call h₂ he₂ => rw [h] at h₂; cases h₂; exact ih he₂
  | ite_true hc h₁ ihc ih₁ => cases h' with
    | ite_true hc₂ h₂ => exact ih₁ h₂
    | ite_false hc₂ h₂ => exact absurd (ihc hc₂) (by simp)
  | ite_false hc h₂ ihc ih₂ => cases h' with
    | ite_true hc₂ h₁ => exact absurd (ihc hc₂) (by simp)
    | ite_false hc₂ h₁ => exact ih₂ h₁
  | _ => cases h' <;> simp_all

/-- A program is **total on `w`** when every rule head is defined at every position. -/
def Program.TotalOn (P : Program α F) (w : List α) : Prop :=
  ∀ f, ∀ i < w.length, ∃ b, Eval P w i (.call f .var) b

/-! ### Substitution -/

/-- Walk reads sequence through composition. -/
private theorem eval_comp_of {z : ℕ} (hu : u.eval w i = some v) (h : t.eval w v = some z) :
    (t.comp u).eval w i = some z := by
  rw [Walk.eval_comp, hu]
  exact h

/-- Evaluating `e[u/x]` at `i` is evaluating `e` at the position `u` reads. -/
theorem Eval.subst (hu : u.eval w i = some v) (h : Eval P w v e b) :
    Eval P w i (e.subst u) b := by
  induction h with
  | tru => exact .tru
  | fls => exact .fls
  | initial_true h => exact .initial_true (eval_comp_of hu h)
  | initial_false h hv => exact .initial_false (eval_comp_of hu h) hv
  | final_true h => exact .final_true (eval_comp_of hu h)
  | final_false h hv => exact .final_false (eval_comp_of hu h) hv
  | label_true h hl has => exact .label_true (eval_comp_of hu h) hl has
  | label_false h hl has => exact .label_false (eval_comp_of hu h) hl has
  | call h he ih => exact .call (eval_comp_of hu h) he
  | ite_true hc h₁ ihc ih₁ => exact .ite_true (ihc hu) (ih₁ hu)
  | ite_false hc h₂ ihc ih₂ => exact .ite_false (ihc hu) (ih₂ hu)

/-! ### Locality

Evaluation reads only the positions its walks reach. Successor-free programs compute
left-subsequentially and predecessor-free programs right-subsequentially, and the one-sided
locality below is what those inclusions rest on. Equal length is load-bearing: walks and the
`max` test read `w.length`. -/

/-- **Locality.** If every walk of `P` and of `e` satisfies `p`, and a `p`-walk read from `j`
reaches only positions `r`-related to `j` for a transitive `r`, then equal-length words agreeing
on the positions `r`-related to `i` evaluate `e` at `i` alike. -/
theorem Eval.congr_of_allWalks {p : Walk → Prop} {r : ℕ → ℕ → Prop} [IsTrans ℕ r]
    (hp : ∀ {t j v}, p t → t.eval w j = some v → r v j) (hP : ∀ f, (P f).AllWalks p)
    (hlen : w.length = w'.length) (h : Eval P w i e b) :
    e.AllWalks p → EqOn (w[·]?) (w'[·]?) {v | r v i} → Eval P w' i e b := by
  have ht : ∀ {t : Walk} {j}, t.eval w' j = t.eval w j := (Walk.eval_congr hlen.symm _)
  induction h with
  | tru => exact fun _ _ ↦ .tru
  | fls => exact fun _ _ ↦ .fls
  | initial_true h => exact fun _ _ ↦ .initial_true (ht.trans h)
  | initial_false h hv => exact fun _ _ ↦ .initial_false (ht.trans h) hv
  | final_true h => exact fun _ _ ↦ .final_true (ht.trans (hlen ▸ h))
  | final_false h hv => exact fun _ _ ↦ .final_false (ht.trans h) (hlen ▸ hv)
  | label_true h hl has =>
    exact fun he hag ↦ .label_true (ht.trans h) ((hag (hp he h)).symm.trans hl) has
  | label_false h hl has =>
    exact fun he hag ↦ .label_false (ht.trans h) ((hag (hp he h)).symm.trans hl) has
  | call h _ ih =>
    exact fun he hag ↦ .call (ht.trans h)
      (ih (hP _) (hag.mono fun _ hu ↦ trans_of r hu (hp he h)))
  | ite_true _ _ ihc ih₁ => exact fun he hag ↦ .ite_true (ihc he.1 hag) (ih₁ he.2.1 hag)
  | ite_false _ _ ihc ih₂ => exact fun he hag ↦ .ite_false (ihc he.1 hag) (ih₂ he.2.2 hag)

/-- A successor-free program evaluated at `i` reads only the prefix through `i`, so equal-length
words with that prefix in common evaluate identically. -/
theorem Eval.congr_take (hP : P.Backward) (hlen : w.length = w'.length)
    (h : Eval P w i e b) :
    e.AllWalks Walk.Backward → w.take (i + 1) = w'.take (i + 1) → Eval P w' i e b := fun he hw ↦
  h.congr_of_allWalks (r := (· ≤ ·)) (fun ht hv ↦ Walk.eval_le_of_backward ht hv) hP hlen he
    fun _ hk ↦ List.take_eq_take_iff_getElem?.mp hw _ (Nat.lt_succ_of_le hk)

/-- A predecessor-free program evaluated at `i` reads only the suffix from `i`, so equal-length
words with that suffix in common evaluate identically. -/
theorem Eval.congr_drop (hP : P.Forward) (hlen : w.length = w'.length)
    (h : Eval P w i e b) :
    e.AllWalks Walk.Forward → w.drop i = w'.drop i → Eval P w' i e b := fun he hw ↦
  h.congr_of_allWalks (r := (· ≥ ·)) (fun ht hv ↦ Walk.le_eval_of_forward ht hv) hP hlen he
    fun _ hk ↦ List.drop_eq_drop_iff_getElem?.mp hw _ hk

/-! ### Evaluation in rounds

A round reruns every rule body with its calls read from a table of the values found so far,
starting from the empty table. Values only accumulate, a round reads the table only at
positions of the word, and until the rounds settle each one values a new pair of a head and a
position, so on a word of length `n` they settle by round `card F * n`. -/

section Rounds

variable [DecidableEq α] {V V' : F → ℕ → Option Bool} {k m : ℕ}

/-- `e.evalWith w V i` evaluates `e` at `i` in one round, reading each rule-head call from the
table `V` instead of unfolding it. -/
def Expr.evalWith (w : List α) (V : F → ℕ → Option Bool) (i : ℕ) : Expr α F → Option Bool
  | .tru => some true
  | .fls => some false
  | .initial t => (t.eval w i).map fun v ↦ decide (v = 0)
  | .final t => (t.eval w i).map fun v ↦ decide (v = w.length - 1)
  | .label s t => (t.eval w i).bind fun v ↦ w[v]?.map fun a ↦ decide (a ∈ s)
  | .call f t => (t.eval w i).bind (V f)
  | .ite c e₁ e₂ =>
      (c.evalWith w V i).bind fun b ↦ bif b then e₁.evalWith w V i else e₂.evalWith w V i

/-- `P.approx w k` is the table after `k` rounds of evaluation. The first round starts from the
empty table, and each round reruns every rule body against the table before it. -/
def Program.approx (P : Program α F) (w : List α) : ℕ → F → ℕ → Option Bool
  | 0, _, _ => none
  | k + 1, f, i => (P f).evalWith w (P.approx w k) i

/-- A round against a larger table finds the same values. -/
theorem Expr.evalWith_mono (hV : ∀ f j b, V f j = some b → V' f j = some b) :
    e.evalWith w V i = some b → e.evalWith w V' i = some b := by
  induction e generalizing b with
  | call f t =>
    simp only [evalWith, Option.bind_eq_some_iff]
    exact fun ⟨v, hv, h⟩ ↦ ⟨v, hv, hV _ _ _ h⟩
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    simp only [evalWith, Option.bind_eq_some_iff]
    rintro ⟨_ | _, hc, h⟩
    exacts [⟨false, ihc hc, ih₂ h⟩, ⟨true, ihc hc, ih₁ h⟩]
  | _ => exact id

/-- A round reads its table only at positions of the word. -/
theorem Expr.evalWith_congr (hV : ∀ f, ∀ j < w.length, V f j = V' f j) (e : Expr α F) :
    e.evalWith w V i = e.evalWith w V' i := by
  induction e with
  | call f t =>
    simp only [evalWith]
    cases h : t.eval w i with
    | none => rfl
    | some v => exact hV f v (Walk.eval_lt h)
  | ite c e₁ e₂ ihc ih₁ ih₂ => simp only [evalWith, ihc, ih₁, ih₂]
  | _ => rfl

namespace Program

theorem approx_succ_of_eq_some : ∀ {k : ℕ} {f : F} {j : ℕ} {b : Bool},
    P.approx w k f j = some b → P.approx w (k + 1) f j = some b
  | _ + 1, _, _, _, h => Expr.evalWith_mono (fun _ _ _ ↦ approx_succ_of_eq_some) h

/-- Rounds only add values. -/
theorem approx_mono (hkm : k ≤ m) {f : F} {j : ℕ} (h : P.approx w k f j = some b) :
    P.approx w m f j = some b := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact approx_succ_of_eq_some ih

theorem evalWith_approx_mono (hkm : k ≤ m) :
    e.evalWith w (P.approx w k) i = some b → e.evalWith w (P.approx w m) i = some b :=
  Expr.evalWith_mono fun _ _ _ ↦ approx_mono hkm

/-- A round against a table of derived values derives every value it finds. -/
theorem eval_of_evalWith (hV : ∀ f j b, V f j = some b → Eval P w j (P f) b) :
    e.evalWith w V i = some b → Eval P w i e b := by
  induction e generalizing b with
  | tru => rintro ⟨⟩; exact .tru
  | fls => rintro ⟨⟩; exact .fls
  | initial t =>
    simp only [Expr.evalWith, Option.map_eq_some_iff]
    rintro ⟨v, hv, rfl⟩
    exact .initial hv
  | final t =>
    simp only [Expr.evalWith, Option.map_eq_some_iff]
    rintro ⟨v, hv, rfl⟩
    exact .final hv
  | label s t =>
    simp only [Expr.evalWith, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    rintro ⟨v, hv, a, ha, rfl⟩
    exact .label hv ha
  | call f t =>
    simp only [Expr.evalWith, Option.bind_eq_some_iff]
    rintro ⟨v, hv, h⟩
    exact .call hv (hV _ _ _ h)
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    simp only [Expr.evalWith, Option.bind_eq_some_iff]
    rintro ⟨_ | _, hc, h⟩
    exacts [.ite_false (ihc hc) (ih₂ h), .ite_true (ihc hc) (ih₁ h)]

/-- Every value a round finds is derived. -/
theorem eval_of_approx : ∀ {k : ℕ} {f : F} {j : ℕ} {b : Bool},
    P.approx w k f j = some b → Eval P w j (P f) b
  | _ + 1, _, _, _, h => eval_of_evalWith (fun _ _ _ ↦ eval_of_approx) h

/-- Every derived value is found by some round. -/
theorem exists_evalWith_approx (h : Eval P w i e b) :
    ∃ k, e.evalWith w (P.approx w k) i = some b := by
  induction h with
  | tru | fls => exact ⟨0, rfl⟩
  | initial_true h | final_true h => exact ⟨0, by simp [Expr.evalWith, h]⟩
  | initial_false h hv => exact ⟨0, by simp [Expr.evalWith, h, hv.ne']⟩
  | final_false h hv => exact ⟨0, by simp [Expr.evalWith, h, hv.ne]⟩
  | label_true h hl has | label_false h hl has =>
    exact ⟨0, by simp [Expr.evalWith, h, hl, has]⟩
  | call h _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by simpa [Expr.evalWith, h, approx] using hk⟩
  | ite_true _ _ ihc ih₁ =>
    obtain ⟨k₁, hk₁⟩ := ihc
    obtain ⟨k₂, hk₂⟩ := ih₁
    exact ⟨max k₁ k₂, Option.bind_eq_some_iff.mpr ⟨true,
      evalWith_approx_mono (le_max_left _ _) hk₁, evalWith_approx_mono (le_max_right _ _) hk₂⟩⟩
  | ite_false _ _ ihc ih₂ =>
    obtain ⟨k₁, hk₁⟩ := ihc
    obtain ⟨k₂, hk₂⟩ := ih₂
    exact ⟨max k₁ k₂, Option.bind_eq_some_iff.mpr ⟨false,
      evalWith_approx_mono (le_max_left _ _) hk₁, evalWith_approx_mono (le_max_right _ _) hk₂⟩⟩

/-- Once a round changes no value on the word, no later round does. -/
private theorem approx_eq_of_settled
    (hk : ∀ f, ∀ j < w.length, P.approx w (k + 1) f j = P.approx w k f j) (hkm : k ≤ m) :
    ∀ f, ∀ j < w.length, P.approx w m f j = P.approx w k f j := by
  induction m, hkm using Nat.le_induction with
  | base => exact fun _ _ _ ↦ rfl
  | succ m _ ih =>
    intro f j hj
    rw [← hk f j hj]
    exact Expr.evalWith_congr ih (P f)

/-- On a word of length `n` the rounds settle by round `card F * n`, since each round before
they settle gives a value to a new pair of a head and a position. -/
theorem approx_eq_approx_card_mul_length [Fintype F] (hk : Fintype.card F * w.length ≤ k) :
    ∀ f, ∀ j < w.length, P.approx w k f j = P.approx w (Fintype.card F * w.length) f j := by
  let cells := (Finset.univ : Finset F) ×ˢ Finset.range w.length
  let D k := cells.filter fun c ↦ (P.approx w k c.1 c.2).isSome
  let Settled k := ∀ f, ∀ j < w.length, P.approx w (k + 1) f j = P.approx w k f j
  have hsub k : D k ⊆ D (k + 1) := fun c hc ↦ by
    simp only [D, Finset.mem_filter, Option.isSome_iff_exists] at hc ⊢
    obtain ⟨hc, b, hb⟩ := hc
    exact ⟨hc, b, approx_succ_of_eq_some hb⟩
  have key k : (∃ k₀ ≤ k, Settled k₀) ∨ k ≤ (D k).card := by
    induction k with
    | zero => exact .inr (Nat.zero_le _)
    | succ k ih =>
      rcases ih with ⟨k₀, hk₀, h⟩ | ih
      · exact .inl ⟨k₀, by omega, h⟩
      by_cases hs : Settled k
      · exact .inl ⟨k, by omega, hs⟩
      simp only [Settled, not_forall] at hs
      obtain ⟨f, j, hj, hne⟩ := hs
      have hnone : P.approx w k f j = none := by
        cases h : P.approx w k f j with
        | none => rfl
        | some b => exact absurd ((approx_succ_of_eq_some h).trans h.symm) hne
      rw [hnone] at hne
      refine .inr (ih.trans_lt (Finset.card_lt_card ((Finset.ssubset_iff_of_subset
        (hsub k)).mpr ⟨(f, j), ?_, ?_⟩)))
      · simpa [D, cells, hj, Option.isSome_iff_ne_none] using hne
      · simp [D, hnone]
  obtain ⟨k₀, hk₀, hs⟩ : ∃ k₀ ≤ Fintype.card F * w.length, Settled k₀ := by
    refine (key _).elim id fun hN ↦ ⟨_, le_rfl, fun f j hj ↦ ?_⟩
    have hD : D (Fintype.card F * w.length) = cells :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa [cells] using hN)
    have hmem : (f, j) ∈ D (Fintype.card F * w.length) := by rw [hD]; simp [cells, hj]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hmem).2
    rw [hb, approx_succ_of_eq_some hb]
  intro f j hj
  rw [approx_eq_of_settled hs (hk₀.trans hk) f j hj, approx_eq_of_settled hs hk₀ f j hj]

/-- The value of `e` at `i` under `P`, from the round by which the rounds settle; `none` where
`P` does not halt. -/
def eval [Fintype F] (P : Program α F) (w : List α) (i : ℕ) (e : Expr α F) : Option Bool :=
  e.evalWith w (P.approx w (Fintype.card F * w.length)) i

/-- The rounds settle on the derivation system. -/
theorem eval_eq_some_iff [Fintype F] : P.eval w i e = some b ↔ Eval P w i e b := by
  refine ⟨eval_of_evalWith fun _ _ _ ↦ eval_of_approx, fun h ↦ ?_⟩
  obtain ⟨k, hk⟩ := exists_evalWith_approx h
  rcases le_total k (Fintype.card F * w.length) with hkN | hNk
  · exact evalWith_approx_mono hkN hk
  · rwa [Expr.evalWith_congr (approx_eq_approx_card_mul_length hNk)] at hk

instance [Fintype F] : Decidable (Eval P w i e b) := decidable_of_iff _ eval_eq_some_iff

instance [Fintype F] : Decidable (P.TotalOn w) :=
  inferInstanceAs (Decidable (∀ f, ∀ i < w.length, ∃ b, Eval P w i (.call f .var) b))

end Program

end Rounds

end Subregular.BMRS
