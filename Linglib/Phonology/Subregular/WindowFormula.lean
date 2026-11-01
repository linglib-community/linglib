/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Basic
public import Linglib.Core.Data.List.DropRight

/-!
# Window formulas

This file defines window formulas, the quantifier-free formulas over strings with successor and
predecessor functions. A *walk* is a sequence of successor and predecessor steps from a position,
and a window formula is a boolean combination of tests on walks: the label at the position a walk
reaches, or whether it reaches one. Since successor and predecessor are functions, a formula reads
a bounded window around its position with no quantifier, the syntactic source of strict locality.
Window formulas are the guards of logical transductions; walks are the terms of boolean monadic
recursive schemes.

## Main definitions

* `Subregular.Walk`, `Walk.eval`: walks, and the position a walk reaches (`none` off an edge).
* `Subregular.WindowFormula`, `WindowFormula.Realize`: formulas, and decidable satisfaction.
* `WindowFormula.Bounded l r`: every walk reaches at most `l` back and `r` forward.
* `WindowFormula.window r u`: the last `r` symbols before the position spell `u`.

## Main results

* `WindowFormula.Bounded.realize_congr`: a bounded formula cannot distinguish positions whose
  windows agree.
* `WindowFormula.realize_window`: `window r u` holds where the last `r` symbols spell `u`.

## Implementation notes

Chandlee and Jardine make successor and predecessor total, the first position its own predecessor
and the last its own successor, and take equality as atomic, so that a position is first when it
equals its predecessor. Here a walk that steps off an edge reaches nothing, every test on it is
false, and a definedness test replaces equality: two walks from one position reach the same
position iff both are defined with equal displacement. Under their reading a guard must exclude
the edges explicitly: their guard $P_b(x) ∧ P_b(p(x))$ for rewriting `b` after `b` also fires at a
word-initial `b`, its own predecessor; here it does not. Mathlib's `FirstOrder.Language`
structures interpret function symbols totally, so this reading is not an instance of its model
theory.

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace Subregular

variable {α : Type*}

/-! ### Positions -/

/-- The successor of position `n` of `w`, defined when `n + 1` is a position. -/
def succ? (w : List α) (n : ℕ) : Option ℕ :=
  if n + 1 < w.length then some (n + 1) else none

/-- The predecessor of position `n` of `w`, defined when `n` is a position other than the first. -/
def pred? (w : List α) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if n + 1 < w.length then some n else none

theorem succ?_eq_some_iff {w : List α} {n m : ℕ} :
    succ? w n = some m ↔ m = n + 1 ∧ n + 1 < w.length := by
  unfold succ?; split <;> simp_all [eq_comm]

theorem pred?_eq_some_iff {w : List α} {n m : ℕ} :
    pred? w n = some m ↔ n = m + 1 ∧ n < w.length := by
  cases n <;> simp [pred?, and_comm]

@[simp] theorem pred?_zero (w : List α) : pred? w 0 = none := rfl

theorem pred?_of_pos {w : List α} {m : ℕ} (h0 : 0 < m) (hm : m < w.length) :
    pred? w m = some (m - 1) :=
  pred?_eq_some_iff.2 ⟨by omega, hm⟩

theorem succ?_congr {w w' : List α} (h : w.length = w'.length) : succ? w = succ? w' := by
  funext n; simp [succ?, h]

theorem pred?_congr {w w' : List α} (h : w.length = w'.length) : pred? w = pred? w' := by
  funext n; cases n <;> simp [pred?, h]

/-! ### Walks -/

/-- A walk of successor and predecessor steps from the position variable. Chains of `succ` and
`pred` reach a bounded window with no quantifier. -/
inductive Walk where
  | var : Walk
  | succ : Walk → Walk
  | pred : Walk → Walk
  deriving DecidableEq

namespace Walk

/-- The position a walk from position `n` of `w` reaches, or `none` if it falls off an edge. -/
def eval (w : List α) (n : ℕ) : Walk → Option ℕ
  | .var => if n < w.length then some n else none
  | .succ t => (eval w n t).bind (succ? w)
  | .pred t => (eval w n t).bind (pred? w)

variable {w w' : List α} {n v : ℕ} {t u : Walk}

@[simp] theorem eval_succ : t.succ.eval w n = (t.eval w n).bind (succ? w) := rfl

@[simp] theorem eval_pred : t.pred.eval w n = (t.eval w n).bind (pred? w) := rfl

theorem eval_var_eq_some_iff : Walk.var.eval w n = some v ↔ v = n ∧ n < w.length := by
  rw [eval]
  split <;> simp_all [eq_comm]
  omega

@[simp] theorem eval_var (h : n < w.length) : Walk.var.eval w n = some n := ite_eq_left h

theorem eval_lt : ∀ {t : Walk} {v : ℕ}, t.eval w n = some v → v < w.length
  | .var, _, h => (eval_var_eq_some_iff.mp h).1 ▸ (eval_var_eq_some_iff.mp h).2
  | .succ t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hlt⟩ := succ?_eq_some_iff.mp hu
    exact hlt
  | .pred t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hlt⟩ := pred?_eq_some_iff.mp hu
    omega

/-- A walk reaches a position only from a position of the word. -/
theorem lt_length_of_eval_eq_some : ∀ {t : Walk} {v : ℕ}, t.eval w n = some v → n < w.length
  | .var, _, h => (eval_var_eq_some_iff.mp h).2
  | .succ _, _, h | .pred _, _, h => by
    obtain ⟨u, hu, -⟩ := Option.bind_eq_some_iff.mp h
    exact lt_length_of_eval_eq_some hu

@[simp] theorem eval_succ_var : Walk.var.succ.eval w n = succ? w n := by
  by_cases h : n < w.length
  · rw [eval_succ, eval_var h, Option.bind_some]
  · simp [eval, succ?, h, show ¬ n + 1 < w.length by omega]

@[simp] theorem eval_pred_var : Walk.var.pred.eval w n = pred? w n := by
  by_cases h : n < w.length
  · rw [eval_pred, eval_var h, Option.bind_some]
  · cases n <;> simp [eval, pred?, h]

theorem eval_congr (hlen : w.length = w'.length) : ∀ t : Walk, t.eval w n = t.eval w' n
  | .var => by simp [eval, hlen]
  | .succ t => by rw [eval_succ, eval_succ, eval_congr hlen t, succ?_congr hlen]
  | .pred t => by rw [eval_pred, eval_pred, eval_congr hlen t, pred?_congr hlen]

/-- The substitution `t.comp u` walks `u` first, then `t`. -/
def comp : Walk → Walk → Walk
  | .var, u => u
  | .succ t, u => .succ (t.comp u)
  | .pred t, u => .pred (t.comp u)

theorem eval_comp : ∀ t u : Walk, (t.comp u).eval w n = (u.eval w n).bind fun v => t.eval w v
  | .var, u => by
    cases hu : u.eval w n with
    | none => simp [comp, hu]
    | some v => simp [comp, hu, eval_var (eval_lt hu)]
  | .succ t, u => by simp only [comp, eval_succ, eval_comp t u, Option.bind_assoc]
  | .pred t, u => by simp only [comp, eval_pred, eval_comp t u, Option.bind_assoc]

/-! ### Reach -/

/-- The number of predecessor steps of a walk, which bounds how far back it reaches. -/
def pdepth : Walk → ℕ
  | .var => 0
  | .pred t => t.pdepth + 1
  | .succ t => t.pdepth

/-- The number of successor steps of a walk, which bounds how far forward it reaches. -/
def sdepth : Walk → ℕ
  | .var => 0
  | .pred t => t.sdepth
  | .succ t => t.sdepth + 1

theorem le_eval_add_pdepth : ∀ {t : Walk} {v : ℕ}, t.eval w n = some v → n ≤ v + t.pdepth
  | .var, v, h => by
    obtain ⟨rfl, -⟩ := eval_var_eq_some_iff.mp h
    simp [pdepth]
  | .succ t, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := succ?_eq_some_iff.mp huv
    have := le_eval_add_pdepth hu
    simp only [pdepth]; omega
  | .pred t, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := pred?_eq_some_iff.mp huv
    have := le_eval_add_pdepth hu
    simp only [pdepth]; omega

theorem eval_le_add_sdepth : ∀ {t : Walk} {v : ℕ}, t.eval w n = some v → v ≤ n + t.sdepth
  | .var, v, h => by
    obtain ⟨rfl, -⟩ := eval_var_eq_some_iff.mp h
    simp [sdepth]
  | .succ t, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := succ?_eq_some_iff.mp huv
    have := eval_le_add_sdepth hu
    simp only [sdepth]; omega
  | .pred t, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := pred?_eq_some_iff.mp huv
    have := eval_le_add_sdepth hu
    simp only [sdepth]; omega

/-- A walk is backward if it takes no successor step, so it reaches only positions at or before
its start. -/
def Backward (t : Walk) : Prop := t.sdepth = 0

/-- A walk is forward if it takes no predecessor step, so it reaches only positions at or after
its start. -/
def Forward (t : Walk) : Prop := t.pdepth = 0

instance : DecidablePred Backward := fun t ↦ inferInstanceAs (Decidable (t.sdepth = 0))

instance : DecidablePred Forward := fun t ↦ inferInstanceAs (Decidable (t.pdepth = 0))

theorem eval_le_of_backward (ht : t.Backward) (h : t.eval w n = some v) : v ≤ n := by
  simpa [show t.sdepth = 0 from ht] using eval_le_add_sdepth h

theorem le_eval_of_forward (ht : t.Forward) (h : t.eval w n = some v) : n ≤ v := by
  simpa [show t.pdepth = 0 from ht] using le_eval_add_pdepth h

/-- The walk `j` predecessor steps back from the position. -/
def back : ℕ → Walk
  | 0 => .var
  | j + 1 => (back j).pred

@[simp] theorem pdepth_back : ∀ j, (back j).pdepth = j
  | 0 => rfl
  | j + 1 => congrArg (· + 1) (pdepth_back j)

@[simp] theorem sdepth_back : ∀ j, (back j).sdepth = 0
  | 0 => rfl
  | j + 1 => sdepth_back j

/-- From a position `n` of the word, the walk `j` steps back reaches `n - j` if `j ≤ n`. -/
theorem eval_back (hn : n < w.length) :
    ∀ j, (back j).eval w n = if j ≤ n then some (n - j) else none
  | 0 => by simp [back, hn]
  | j + 1 => by
    rw [back, eval_pred, eval_back hn j]
    by_cases h : j + 1 ≤ n
    · rw [ite_eq_left (by omega), ite_eq_left h, Option.bind_some,
        pred?_of_pos (by omega) (by omega), Nat.sub_sub]
    · by_cases h' : j ≤ n
      · rw [ite_eq_left h', ite_eq_right h, Option.bind_some, show n - j = 0 by omega, pred?_zero]
      · rw [ite_eq_right h', ite_eq_right h, Option.bind_none]

/-! ### Bounded windows -/

/-- A walk reaching at most `l` back and `r` forward moves the same displacement from `n` in `w`
and from `n'` in `w'`, or falls off from both, when the two positions are equally far from the
left edge up to `l` and the same offsets up to `r` forward are positions. -/
theorem eval_bounded {l r n' : ℕ} (hedge : min n l = min n' l)
    (hright : ∀ j ≤ r, (n + j < w.length ↔ n' + j < w'.length))
    (hp : t.pdepth ≤ l) (hs : t.sdepth ≤ r) :
    ((t.eval w n).map fun v ↦ (v : Int) - n) = (t.eval w' n').map fun v ↦ (v : Int) - n' := by
  have hnone {w : List α} {n : ℕ} (h : ¬ n < w.length) (t : Walk) : t.eval w n = none :=
    Option.eq_none_iff_forall_ne_some.2 fun _ hv ↦ h (lt_length_of_eval_eq_some hv)
  by_cases hn : n < w.length
  swap
  · rw [hnone hn, hnone (by simpa using (hright 0 (Nat.zero_le r)).not.mp hn)]; rfl
  have hn' : n' < w'.length := by simpa using (hright 0 (Nat.zero_le r)).mp (by simpa using hn)
  induction t with
  | var => simp [eval_var hn, eval_var hn']
  | succ t ih =>
    simp only [pdepth, sdepth] at hp hs
    have ih := ih hp (by omega)
    simp only [eval_succ]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at ih ⊢
    have hvn := le_eval_add_pdepth hv
    have hvs := eval_le_add_sdepth hv
    have key : v + 1 < w.length ↔ v' + 1 < w'.length := by
      rcases Nat.lt_or_ge v n with hlt | hge
      · constructor <;> intro <;> omega
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
        rw [show v' = n' + j by omega]
        exact hright (j + 1) (by omega)
    by_cases h : v + 1 < w.length
    · rw [succ?_eq_some_iff.mpr ⟨rfl, h⟩, succ?_eq_some_iff.mpr ⟨rfl, key.mp h⟩]
      simp; omega
    · rw [show succ? w v = none by simp [succ?, h],
        show succ? w' v' = none by simp [succ?, mt key.mpr h]]
      rfl
  | pred t ih =>
    simp only [pdepth, sdepth] at hp hs
    have ih := ih (by omega) hs
    simp only [eval_pred]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at ih ⊢
    have hvn := le_eval_add_pdepth hv
    have hvl := eval_lt hv
    have hvl' := eval_lt hv'
    by_cases h : 1 ≤ v
    · have h' : 1 ≤ v' := by omega
      rw [pred?_of_pos h hvl, pred?_of_pos h' hvl']
      simp; omega
    · rw [show v = 0 by omega, show v' = 0 by omega]
      rfl

end Walk

/-! ### Window formulas -/

/-- A window formula is a boolean combination of label and definedness tests on walks from a
single position. -/
inductive WindowFormula (α : Type*) where
  | label : α → Walk → WindowFormula α
  | defined : Walk → WindowFormula α
  | tru : WindowFormula α
  | fls : WindowFormula α
  | neg : WindowFormula α → WindowFormula α
  | conj : WindowFormula α → WindowFormula α → WindowFormula α
  | disj : WindowFormula α → WindowFormula α → WindowFormula α

namespace WindowFormula

/-- Satisfaction of a formula at position `n` of `w`; tests on an undefined walk are false. -/
def Realize (w : List α) (n : ℕ) : WindowFormula α → Prop
  | .label a t => (t.eval w n).bind (w[·]?) = some a
  | .defined t => t.eval w n ≠ none
  | .tru => True
  | .fls => False
  | .neg φ => ¬ φ.Realize w n
  | .conj φ ψ => φ.Realize w n ∧ ψ.Realize w n
  | .disj φ ψ => φ.Realize w n ∨ ψ.Realize w n

instance instDecidableRealize [DecidableEq α] (w : List α) (n : ℕ) :
    (φ : WindowFormula α) → Decidable (φ.Realize w n)
  | .label _ t => inferInstanceAs (Decidable ((t.eval w n).bind _ = _))
  | .defined t => inferInstanceAs (Decidable (t.eval w n ≠ none))
  | .tru => isTrue trivial
  | .fls => isFalse not_false
  | .neg φ => @instDecidableNot _ (instDecidableRealize w n φ)
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidableRealize w n φ) (instDecidableRealize w n ψ)
  | .disj φ ψ => @instDecidableOr _ _ (instDecidableRealize w n φ) (instDecidableRealize w n ψ)

@[simp] theorem realize_neg {w : List α} {n : ℕ} {φ : WindowFormula α} :
    φ.neg.Realize w n ↔ ¬ φ.Realize w n := Iff.rfl

@[simp] theorem realize_conj {w : List α} {n : ℕ} {φ ψ : WindowFormula α} :
    (φ.conj ψ).Realize w n ↔ φ.Realize w n ∧ ψ.Realize w n := Iff.rfl

@[simp] theorem realize_label_var {w : List α} {n : ℕ} {a : α} :
    (label a .var).Realize w n ↔ w[n]? = some a := by
  simp only [Realize, Walk.eval]
  split_ifs with h
  · simp
  · simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- `t` reads an initial position, one in the domain with no predecessor. -/
def initial (t : Walk) : WindowFormula α := .conj (.defined t) (.neg (.defined t.pred))

/-- `t` reads a final position, one in the domain with no successor. -/
def final (t : Walk) : WindowFormula α := .conj (.defined t) (.neg (.defined t.succ))

/-! ### Bounded formulas read only a window -/

/-- A formula is bounded by `l` back and `r` forward if every walk it uses reaches at most `l`
positions back and `r` forward, so it reads only the window from `l` before its position to
`r` after. -/
def Bounded (l r : ℕ) : WindowFormula α → Prop
  | .label _ t => t.pdepth ≤ l ∧ t.sdepth ≤ r
  | .defined t => t.pdepth ≤ l ∧ t.sdepth ≤ r
  | .tru => True
  | .fls => True
  | .neg φ => φ.Bounded l r
  | .conj φ ψ => φ.Bounded l r ∧ ψ.Bounded l r
  | .disj φ ψ => φ.Bounded l r ∧ ψ.Bounded l r

instance instDecidableBounded (l r : ℕ) : ∀ φ : WindowFormula α, Decidable (φ.Bounded l r)
  | .label _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .defined _ => inferInstanceAs (Decidable (_ ∧ _))
  | .tru => .isTrue trivial
  | .fls => .isTrue trivial
  | .neg φ => instDecidableBounded l r φ
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidableBounded l r φ) (instDecidableBounded l r ψ)
  | .disj φ ψ => @instDecidableAnd _ _ (instDecidableBounded l r φ) (instDecidableBounded l r ψ)

/-- A formula is backward-bounded by `r` if it reads only the `r + 1` positions ending at its
own, bounded by `r` back and nothing forward. -/
abbrev BackBounded (r : ℕ) (φ : WindowFormula α) : Prop := φ.Bounded r 0

variable {l r : ℕ} {φ : WindowFormula α} {w w' : List α} {n n' : ℕ}

/-- A formula bounded by `l` back and `r` forward has the same truth value at `n` in `w` and at
`n'` in `w'` when the windows agree: the positions are equally far from the left edge up to `l`,
and the offsets up to `l` back and `r` forward carry the same labels or none. -/
theorem Bounded.realize_congr (hφ : φ.Bounded l r) (hedge : min n l = min n' l)
    (hleft : ∀ j ≤ l, w[n - j]? = w'[n' - j]?) (hright : ∀ j ≤ r, w[n + j]? = w'[n' + j]?) :
    φ.Realize w n ↔ φ.Realize w' n' := by
  have hr j (hj : j ≤ r) : n + j < w.length ↔ n' + j < w'.length := by
    simp only [← Nat.not_le, ← List.getElem?_eq_none_iff, hright j hj]
  induction φ with
  | label a t =>
    obtain ⟨hp, hs⟩ := hφ
    have h := Walk.eval_bounded hedge hr hp hs
    simp only [Realize]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at h ⊢
    have hvn := Walk.le_eval_add_pdepth hv
    have hvs := Walk.eval_le_add_sdepth hv
    rcases Nat.lt_or_ge v n with hlt | hge
    · rw [show v = n - (n - v) by omega, show v' = n' - (n - v) by omega, hleft _ (by omega)]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
      rw [show v' = n' + j by omega, hright j (by omega)]
  | defined t =>
    have h := Walk.eval_bounded hedge hr hφ.1 hφ.2
    simp only [Realize]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at h ⊢
  | tru | fls => exact Iff.rfl
  | neg φ ih => simp only [Realize, ih hφ]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ => simp only [Realize, ihφ hφ.1, ihψ hφ.2]

/-- A backward-bounded formula reads only the `r + 1` symbols ending at its position. -/
theorem BackBounded.realize_congr (hφ : φ.BackBounded r) (hedge : min n r = min n' r)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?) : φ.Realize w n ↔ φ.Realize w' n' :=
  Bounded.realize_congr hφ hedge hlbl fun j hj ↦ by
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    simpa using hlbl 0 (Nat.zero_le _)

/-! ### Window tests -/

/-- `readBack v j` holds at a position when the positions `j + 1`, `j + 2`, … back carry `v`,
nearest first. -/
def readBack : List α → ℕ → WindowFormula α
  | [], _ => tru
  | b :: v, j => (label b (Walk.back (j + 1))).conj (readBack v (j + 1))

/-- `window r u` holds at a position when the last `r` symbols before it, or all of them if there
are fewer than `r`, spell `u`. -/
def window (r : ℕ) (u : List α) : WindowFormula α :=
  (readBack u.reverse 0).conj
    (if u.length < r then (defined (Walk.back (u.length + 1))).neg else tru)

theorem realize_readBack (hn : n < w.length) :
    ∀ {v : List α} {j : ℕ}, j ≤ n →
      ((readBack v j).Realize w n ↔ v <+: (w.take (n - j)).reverse)
  | [], _, _ => by simp [readBack, Realize]
  | b :: v, j, hj => by
    rcases Nat.lt_or_ge j n with h | h
    · have htake : w.take (n - j) = w.take (n - (j + 1)) ++ [w[n - (j + 1)]] := by
        rw [show n - j = n - (j + 1) + 1 by omega, List.take_add_one,
          List.getElem?_eq_getElem (by omega)]
        rfl
      rw [readBack, realize_conj, realize_readBack hn (by omega), htake, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.cons_prefix_cons]
      refine and_congr_left' ?_
      simp [Realize, Walk.eval_back hn, show j + 1 ≤ n by omega,
        List.getElem?_eq_getElem (show n - (j + 1) < w.length by omega), eq_comm]
    · obtain rfl : j = n := by omega
      simp [readBack, Realize, Walk.eval_back hn, Nat.not_succ_le_self]

theorem bounded_readBack :
    ∀ {v : List α} {j : ℕ}, j + v.length ≤ l → (readBack v j).Bounded l 0
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨⟨by simp at h ⊢; omega, by simp⟩, bounded_readBack (by simp at h; omega)⟩

/-- At a position of the word, `window r u` holds exactly when the last `r` symbols before the
position spell `u`. -/
theorem realize_window {u : List α} (hn : n < w.length) (hu : u.length ≤ r) :
    (window r u).Realize w n ↔ (w.take n).rtake r = u := by
  rw [List.rtake_eq_iff, window, realize_conj, realize_readBack hn (Nat.zero_le n), Nat.sub_zero,
    List.reverse_prefix]
  refine and_congr_right fun hs ↦ ?_
  have := hs.length_le
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at this ⊢
  split_ifs with h
  · simp [Realize, Walk.eval_back hn]
    omega
  · simp only [Realize, true_iff]
    omega

theorem window_backBounded {u : List α} (hu : u.length ≤ r) : (window r u).BackBounded r :=
  ⟨bounded_readBack (by simpa using hu), by
    split_ifs with h
    · exact ⟨by simp; omega, by simp⟩
    · trivial⟩

end WindowFormula

end Subregular
