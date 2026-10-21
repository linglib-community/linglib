/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Basic
public import Linglib.Core.Data.List.DropRight

/-!
# Quantifier-free position tests

A `Subregular.Walk` walks successor and predecessor steps from a position, and a
`Subregular.WindowFormula` is a boolean combination of label and definedness tests on such walks.
Because successor and predecessor are *functions*, a term reaches a bounded neighbourhood of its
position with no quantifiers, the syntactic source of strict locality. Satisfaction is
decidable, and a formula whose walks are backward with depth `≤ r` reads only the `r + 1`
symbols ending at its position (`BackBounded.realize_congr`). These formulas are the guards of
logical transductions (`Transduction.lean`) and the term language of boolean monadic recursive
schemes (`BMRS.lean`).

## Main definitions

* `Subregular.succ?` / `Subregular.pred?`: the next/previous position, as partial functions.
* `Subregular.Walk`: walks; `Walk.eval` reads the position a walk reaches, `none` off an edge.
* `Walk.Backward` / `Walk.Forward` / `Walk.pdepth` / `Walk.sdepth`: one-sided walks and how far
  back and forward a walk reaches.
* `Subregular.WindowFormula`: label/definedness tests on walks, closed under boolean combination;
  `WindowFormula.Realize` is decidable satisfaction; `initial`/`final` are the derived edge tests.
* `WindowFormula.Bounded l r`: every walk reaches at most `l` back and `r` forward;
  `WindowFormula.BackBounded r` is `Bounded r 0`.
* `Walk.back j`, `WindowFormula.window r u`: the walk `j` steps back, and the test that the last
  `r` symbols before the position spell `u`.

## Main results

* `Walk.eval_backward`: a backward walk of depth `j` from position `n` reads exactly `n - j`.
* `Walk.eval_bounded`: a walk reads the same displacement from two positions whose windows
  have the same edges.
* `Bounded.realize_congr`: a bounded formula cannot distinguish positions whose windows agree;
  `BackBounded.realize_congr` is the left-window case.
* `realize_window`: `window r u` holds exactly where the last `r` symbols before the position
  spell `u`.

## Implementation notes

The logic is monadic — one position variable, so `Walk.eval` takes a position rather than an
assignment — since every consumer (transduction guards, BMRS) is; and there is no equality atom:
with a single position variable, two walks from one origin agree exactly when both are defined
with equal displacement, so equality tests reduce to definedness tests. It is a bespoke syntax
rather than a fragment of `FirstOrder.Language`: over a relational word signature,
quantifier-free formulas cannot leave their variables, so bounded-window reach requires
successor and predecessor as *function* symbols — but a mathlib `Structure` interprets function
symbols totally, whereas falling off an edge is the semantics here (`defined`, `initial`,
`final`).

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace Subregular

variable {α : Type*}

/-! ### Positions -/

/-- The successor of `n` is the position after it, defined iff it is in range. -/
def succ? (w : List α) (n : ℕ) : Option ℕ :=
  if n + 1 < w.length then some (n + 1) else none

/-- The predecessor of `n` is the position before it, defined iff `n > 0`. -/
def pred? (w : List α) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if n < w.length then some n else none

theorem succ?_eq_some_iff {w : List α} {n m : ℕ} :
    succ? w n = some m ↔ m = n + 1 ∧ n + 1 < w.length := by
  unfold succ?
  split <;> simp_all
  all_goals omega

theorem pred?_eq_some_iff {w : List α} {n m : ℕ} :
    pred? w n = some m ↔ n = m + 1 ∧ m < w.length := by
  cases n with
  | zero => simp [pred?]
  | succ k =>
    unfold pred?
    split <;> simp_all
    all_goals omega

@[simp] theorem pred?_zero (w : List α) : pred? w 0 = none := rfl

theorem pred?_of_pos {w : List α} {m : ℕ} (h0 : 0 < m) (hm : m ≤ w.length) :
    pred? w m = some (m - 1) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have hm' : m' < w.length := by omega
  simp [pred?, hm']

/-- The successor structure depends only on the length. -/
theorem succ?_congr {w w' : List α} (h : w.length = w'.length) : succ? w = succ? w' := by
  funext n; simp [succ?, h]

/-- The predecessor structure depends only on the length. -/
theorem pred?_congr {w w' : List α} (h : w.length = w'.length) : pred? w = pred? w' := by
  funext n; cases n <;> simp [pred?, h]

/-! ### Walks -/

/-- A **term** is a walk of successor and predecessor steps from the position variable. Chains of
`succ` and `pred` reach a bounded window with no quantifier. -/
inductive Walk where
  | var : Walk
  | succ : Walk → Walk
  | pred : Walk → Walk
  deriving DecidableEq

namespace Walk

/-- The position a term reads, walking from position `n` of `w`; `none` once the walk falls off
an edge. -/
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

/-- The variable reads its own in-domain position. -/
@[simp] theorem eval_var (h : n < w.length) : Walk.var.eval w n = some n := ite_eq_left h

/-- Terms read in-domain positions. -/
theorem eval_lt : ∀ {t : Walk} {v : ℕ}, t.eval w n = some v → v < w.length
  | .var, _, h => by
    obtain ⟨rfl, hlt⟩ := eval_var_eq_some_iff.mp h
    exact hlt
  | .succ t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hlt⟩ := succ?_eq_some_iff.mp hu
    exact hlt
  | .pred t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    exact (pred?_eq_some_iff.mp hu).2

/-- A one-step successor walk reads the successor position. -/
@[simp] theorem eval_succ_var : Walk.var.succ.eval w n = succ? w n := by
  rcases Nat.lt_or_ge n w.length with h | h
  · rw [eval_succ, eval_var h, Option.bind_some]
  · rw [eval_succ, eval, ite_eq_right (by simpa using h), Option.bind_none, eq_comm,
      Option.eq_none_iff_forall_ne_some]
    intro m hm
    have := (succ?_eq_some_iff.mp hm).2
    omega

/-- A one-step predecessor walk reads the predecessor position (in-domain, since off the right
edge `pred?` is still defined at `w.length` but the variable is not). -/
theorem eval_pred_var (h : n < w.length) : Walk.var.pred.eval w n = pred? w n := by
  rw [eval_pred, eval_var h, Option.bind_some]

/-- Terms read only the length, so their reads transport across equal-length words. -/
theorem eval_congr (hlen : w.length = w'.length) : ∀ t : Walk, t.eval w n = t.eval w' n
  | .var => by simp [eval, hlen]
  | .succ t => by rw [eval_succ, eval_succ, eval_congr hlen t, succ?_congr hlen]
  | .pred t => by rw [eval_pred, eval_pred, eval_congr hlen t, pred?_congr hlen]

/-- The substitution `t.comp u` walks `u` first, then `t`. -/
def comp : Walk → Walk → Walk
  | .var, u => u
  | .succ t, u => .succ (t.comp u)
  | .pred t, u => .pred (t.comp u)

/-- Composite terms read sequenced positions. -/
theorem eval_comp : ∀ t u : Walk, (t.comp u).eval w n = (u.eval w n).bind fun v => t.eval w v
  | .var, u => by
    cases hu : u.eval w n with
    | none => simp [comp, hu]
    | some v => simp [comp, hu, eval_var (eval_lt hu)]
  | .succ t, u => by simp only [comp, eval_succ, eval_comp t u, Option.bind_assoc]
  | .pred t, u => by simp only [comp, eval_pred, eval_comp t u, Option.bind_assoc]

/-! ### Directed walks -/

/-- A term is *backward* if it uses no successor — only the variable and predecessors, so it
reads positions at or before its variable. -/
def Backward : Walk → Prop
  | .var => True
  | .pred t => t.Backward
  | .succ _ => False

/-- A term is *forward* if it uses no predecessor, so it reads positions at or after its
variable. -/
def Forward : Walk → Prop
  | .var => True
  | .pred _ => False
  | .succ t => t.Forward

/-- The predecessor depth of a term is how far back it reaches. -/
def pdepth : Walk → ℕ
  | .var => 0
  | .pred t => t.pdepth + 1
  | .succ t => t.pdepth

/-- The successor depth of a term is how far forward it reaches. -/
def sdepth : Walk → ℕ
  | .var => 0
  | .pred t => t.sdepth
  | .succ t => t.sdepth + 1

instance instDecidableBackward : ∀ t : Walk, Decidable t.Backward
  | .var => .isTrue trivial
  | .pred t => instDecidableBackward t
  | .succ _ => .isFalse not_false

instance instDecidableForward : ∀ t : Walk, Decidable t.Forward
  | .var => .isTrue trivial
  | .pred _ => .isFalse not_false
  | .succ t => instDecidableForward t

/-- Backward terms only move left. -/
theorem eval_le_of_backward :
    ∀ {t : Walk}, t.Backward → ∀ {v}, t.eval w n = some v → v ≤ n
  | .var, _, v, h => Nat.le_of_eq (eval_var_eq_some_iff.mp h).1
  | .pred t, ht, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := pred?_eq_some_iff.mp huv
    exact Nat.le_of_succ_le (eval_le_of_backward (t := t) ht hu)

/-- Forward terms only move right. -/
theorem le_eval_of_forward :
    ∀ {t : Walk}, t.Forward → ∀ {v}, t.eval w n = some v → n ≤ v
  | .var, _, v, h => Nat.le_of_eq (eval_var_eq_some_iff.mp h).1.symm
  | .succ t, ht, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := succ?_eq_some_iff.mp huv
    exact Nat.le_trans (le_eval_of_forward (t := t) ht hu) (Nat.le_succ u)

/-- A backward term of predecessor depth `j`, read from an in-range position `n`, reads exactly
position `n - j` — defined iff `j ≤ n`. -/
theorem eval_backward (hn : n < w.length) :
    ∀ {t : Walk}, t.Backward →
      t.eval w n = if t.pdepth ≤ n then some (n - t.pdepth) else none := by
  intro t ht
  induction t with
  | var => simp [eval, pdepth, hn]
  | succ t _ => exact absurd ht (by simp [Backward])
  | pred t ih =>
    simp only [Backward] at ht
    simp only [eval_pred, ih ht, pdepth]
    by_cases h : t.pdepth ≤ n
    · rw [ite_eq_left h, Option.bind_some]
      by_cases h0 : t.pdepth = n
      · subst h0; rw [Nat.sub_self, pred?_zero, ite_eq_right (by omega)]
      · rw [pred?_of_pos (by omega) (by omega), ite_eq_left (by omega), Nat.sub_sub]
    · rw [ite_eq_right h, Option.bind_none, ite_eq_right (by omega)]

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

theorem backward_back : ∀ j, (back j).Backward
  | 0 => trivial
  | j + 1 => backward_back j

/-- From an in-range position `n`, the walk `j` steps back reads position `n - j`, defined iff
`j ≤ n`. -/
theorem eval_back (hn : n < w.length) (j : ℕ) :
    (back j).eval w n = if j ≤ n then some (n - j) else none := by
  simpa using eval_backward hn (backward_back j)

/-! ### Bounded windows -/

/-- A walk reaches at most `pdepth` back. -/
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

/-- A walk reaches at most `sdepth` forward. -/
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

/-- **Window transport.** From two in-range positions whose windows `l` back and `r` forward
have the same edges — an offset stays in range at one exactly when it does at the other — a
walk reaching at most `l` back and `r` forward reads the same displacement, or falls off at
both. -/
theorem eval_bounded {l r n' : ℕ} (hn : n < w.length) (hn' : n' < w'.length)
    (hleft : ∀ j ≤ l, (j ≤ n ↔ j ≤ n'))
    (hright : ∀ j ≤ r, (n + j < w.length ↔ n' + j < w'.length)) :
    ∀ {t : Walk}, t.pdepth ≤ l → t.sdepth ≤ r →
      ((t.eval w n).map fun v ↦ (v : Int) - n) = (t.eval w' n').map fun v ↦ (v : Int) - n' := by
  intro t
  induction t with
  | var => intro _ _; simp [eval_var hn, eval_var hn']
  | succ t ih =>
    intro hp hs
    simp only [pdepth, sdepth] at hp hs
    have ih := ih hp (by omega)
    simp only [eval_succ]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at ih ⊢
    have hvn := le_eval_add_pdepth hv
    have hvs := eval_le_add_sdepth hv
    have hvl := eval_lt hv
    have hvl' := eval_lt hv'
    have key : v + 1 < w.length ↔ v' + 1 < w'.length := by
      rcases Nat.lt_or_ge v n with hlt | hge
      · constructor <;> intro <;> omega
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
        have hj : j + 1 ≤ r := by omega
        have := hright (j + 1) hj
        have hv'eq : v' = n' + j := by omega
        subst hv'eq
        simpa [Nat.add_assoc] using this
    by_cases h : v + 1 < w.length
    · rw [show succ? w v = some (v + 1) from succ?_eq_some_iff.mpr ⟨rfl, h⟩,
        show succ? w' v' = some (v' + 1) from succ?_eq_some_iff.mpr ⟨rfl, key.mp h⟩]
      simp; omega
    · rw [show succ? w v = none from by simp [succ?, h],
        show succ? w' v' = none from by simp [succ?, mt key.mpr h]]
      rfl
  | pred t ih =>
    intro hp hs
    simp only [pdepth, sdepth] at hp hs
    have ih := ih (by omega) hs
    simp only [eval_pred]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at ih ⊢
    have hvn := le_eval_add_pdepth hv
    have hvl := eval_lt hv
    have hvl' := eval_lt hv'
    have key : 1 ≤ v ↔ 1 ≤ v' := by
      rcases Nat.lt_or_ge n v with hlt | hge
      · constructor <;> intro <;> omega
      · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
        have hjl : j + 1 ≤ l := by omega
        have := hleft (j + 1) hjl
        constructor <;> intro <;> omega
    by_cases h : 1 ≤ v
    · have h' : 1 ≤ v' := key.mp h
      rw [pred?_of_pos h (Nat.le_of_lt hvl), pred?_of_pos h' (Nat.le_of_lt hvl')]
      simp
      omega
    · rw [show v = 0 by omega, show v' = 0 by omega]
      rfl

end Walk

/-! ### Quantifier-free formulas -/

/-- A **quantifier-free formula** is a boolean combination of label and definedness tests on
term walks from a single position. -/
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

@[simp] theorem realize_conj {w : List α} {n : ℕ} {φ ψ : WindowFormula α} :
    (φ.conj ψ).Realize w n ↔ φ.Realize w n ∧ ψ.Realize w n := Iff.rfl

/-- A label test at the position itself reads the symbol there. -/
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

/-- A bounded formula reads only its window: it has the same truth value at `(w, n)` and
`(w', n')` whenever the windows `l` back and `r` forward agree — the same labels at each
offset, and the same offsets in range. -/
theorem Bounded.realize_congr {l r : ℕ} {w w' : List α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hleft : ∀ j ≤ l, (j ≤ n ↔ j ≤ n') ∧ (j ≤ n → w[n - j]? = w'[n' - j]?))
    (hright : ∀ j ≤ r, (n + j < w.length ↔ n' + j < w'.length) ∧ w[n + j]? = w'[n' + j]?) :
    ∀ {φ : WindowFormula α}, φ.Bounded l r → (φ.Realize w n ↔ φ.Realize w' n') := by
  have hl : ∀ j ≤ l, (j ≤ n ↔ j ≤ n') := fun j hj ↦ (hleft j hj).1
  have hr : ∀ j ≤ r, (n + j < w.length ↔ n' + j < w'.length) := fun j hj ↦ (hright j hj).1
  intro φ
  induction φ with
  | label a t =>
    rintro ⟨hp, hs⟩
    have h := Walk.eval_bounded hn hn' hl hr hp hs
    simp only [Realize]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at h ⊢
    have hvn := Walk.le_eval_add_pdepth hv
    have hvs := Walk.eval_le_add_sdepth hv
    rcases Nat.lt_or_ge v n with hlt | hge
    · have hveq : v = n - (n - v) := by omega
      have hv'eq : v' = n' - (n - v) := by omega
      rw [hveq, hv'eq, (hleft (n - v) (by omega)).2 (by omega)]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
      have hv'eq : v' = n' + j := by omega
      rw [hv'eq, (hright j (by omega)).2]
  | defined t =>
    rintro ⟨hp, hs⟩
    have h := Walk.eval_bounded hn hn' hl hr hp hs
    simp only [Realize]
    rcases hv : t.eval w n with _ | v <;> rcases hv' : t.eval w' n' with _ | v' <;>
      simp [hv, hv'] at h ⊢
  | tru => intro _; simp [Realize]
  | fls => intro _; simp [Realize]
  | neg φ ih => intro hφ; simp only [Realize, ih hφ]
  | conj φ ψ ihφ ihψ => rintro ⟨h1, h2⟩; simp only [Realize, ihφ h1, ihψ h2]
  | disj φ ψ ihφ ihψ => rintro ⟨h1, h2⟩; simp only [Realize, ihφ h1, ihψ h2]

/-- A backward-bounded formula reads only the `r + 1` symbols ending at its position. -/
theorem BackBounded.realize_congr {r : ℕ} {w w' : List α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?)
    (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    ∀ {φ : WindowFormula α}, φ.BackBounded r → (φ.Realize w n ↔ φ.Realize w' n') :=
  Bounded.realize_congr hn hn' (fun j hj ↦ ⟨hedge j hj, fun _ ↦ hlbl j hj⟩) fun j hj ↦ by
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact ⟨iff_of_true (by simpa using hn) (by simpa using hn'),
      by simpa using hlbl 0 (Nat.zero_le _)⟩

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

theorem realize_readBack {w : List α} {n : ℕ} (hn : n < w.length) :
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

theorem bounded_readBack {l : ℕ} :
    ∀ {v : List α} {j : ℕ}, j + v.length ≤ l → (readBack v j).Bounded l 0
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨⟨by simp at h ⊢; omega, by simp⟩, bounded_readBack (by simp at h; omega)⟩

/-- At an in-range position, `window r u` holds exactly when the last `r` symbols before the
position spell `u`. -/
theorem realize_window {w u : List α} {n r : ℕ} (hn : n < w.length) (hu : u.length ≤ r) :
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

theorem window_backBounded {u : List α} {r : ℕ} (hu : u.length ≤ r) :
    (window r u).BackBounded r :=
  ⟨bounded_readBack (by simpa using hu), by
    split_ifs with h
    · exact ⟨by simp; omega, by simp⟩
    · trivial⟩

end WindowFormula

/-! ### Worked example -/

section Example

private inductive Sym | a | b deriving DecidableEq

/-- The position is flanked by `a`s — a bounded two-sided context stated by walks, with no
quantifier. -/
private def flankedByA : WindowFormula Sym :=
  .conj (.label .a (.pred .var)) (.label .a (.succ .var))

private def aba : List Sym := [Sym.a, Sym.b, Sym.a]

-- Position 1 (the `b`) is flanked by `a`s; position 0 is not (no predecessor).
example : flankedByA.Realize aba 1 := by decide
example : ¬ flankedByA.Realize aba 0 := by decide
-- The edge tests compute as expected.
example : (WindowFormula.initial (α := Sym) .var).Realize aba 0 := by decide
example : (WindowFormula.final (α := Sym) .var).Realize aba 2 := by decide

end Example

end Subregular
