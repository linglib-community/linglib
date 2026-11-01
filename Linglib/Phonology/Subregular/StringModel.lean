/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.ModelTheory.Semantics
public import Linglib.Core.Data.List.DropRight

/-!
# String models

This file defines the string models of Chandlee and Jardine, the first-order structures over
which quantifier-free formulas state local conditions on strings. The string model of a word has
its positions as domain, a unary relation $P_a$ for each symbol $a$, and the successor and
predecessor functions $s$ and $p$, the first position being its own predecessor and the last its
own successor, so that $\mathrm{first}(x)$ is $p(x) ≈ x$ and $\mathrm{last}(x)$ is $s(x) ≈ x$.
Since $s$ and $p$ are functions, a quantifier-free formula in the position variable $x$ reads a
bounded window around the position, the syntactic source of strict locality: a formula whose
terms step at most `l` back and `r` forward cannot tell apart positions whose windows agree.
These formulas are the guards of logical transductions.

## Main definitions

* `Subregular.stringLanguage`: the signature $\{s, p, P_a\}$.
* `Subregular.StringModel`: the string model of a word.
* `Subregular.StringFormula`: formulas in the position variable, with `StringFormula.HoldsAt`.
* `StringFormula.Bounded l r`: quantifier-free, with terms at most `l` back and `r` forward.
* `StringFormula.window r u`: the last `r` symbols before the position spell `u`.

## Main results

* `StringFormula.Bounded.holdsAt_congr`: a bounded formula cannot distinguish positions whose
  windows agree.
* `StringFormula.holdsAt_window`: `window r u` holds where the last `r` symbols spell `u`.

## Implementation notes

The word models of `Subregular.WordModel` order positions by a binary relation, over which a
quantifier-free formula cannot leave its variables; the window is reached here through the
function symbols. `HoldsAt` evaluates at a natural-number position, false off the word, as the
docking processes and transductions scan positions by index. The terms of boolean monadic
recursive schemes, `Subregular.Walk`, instead step off the word into nothing.

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
-/

@[expose] public section

open FirstOrder FirstOrder.Language Structure

namespace Subregular

universe u

/-- The function symbols of string models, successor and predecessor. -/
inductive StringFun : ℕ → Type
  | succ : StringFun 1
  | pred : StringFun 1

/-- The relation symbols of string models, a unary label for each symbol. -/
inductive StringRel (α : Type u) : ℕ → Type u
  | label (a : α) : StringRel α 1

/-- The signature of string models over the alphabet `α`. -/
def stringLanguage (α : Type u) : Language := ⟨StringFun, StringRel α⟩

variable {α : Type u}

/-! ### The string model of a word -/

/-- The string model of `w`, whose elements are the positions of `w`. -/
def StringModel (w : List α) : Type := Fin w.length

namespace StringModel

variable {w : List α}

instance : DecidableEq (StringModel w) := inferInstanceAs (DecidableEq (Fin w.length))

instance : Fintype (StringModel w) := inferInstanceAs (Fintype (Fin w.length))

/-- Position `n` of `w`. -/
def mk (n : ℕ) (h : n < w.length) : StringModel w := ⟨n, h⟩

/-- The index of a position. -/
def val (i : StringModel w) : ℕ := Fin.val (n := w.length) i

theorem val_lt (i : StringModel w) : i.val < w.length := Fin.isLt (n := w.length) i

@[simp] theorem val_mk {n : ℕ} (h : n < w.length) : (mk n h).val = n := rfl

theorem ext {i j : StringModel w} (h : i.val = j.val) : i = j := Fin.ext (n := w.length) h

/-- The symbol at a position. -/
def symbol (i : StringModel w) : α := w.get i

theorem getElem?_val (i : StringModel w) : w[i.val]? = some i.symbol :=
  List.getElem?_eq_getElem i.val_lt

theorem symbol_eq_iff {i : StringModel w} {a : α} : i.symbol = a ↔ w[i.val]? = some a := by
  rw [getElem?_val, Option.some_inj]

/-- The successor of a position, the last position being its own. -/
def succ (i : StringModel w) : StringModel w :=
  if h : i.val + 1 < w.length then mk (i.val + 1) h else i

/-- The predecessor of a position, the first position being its own. -/
def pred (i : StringModel w) : StringModel w := mk (i.val - 1) (by have := i.val_lt; omega)

theorem val_succ (i : StringModel w) :
    i.succ.val = if i.val + 1 < w.length then i.val + 1 else i.val := by
  unfold succ; split_ifs <;> rfl

@[simp] theorem val_pred (i : StringModel w) : i.pred.val = i.val - 1 := rfl

instance : (stringLanguage α).Structure (StringModel w) where
  funMap
    | .succ, x => (x 0).succ
    | .pred, x => (x 0).pred
  RelMap
    | .label a, x => (x 0).symbol = a

instance [DecidableEq α] :
    ∀ (n : ℕ) (R : (stringLanguage α).Relations n) (x : Fin n → StringModel w),
      Decidable (RelMap R x)
  | _, .label a, x => inferInstanceAs (Decidable ((x 0).symbol = a))

end StringModel

/-! ### Terms -/

/-- Terms in the position variable. -/
abbrev StringTerm (α : Type u) := (stringLanguage α).Term (Fin 1)

namespace StringTerm

/-- The successor $s(t)$ of a term. -/
def succ (t : StringTerm α) : StringTerm α :=
  Functions.apply₁ (L := stringLanguage α) StringFun.succ t

/-- The predecessor $p(t)$ of a term. -/
def pred (t : StringTerm α) : StringTerm α :=
  Functions.apply₁ (L := stringLanguage α) StringFun.pred t

/-- The term `j` predecessor steps back from the position variable. -/
def back : ℕ → StringTerm α
  | 0 => .var 0
  | j + 1 => (back j).pred

variable {w : List α} {γ : Type*}

@[simp] theorem realize_succ (v : Fin 1 → StringModel w) (t : StringTerm α) :
    t.succ.realize v = (t.realize v).succ := rfl

@[simp] theorem realize_pred (v : Fin 1 → StringModel w) (t : StringTerm α) :
    t.pred.realize v = (t.realize v).pred := rfl

theorem val_realize_back (v : Fin 1 → StringModel w) :
    ∀ j, ((back j : StringTerm α).realize v).val = (v 0).val - j
  | 0 => rfl
  | j + 1 => by rw [back, realize_pred, StringModel.val_pred, val_realize_back v j, Nat.sub_sub]

/-- The number of predecessor steps of a term, which bounds how far back it reaches. -/
def pdepth : (stringLanguage α).Term γ → ℕ
  | .var _ => 0
  | .func .succ ts => pdepth (ts 0)
  | .func .pred ts => pdepth (ts 0) + 1

/-- The number of successor steps of a term, which bounds how far forward it reaches. -/
def sdepth : (stringLanguage α).Term γ → ℕ
  | .var _ => 0
  | .func .succ ts => sdepth (ts 0) + 1
  | .func .pred ts => sdepth (ts 0)

@[simp] theorem pdepth_relabel {δ : Type*} (g : γ → δ) :
    ∀ t : (stringLanguage α).Term γ, pdepth (t.relabel g) = pdepth t
  | .var _ => rfl
  | .func .succ ts => pdepth_relabel g (ts 0)
  | .func .pred ts => congrArg (· + 1) (pdepth_relabel g (ts 0))

@[simp] theorem sdepth_relabel {δ : Type*} (g : γ → δ) :
    ∀ t : (stringLanguage α).Term γ, sdepth (t.relabel g) = sdepth t
  | .var _ => rfl
  | .func .succ ts => congrArg (· + 1) (sdepth_relabel g (ts 0))
  | .func .pred ts => sdepth_relabel g (ts 0)

@[simp] theorem pdepth_succ (t : StringTerm α) : pdepth t.succ = pdepth t := rfl
@[simp] theorem pdepth_pred (t : StringTerm α) : pdepth t.pred = pdepth t + 1 := rfl
@[simp] theorem sdepth_succ (t : StringTerm α) : sdepth t.succ = sdepth t + 1 := rfl
@[simp] theorem sdepth_pred (t : StringTerm α) : sdepth t.pred = sdepth t := rfl

@[simp] theorem pdepth_back : ∀ j, pdepth (back j : StringTerm α) = j
  | 0 => rfl
  | j + 1 => congrArg (· + 1) (pdepth_back j)

@[simp] theorem sdepth_back : ∀ j, sdepth (back j : StringTerm α) = 0
  | 0 => rfl
  | j + 1 => sdepth_back j

/-- A term evaluated where every variable denotes position `i` lands within its depths of `i`, and
at the same offset from `i` in `w` as from `i'` in `w'` when the two positions are equally far
from the left edge up to `l` and the same offsets up to `r` forward are positions. -/
theorem realize_offset {w' : List α} {i : StringModel w} {i' : StringModel w'} {l r : ℕ}
    (hedge : min i.val l = min i'.val l)
    (hright : ∀ j ≤ r, (i.val + j < w.length ↔ i'.val + j < w'.length))
    {v : γ → StringModel w} {v' : γ → StringModel w'} (hv : ∀ a, v a = i) (hv' : ∀ a, v' a = i') :
    ∀ t : (stringLanguage α).Term γ, pdepth t ≤ l → sdepth t ≤ r →
      -(pdepth t : Int) ≤ (t.realize v).val - i.val ∧ (t.realize v).val - (i.val : Int) ≤ sdepth t ∧
      ((t.realize v).val : Int) - i.val = (t.realize v').val - i'.val
  | .var a, _, _ => by simp [hv a, hv' a]
  | .func .succ ts, hp, hs => by
    have ih := realize_offset hedge hright hv hv' (ts 0) hp (by simp only [sdepth] at hs; omega)
    have hlt := (ts 0 |>.realize v).val_lt
    have hlt' := (ts 0 |>.realize v').val_lt
    have hi := i.val_lt
    have hi' := i'.val_lt
    simp only [sdepth] at hs
    change -(pdepth (ts 0) : Int) ≤ ((ts 0).realize v).succ.val - i.val ∧
      ((ts 0).realize v).succ.val - (i.val : Int) ≤ sdepth (ts 0) + 1 ∧
      (((ts 0).realize v).succ.val : Int) - i.val = ((ts 0).realize v').succ.val - i'.val
    rw [StringModel.val_succ, StringModel.val_succ]
    have key : ((ts 0).realize v).val + 1 < w.length ↔ ((ts 0).realize v').val + 1 < w'.length := by
      by_cases hd : ((ts 0).realize v).val + 1 ≤ i.val
      · constructor <;> intro <;> omega
      · have := hright (((ts 0).realize v).val + 1 - i.val) (by omega)
        constructor <;> intro <;> omega
    split_ifs <;> omega
  | .func .pred ts, hp, hs => by
    have ih := realize_offset hedge hright hv hv' (ts 0) (by simp only [pdepth] at hp; omega) hs
    simp only [pdepth] at hp
    change -((pdepth (ts 0) + 1 : ℕ) : Int) ≤ ((ts 0).realize v).pred.val - i.val ∧
      ((ts 0).realize v).pred.val - (i.val : Int) ≤ sdepth (ts 0) ∧
      (((ts 0).realize v).pred.val : Int) - i.val = ((ts 0).realize v').pred.val - i'.val
    simp only [StringModel.val_pred]
    omega

end StringTerm

/-! ### Formulas -/

/-- Formulas in the position variable. -/
abbrev StringFormula (α : Type u) := (stringLanguage α).Formula (Fin 1)

namespace StringFormula

open StringTerm

/-- $P_a(t)$: term `t` reads symbol `a`. -/
def label (a : α) (t : StringTerm α) : StringFormula α :=
  Relations.formula₁ (L := stringLanguage α) (StringRel.label a) t

/-- $\mathrm{first}(t)$, that is $p(t) ≈ t$: term `t` reads the first position. -/
def first (t : StringTerm α) : StringFormula α := t.pred.equal t

/-- $\mathrm{last}(t)$, that is $s(t) ≈ t$: term `t` reads the last position. -/
def last (t : StringTerm α) : StringFormula α := t.succ.equal t

variable {w : List α} {v : Fin 1 → StringModel w} {a : α} {t : StringTerm α}

@[simp] theorem realize_label : (label a t).Realize v ↔ (t.realize v).symbol = a := by
  simp only [label, Formula.realize_rel₁]; rfl

@[simp] theorem realize_first : (first t).Realize v ↔ (t.realize v).val = 0 := by
  simp only [first, Formula.realize_equal, realize_pred]
  constructor
  · intro h; have := congrArg StringModel.val h; simp only [StringModel.val_pred] at this; omega
  · intro h; exact StringModel.ext (by simp [h])

@[simp] theorem realize_last : (last t).Realize v ↔ (t.realize v).val + 1 = w.length := by
  simp only [last, Formula.realize_equal, realize_succ]
  have := (t.realize v).val_lt
  constructor
  · intro h; have := congrArg StringModel.val h
    rw [StringModel.val_succ] at this; split_ifs at this <;> omega
  · intro h; exact StringModel.ext (by rw [StringModel.val_succ, ite_eq_right (by omega)])

/-- `φ.HoldsAt w n`: `n` is a position of `w`, and `φ` holds there. -/
def HoldsAt (φ : StringFormula α) (w : List α) (n : ℕ) : Prop :=
  ∃ h : n < w.length, φ.Realize fun _ ↦ StringModel.mk n h

instance [DecidableEq α] (φ : StringFormula α) (w : List α) (n : ℕ) : Decidable (φ.HoldsAt w n) :=
  inferInstanceAs (Decidable (∃ h : n < w.length, φ.Realize fun _ ↦ StringModel.mk n h))

variable {φ ψ : StringFormula α} {n : ℕ}

theorem HoldsAt.lt_length (h : φ.HoldsAt w n) : n < w.length := h.1

@[simp] theorem holdsAt_top : (⊤ : StringFormula α).HoldsAt w n ↔ n < w.length := by
  simp [HoldsAt]

@[simp] theorem holdsAt_not : HoldsAt φ.not w n ↔ n < w.length ∧ ¬ φ.HoldsAt w n := by
  simp only [HoldsAt, Formula.realize_not, not_exists]
  exact ⟨fun ⟨h, hn⟩ ↦ ⟨h, fun _ ↦ hn⟩, fun ⟨h, hn⟩ ↦ ⟨h, hn h⟩⟩

@[simp] theorem holdsAt_inf : (φ ⊓ ψ).HoldsAt w n ↔ φ.HoldsAt w n ∧ ψ.HoldsAt w n := by
  simp only [HoldsAt, Formula.realize_inf]
  exact ⟨fun ⟨h, a, b⟩ ↦ ⟨⟨h, a⟩, h, b⟩, fun ⟨⟨h, a⟩, _, b⟩ ↦ ⟨h, a, b⟩⟩

@[simp] theorem holdsAt_sup : (φ ⊔ ψ).HoldsAt w n ↔ φ.HoldsAt w n ∨ ψ.HoldsAt w n := by
  simp [HoldsAt, exists_or]

@[simp] theorem holdsAt_label_var : (label a (.var 0)).HoldsAt w n ↔ w[n]? = some a := by
  simp only [HoldsAt, realize_label, Term.realize_var, StringModel.symbol, StringModel.mk]
  constructor
  · rintro ⟨h, rfl⟩; exact List.getElem?_eq_getElem h
  · intro h
    obtain ⟨h₁, h₂⟩ := List.getElem?_eq_some_iff.1 h
    exact ⟨h₁, h₂⟩

/-! ### Bounded formulas read only a window -/

/-- A formula is bounded by `l` back and `r` forward if it is quantifier-free and each of its terms
takes at most `l` predecessor and `r` successor steps, so that it reads only the window from `l`
before its position to `r` after. -/
def Bounded (l r : ℕ) : ∀ {n}, (stringLanguage α).BoundedFormula (Fin 1) n → Prop
  | _, .falsum => True
  | _, .equal t₁ t₂ => (pdepth t₁ ≤ l ∧ sdepth t₁ ≤ r) ∧ pdepth t₂ ≤ l ∧ sdepth t₂ ≤ r
  | _, .rel _ ts => ∀ k, pdepth (ts k) ≤ l ∧ sdepth (ts k) ≤ r
  | _, .imp φ ψ => Bounded l r φ ∧ Bounded l r ψ
  | _, .all _ => False

instance instDecidableBounded (l r : ℕ) :
    ∀ {n} (φ : (stringLanguage α).BoundedFormula (Fin 1) n), Decidable (Bounded l r φ)
  | _, .falsum => .isTrue trivial
  | _, .equal _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .rel _ _ => inferInstanceAs (Decidable (∀ _, _))
  | _, .imp φ ψ => @instDecidableAnd _ _ (instDecidableBounded l r φ) (instDecidableBounded l r ψ)
  | _, .all _ => .isFalse id

variable {l r : ℕ}

@[simp] theorem bounded_top : Bounded l r (⊤ : StringFormula α) := ⟨trivial, trivial⟩

@[simp] theorem bounded_not : Bounded l r φ.not ↔ Bounded l r φ := and_iff_left trivial

@[simp] theorem bounded_inf : Bounded l r (φ ⊓ ψ) ↔ Bounded l r φ ∧ Bounded l r ψ := by
  simp [Min.min, Bounded]

@[simp] theorem bounded_sup : Bounded l r (φ ⊔ ψ) ↔ Bounded l r φ ∧ Bounded l r ψ := by
  simp [Max.max, Bounded]

@[simp] theorem bounded_label : Bounded l r (label a t) ↔ pdepth t ≤ l ∧ sdepth t ≤ r := by
  simp [label, Relations.formula₁, Relations.formula, Relations.boundedFormula, Bounded]

@[simp] theorem bounded_first : Bounded l r (first t) ↔ pdepth t + 1 ≤ l ∧ sdepth t ≤ r := by
  simp only [first, Term.equal, Term.bdEqual, Bounded, pdepth_relabel, pdepth_pred,
    sdepth_relabel, sdepth_pred]
  omega

@[simp] theorem bounded_last : Bounded l r (last t) ↔ pdepth t ≤ l ∧ sdepth t + 1 ≤ r := by
  simp only [last, Term.equal, Term.bdEqual, Bounded, pdepth_relabel, pdepth_succ,
    sdepth_relabel, sdepth_succ]
  omega

private theorem realize_congr_aux {w' : List α} {i : StringModel w} {i' : StringModel w'}
    (hedge : min i.val l = min i'.val l) (hleft : ∀ j ≤ l, w[i.val - j]? = w'[i'.val - j]?)
    (hright : ∀ j ≤ r, w[i.val + j]? = w'[i'.val + j]?) :
    ∀ {n} (φ : (stringLanguage α).BoundedFormula (Fin 1) n), Bounded l r φ → n = 0 →
      ∀ xs xs', (φ.Realize (fun _ ↦ i) xs ↔ φ.Realize (fun _ ↦ i') xs')
  | _, .falsum, _, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, h, rfl, xs, xs' => by
    obtain ⟨⟨hp₁, hs₁⟩, hp₂, hs₂⟩ := h
    have hr j (hj : j ≤ r) : i.val + j < w.length ↔ i'.val + j < w'.length := by
      simp only [← Nat.not_le, ← List.getElem?_eq_none_iff, hright j hj]
    have hv (a : Fin 1 ⊕ Fin 0) : Sum.elim (fun _ ↦ i) xs a = i := by
      rcases a with _ | k
      · rfl
      · exact k.elim0
    have hv' (a : Fin 1 ⊕ Fin 0) : Sum.elim (fun _ ↦ i') xs' a = i' := by
      rcases a with _ | k
      · rfl
      · exact k.elim0
    have e₁ := StringTerm.realize_offset hedge hr hv hv' t₁ hp₁ hs₁
    have e₂ := StringTerm.realize_offset hedge hr hv hv' t₂ hp₂ hs₂
    simp only [BoundedFormula.Realize]
    constructor <;> intro h <;> apply StringModel.ext <;> have := congrArg StringModel.val h <;>
      omega
  | _, .rel (.label a) ts, hb, rfl, xs, xs' => by
    obtain ⟨hp, hs⟩ := hb 0
    have hr j (hj : j ≤ r) : i.val + j < w.length ↔ i'.val + j < w'.length := by
      simp only [← Nat.not_le, ← List.getElem?_eq_none_iff, hright j hj]
    have hv (a : Fin 1 ⊕ Fin 0) : Sum.elim (fun _ ↦ i) xs a = i := by
      rcases a with _ | k
      · rfl
      · exact k.elim0
    have hv' (a : Fin 1 ⊕ Fin 0) : Sum.elim (fun _ ↦ i') xs' a = i' := by
      rcases a with _ | k
      · rfl
      · exact k.elim0
    obtain ⟨e₁, e₂, e₃⟩ := StringTerm.realize_offset hedge hr hv hv' (ts 0) hp hs
    show ((ts 0).realize (Sum.elim (fun _ ↦ i) xs)).symbol = a ↔
      ((ts 0).realize (Sum.elim (fun _ ↦ i') xs')).symbol = a
    generalize (ts 0).realize (Sum.elim (fun _ ↦ i) xs) = P at e₁ e₂ e₃ ⊢
    generalize (ts 0).realize (Sum.elim (fun _ ↦ i') xs') = P' at e₁ e₂ e₃ ⊢
    suffices w[P.val]? = w'[P'.val]? by
      rw [P.getElem?_val, P'.getElem?_val, Option.some_inj] at this
      rw [this]
    by_cases hd : i.val ≤ P.val
    · rw [show P.val = i.val + (P.val - i.val) by omega,
        show P'.val = i'.val + (P.val - i.val) by omega]
      exact hright _ (by omega)
    · rw [show P.val = i.val - (i.val - P.val) by omega,
        show P'.val = i'.val - (i.val - P.val) by omega]
      exact hleft _ (by omega)
  | _, .imp φ ψ, h, hn, xs, xs' => by
    obtain ⟨hφ, hψ⟩ := h
    simp only [BoundedFormula.realize_imp, realize_congr_aux hedge hleft hright φ hφ hn xs xs',
      realize_congr_aux hedge hleft hright ψ hψ hn xs xs']
  | _, .all _, h, _, _, _ => h.elim

/-- A formula bounded by `l` back and `r` forward has the same truth value at `n` in `w` and at
`n'` in `w'` when the windows agree: the positions are equally far from the left edge up to `l`,
and the offsets up to `l` back and `r` forward carry the same symbols or none. -/
theorem Bounded.holdsAt_congr (hφ : Bounded l r φ) {w' : List α} {n' : ℕ}
    (hedge : min n l = min n' l) (hleft : ∀ j ≤ l, w[n - j]? = w'[n' - j]?)
    (hright : ∀ j ≤ r, w[n + j]? = w'[n' + j]?) : φ.HoldsAt w n ↔ φ.HoldsAt w' n' := by
  have h0 := hright 0 (Nat.zero_le r)
  simp only [Nat.add_zero] at h0
  have hlen : n < w.length ↔ n' < w'.length := by
    simp only [← Nat.not_le, ← List.getElem?_eq_none_iff, h0]
  constructor
  · rintro ⟨h, hφ'⟩
    exact ⟨hlen.1 h, (realize_congr_aux (i := StringModel.mk n h)
      (i' := StringModel.mk n' (hlen.1 h)) hedge hleft hright φ hφ rfl default default).1 hφ'⟩
  · rintro ⟨h, hφ'⟩
    exact ⟨hlen.2 h, (realize_congr_aux (i := StringModel.mk n (hlen.2 h))
      (i' := StringModel.mk n' h) hedge hleft hright φ hφ rfl default default).2 hφ'⟩

/-! ### Window tests -/

/-- `readBack v j` holds at a position when the positions `j + 1`, `j + 2`, … back exist and carry
`v`, nearest first. -/
def readBack : List α → ℕ → StringFormula α
  | [], _ => ⊤
  | b :: v, j => (first (back j)).not ⊓ label b (back (j + 1)) ⊓ readBack v (j + 1)

/-- `window r u` holds at a position when the last `r` symbols before it, or all of them if there
are fewer than `r`, spell `u`. -/
def window (r : ℕ) (u : List α) : StringFormula α :=
  readBack u.reverse 0 ⊓ if u.length < r then first (back u.length) else ⊤

theorem realize_readBack {i : StringModel w} :
    ∀ {v : List α} {j : ℕ}, j ≤ i.val →
      ((readBack v j).Realize (fun _ ↦ i) ↔ v <+: (w.take (i.val - j)).reverse)
  | [], _, _ => by simp [readBack]
  | b :: v, j, hj => by
    have hi := i.val_lt
    rcases Nat.lt_or_ge j i.val with h | h
    · have htake : w.take (i.val - j) = w.take (i.val - (j + 1)) ++ [w[i.val - (j + 1)] ] := by
        rw [show i.val - j = i.val - (j + 1) + 1 by omega, List.take_add_one,
          List.getElem?_eq_getElem (by omega)]
        rfl
      rw [readBack, Formula.realize_inf, Formula.realize_inf, realize_readBack (by omega), htake,
        List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_prefix_cons]
      refine and_congr_left' ?_
      simp only [Formula.realize_not, realize_first, realize_label, StringModel.symbol_eq_iff,
        val_realize_back, List.getElem?_eq_getElem (show i.val - (j + 1) < w.length by omega),
        Option.some_inj, eq_comm (a := b)]
      exact and_iff_right (by omega)
    · obtain rfl : j = i.val := by omega
      simp [readBack, val_realize_back]

theorem bounded_readBack : ∀ {v : List α} {j : ℕ}, j + v.length ≤ l → Bounded l 0 (readBack v j)
  | [], _, _ => bounded_top
  | _ :: _, _, h => by
    simp only [List.length_cons] at h
    simp only [readBack, bounded_inf, bounded_not, bounded_first, bounded_label, pdepth_back,
      sdepth_back]
    exact ⟨⟨⟨by omega, le_rfl⟩, by omega, le_rfl⟩, bounded_readBack (by omega)⟩

/-- At a position of the word, `window r u` holds exactly when the last `r` symbols before the
position spell `u`. -/
theorem holdsAt_window {u : List α} (hn : n < w.length) (hu : u.length ≤ r) :
    (window r u).HoldsAt w n ↔ (w.take n).rtake r = u := by
  have hR : (window r u).HoldsAt w n ↔
      (window r u).Realize fun _ ↦ StringModel.mk n hn := ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hn, h⟩⟩
  rw [hR, List.rtake_eq_iff, window, Formula.realize_inf, realize_readBack (Nat.zero_le _),
    StringModel.val_mk, Nat.sub_zero, List.reverse_prefix]
  refine and_congr_right fun hs ↦ ?_
  have := hs.length_le
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at this ⊢
  split_ifs with h
  · simp only [realize_first, val_realize_back, StringModel.val_mk]
    omega
  · simp only [Formula.realize_top, true_iff]
    omega

theorem bounded_window {u : List α} (hu : u.length ≤ r) : Bounded r 0 (window r u) := by
  rw [window, bounded_inf]
  refine ⟨bounded_readBack (by simpa using hu), ?_⟩
  split_ifs with h
  · simp only [bounded_first, pdepth_back, sdepth_back]
    omega
  · exact bounded_top

end StringFormula

end Subregular
