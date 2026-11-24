/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.CCG.Derivation
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Invariants of CCG derivations

Give each atom a value in a group. Every category then has a value: `X/Y` has the value of `X`
times the inverse of the value of `Y`, and `X\Y` the inverse of the value of `Y` times the value
of `X`. A harmonic rule multiplies the values of its daughters, so [the value of the category of
a harmonic derivation is the product, in order, of the values of its
leaves](##CCG.Derivation.eval_eq_prod_cats). A string of categories whose product is not the
value of `S` therefore has no harmonic derivation of `S`, whatever the rule system. Type-raising
leaves the value unchanged. In the free group on the atoms the value is the free group
interpretation of [pentus-1993].

Crossing composition changes the order of the factors, so it preserves the product only in a
commutative group, where [every derivation has the
invariant](##CCG.Derivation.eval_eq_prod_cats_of_comm). The count of an atom in a category
([van-benthem-1986]) is its value in the integers when that atom is sent to `1` and the others
to `0`, and [the count invariant](##CCG.Derivation.count_eq_sum) is this commutative case.

## References

* [pentus-1993]
* [van-benthem-1986]

## References

* [pentus-1993]
* [van-benthem-1986]
-/

@[expose] public section

namespace CCG

variable {T α : Type*}

namespace Cat

/-! ### Values in a group -/

section Group

variable {G : Type*} [Group G] (v : α → G)

/-- The value of a category in a group `G`, given the values `v` of the atoms: `X/Y` has the
value of `X` times the inverse of the value of `Y`, and `X\Y` the inverse of the value of `Y`
times the value of `X`. -/
def eval : Cat α → G
  | .atom a => v a
  | .slash .right x _ y => x.eval * (y.eval)⁻¹
  | .slash .left x _ y => (y.eval)⁻¹ * x.eval

@[simp] theorem eval_atom (a : α) : (atom a).eval v = v a := rfl

@[simp] theorem eval_slash_right (x y : Cat α) (m : Modality) :
    (slash .right x m y).eval v = x.eval v * (y.eval v)⁻¹ := rfl

@[simp] theorem eval_slash_left (x y : Cat α) (m : Modality) :
    (slash .left x m y).eval v = (y.eval v)⁻¹ * x.eval v := rfl

@[simp] theorem eval_forwardTypeRaise (x t : Cat α) :
    (x.forwardTypeRaise t).eval v = x.eval v := by
  simp [forwardTypeRaise]

@[simp] theorem eval_backwardTypeRaise (x t : Cat α) :
    (x.backwardTypeRaise t).eval v = x.eval v := by
  simp [backwardTypeRaise]

/-- Rightward arguments divide the value on the right, in order. -/
theorem eval_pushArgs_of_right (x : Cat α) {β : List (Arg α)} (h : ∀ b ∈ β, b.side = .right) :
    (x.pushArgs β).eval v = x.eval v * (β.map fun b ↦ (b.cat.eval v)⁻¹).prod := by
  induction β generalizing x with
  | nil => simp
  | cons b β ih =>
    obtain ⟨s, m, y⟩ := b
    obtain rfl : s = .right := h _ List.mem_cons_self
    rw [pushArgs_cons, ih _ fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]
    simp [mul_assoc]

/-- Leftward arguments divide the value on the left, the outermost first. -/
theorem eval_pushArgs_of_left (x : Cat α) {β : List (Arg α)} (h : ∀ b ∈ β, b.side = .left) :
    (x.pushArgs β).eval v = (β.reverse.map fun b ↦ (b.cat.eval v)⁻¹).prod * x.eval v := by
  induction β generalizing x with
  | nil => simp
  | cons b β ih =>
    obtain ⟨s, m, y⟩ := b
    obtain rfl : s = .left := h _ List.mem_cons_self
    rw [pushArgs_cons, ih _ fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]
    simp [mul_assoc]

end Group

/-- In a commutative group the side of a slash does not matter to the value. -/
theorem eval_pushArgs_of_comm {G : Type*} [CommGroup G] (v : α → G) (x : Cat α)
    (β : List (Arg α)) :
    (x.pushArgs β).eval v = x.eval v * (β.map fun b ↦ (b.cat.eval v)⁻¹).prod := by
  induction β generalizing x with
  | nil => simp
  | cons b β ih =>
    obtain ⟨_ | _, m, y⟩ := b <;> rw [pushArgs_cons, ih] <;> simp [mul_assoc, mul_comm]

/-! ### The count of an atom -/

variable [DecidableEq α]

/-- The count of the atom `a` in a category ([van-benthem-1986]) adds `1` for each occurrence in
result position and subtracts `1` for each occurrence in argument position, so that every
combinatory rule preserves it (`CCG.Rule.count_eq`). -/
def count (a : α) : Cat α → ℤ
  | .atom b => if b = a then 1 else 0
  | .slash _ x _ y => count a x - count a y

@[simp] theorem count_atom (a b : α) : count a (atom b) = if b = a then 1 else 0 := rfl

@[simp] theorem count_slash (a : α) (s : Edge) (x y : Cat α) (m : Modality) :
    count a (slash s x m y) = count a x - count a y := rfl

@[simp] theorem count_push (a : α) (x : Cat α) (b : Arg α) :
    (x.push b).count a = x.count a - b.cat.count a := rfl

theorem count_pushArgs (a : α) (x : Cat α) (β : List (Arg α)) :
    (x.pushArgs β).count a = x.count a - (β.map (·.cat.count a)).sum := by
  induction β generalizing x with
  | nil => simp
  | cons b β ih =>
    simp only [pushArgs_cons, ih, count_push, List.map_cons, List.sum_cons]
    omega

/-- The count of an atom is the value of the category in the integers when that atom has value
`1` and every other atom `0`. -/
theorem ofAdd_count (a : α) (c : Cat α) :
    Multiplicative.ofAdd (c.count a) =
      c.eval fun b ↦ Multiplicative.ofAdd (if b = a then (1 : ℤ) else 0) := by
  induction c with
  | atom b => rfl
  | slash s x m y ihx ihy =>
    cases s <;> simp [← ihx, ← ihy, sub_eq_add_neg, ofAdd_add, ofAdd_neg, mul_comm]

end Cat

/-! ### Rules -/

variable {R : RuleSystem α}

/-- A harmonic rule multiplies the values of its daughters, in any group. -/
theorem Rule.eval_eq {G : Type*} [Group G] (v : α → G) {l r c : Cat α} (ru : Rule R l r c)
    (h : ru.IsHarmonic) : c.eval v = l.eval v * r.eval v := by
  cases ru with
  | forward β _ => simp [Cat.eval_pushArgs_of_right v _ h, mul_assoc]
  | backward β _ => simp [Cat.eval_pushArgs_of_left v _ h, mul_assoc]

/-- Every rule, harmonic or crossing, multiplies the values of its daughters in a commutative
group. -/
theorem Rule.eval_eq_of_comm {G : Type*} [CommGroup G] (v : α → G) {l r c : Cat α}
    (ru : Rule R l r c) : c.eval v = l.eval v * r.eval v := by
  cases ru <;> simp [Cat.eval_pushArgs_of_comm, mul_assoc, mul_comm, mul_left_comm]

theorem Rule.count_eq [DecidableEq α] (a : α) {l r c : Cat α} (ru : Rule R l r c) :
    c.count a = l.count a + r.count a :=
  Multiplicative.ofAdd.injective <| by
    simp only [ofAdd_add, Cat.ofAdd_count]
    exact ru.eval_eq_of_comm _

/-! ### Derivations -/

namespace Derivation

variable {W : Cat α → Type*}

/-- The category of a harmonic derivation has, in any group, the ordered product of the values
of its leaves' categories. -/
theorem eval_eq_prod_cats {G : Type*} [Group G] (v : α → G) {c : Cat α} :
    ∀ d : Derivation W R c, d.IsHarmonic → c.eval v = (d.cats.map (Cat.eval v)).prod
  | .lex _ _, _ => by simp [cats]
  | .node ru d₁ d₂, h => by
    rw [ru.eval_eq v h.1, eval_eq_prod_cats v d₁ h.2.1, eval_eq_prod_cats v d₂ h.2.2, cats,
      List.map_append, List.prod_append]

/-- In a commutative group the category of every derivation has the product of the values of
its leaves' categories. -/
theorem eval_eq_prod_cats_of_comm {G : Type*} [CommGroup G] (v : α → G) {c : Cat α} :
    ∀ d : Derivation W R c, c.eval v = (d.cats.map (Cat.eval v)).prod
  | .lex _ _ => by simp [cats]
  | .node ru d₁ d₂ => by
    rw [ru.eval_eq_of_comm v, eval_eq_prod_cats_of_comm v d₁, eval_eq_prod_cats_of_comm v d₂,
      cats, List.map_append, List.prod_append]

/-- The count invariant of [van-benthem-1986]. A derivation's category has the count of its
leaves, so a string whose lexical counts do not sum to the count of a category has no derivation
of that category from the lexicon, whatever the rule system. -/
theorem count_eq_sum [DecidableEq α] (a : α) {L : List (T × Cat α)} {f : T → ℤ}
    (hL : ∀ p ∈ L, p.2.count a = f p.1) {c : Cat α} :
    ∀ d : Derivation (fun _ ↦ T) R c, d.LexIn L → c.count a = (d.yield.map f).sum
  | .lex c w, h => by simpa [yield] using hL (w, c) h
  | .node ru d₁ d₂, h => by
    rw [ru.count_eq a, count_eq_sum a hL d₁ (show d₁.LexIn L ∧ d₂.LexIn L from h).1,
      count_eq_sum a hL d₂ (show d₁.LexIn L ∧ d₂.LexIn L from h).2, yield, List.map_append,
      List.sum_append]

end Derivation

end CCG
