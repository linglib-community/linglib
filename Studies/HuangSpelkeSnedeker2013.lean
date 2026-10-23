module

public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# Huang, Spelke and Snedeker (2013): What exactly do numbers mean?

Huang, Spelke and Snedeker ask whether number words have exact or lower-bounded semantics by
cancelling the scalar implicature that would otherwise supply the upper bound. A trial shows two
visible boxes and a covered one, and the instruction is a definite description such as *the box
with two fish*. Its referent under a reading of the term is the visible box satisfying it when
exactly one does, the covered box when none does, and no box when both do (`choice`). Adults and
two- to three-year-olds took the total set for *some* and the covered box for *two*.

Two-knowers, children who give one and two but a handful for larger numerals in Wynn's Give-N
task, are the population for which the lower-bounded account has no implicature to offer, the
developmental strategy of Musolino.

## Main results

* `choice_exact_covered`, `choice_atLeast_visible`: in the critical trials an exact *two* sends
  the participant to the covered box and a lower-bounded *two* to the visible one.
* `some_none_all_literal`, `some_none_all_strengthened`: literal *some* picks the box where
  Cookie Monster has all of the cookies, strengthened *some* the covered box.
* `exhKnown_last`, `exhKnown_of_lt`: exhaustifying *two* against a known count list leaves it
  lower-bounded when it is the top of the list and makes it exact otherwise.
* `atLeast_diff_moreThan_eq_bare`: an implicit alternative *more than two* recovers exactness.

## Implementation notes

* Scalar trials are typed by the vertices of the triangle of opposition (`Aristotelian.Triangle`),
  a box showing Cookie Monster with none, some but not all, or all of the cookies; number trials
  by the cardinality of a box.
* The choice proportions and the statistics stay in prose: the paradigm's predictions are
  categorical, and the paper's argument is that the majority choice identifies the reading.

## References

* [huang-spelke-snedeker-2013]
* [wynn-1992]
* [musolino-2004]
-/

@[expose] public section

namespace HuangSpelkeSnedeker2013

open Numerals Degree

/-! ### The covered-box task -/

/-- A covered-box trial shows two visible boxes with contents of type `α` beside a covered box. -/
structure Trial (α : Type*) where
  left : α
  right : α

/-- What the participant hands over. -/
inductive Choice (α : Type*) where
  | visible (x : α)
  | covered
  deriving DecidableEq

variable {α : Type*} (R : α → Prop) [DecidablePred R] (t : Trial α)

/-- The referent of the definite description under a reading `R` of the term is the visible box
satisfying `R` when exactly one does, the covered box when none does, and no box when both do,
since the description presupposes a unique referent. -/
def choice : Option (Choice α) :=
  if R t.left then if R t.right then none else some (.visible t.left)
  else if R t.right then some (.visible t.right) else some .covered

theorem choice_eq_none_iff : choice R t = none ↔ R t.left ∧ R t.right := by
  unfold choice; split_ifs <;> simp_all

theorem choice_eq_covered_iff : choice R t = some .covered ↔ ¬ R t.left ∧ ¬ R t.right := by
  unfold choice; split_ifs <;> simp_all

theorem choice_eq_visible_left_iff :
    choice R t = some (.visible t.left) ↔ R t.left ∧ ¬ R t.right := by
  unfold choice
  split_ifs with h₁ h₂ h₂ <;> simp only [h₁, h₂, Option.some.injEq, Choice.visible.injEq,
    reduceCtorEq, not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, iff_false]
  exact fun h ↦ h₁ (h ▸ h₂)

theorem choice_eq_visible_right_iff :
    choice R t = some (.visible t.right) ↔ ¬ R t.left ∧ R t.right := by
  unfold choice
  split_ifs with h₁ h₂ h₂ <;> simp only [h₁, h₂, Option.some.injEq, Choice.visible.injEq,
    reduceCtorEq, not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, iff_false]
  exact fun h ↦ h₂ (h ▸ h₁)

/-- Strengthening the reading can only move the referent to the covered box or resolve a tie,
which is the design of Section 1.4. -/
theorem choice_covered_of_le {R' : α → Prop} [DecidablePred R'] (h : ∀ x, R' x → R x)
    (hc : choice R t = some .covered) : choice R' t = some .covered := by
  rw [choice_eq_covered_iff] at hc ⊢
  exact ⟨mt (h _) hc.1, mt (h _) hc.2⟩

/-! ### Number trials -/

theorem choice_exact_covered {m a b : ℕ} (ha : a < m) (hb : m < b) :
    choice (· ∈ Comparison.eq.interval m) ⟨a, b⟩ = some .covered :=
  (choice_eq_covered_iff _ _).2 ⟨by simp; omega, by simp; omega⟩

theorem choice_atLeast_visible {m a b : ℕ} (ha : a < m) (hb : m ≤ b) :
    choice (· ∈ Comparison.ge.interval m) ⟨a, b⟩ = some (.visible b) :=
  (choice_eq_visible_right_iff _ _).2 ⟨by simp; omega, by simp; omega⟩

theorem choice_exhNumeral_covered {m a b : ℕ} (ha : a < m) (hb : m < b) :
    choice (· ∈ exhNumeral m) ⟨a, b⟩ = some .covered :=
  (choice_eq_covered_iff _ _).2
    ⟨by simp only [exhNumeral_eq, Comparison.interval_eq, Set.mem_singleton_iff]; omega,
      by simp only [exhNumeral_eq, Comparison.interval_eq, Set.mem_singleton_iff]; omega⟩

/-- In two(1,2) an exact match is visible against a smaller set, and both readings pick it. -/
theorem choice_one_two_bare :
    choice (· ∈ Comparison.eq.interval 2) ⟨1, 2⟩ = some (.visible 2) := by decide

theorem choice_one_two_atLeast :
    choice (· ∈ Comparison.ge.interval 2) ⟨1, 2⟩ = some (.visible 2) := by
  decide

theorem choice_two_three_bare :
    choice (· ∈ Comparison.eq.interval 2) ⟨2, 3⟩ = some (.visible 2) := by decide

theorem choice_two_three_atLeast : choice (· ∈ Comparison.ge.interval 2) ⟨2, 3⟩ = none := by decide

theorem choice_two_three_exh : choice (· ∈ exhNumeral 2) ⟨2, 3⟩ = some (.visible 2) := by decide

theorem choice_one_three_bare : choice (· ∈ Comparison.eq.interval 2) ⟨1, 3⟩ = some .covered :=
  choice_exact_covered (by omega) (by omega)

theorem choice_one_three_atLeast :
    choice (· ∈ Comparison.ge.interval 2) ⟨1, 3⟩ = some (.visible 3) :=
  choice_atLeast_visible (by omega) (by omega)

theorem choice_one_five_atLeast :
    choice (· ∈ Comparison.ge.interval 2) ⟨1, 5⟩ = some (.visible 5) :=
  choice_atLeast_visible (by omega) (by omega)

/-! ### Scalar trials

A box's vertex of the triangle of opposition records whether Cookie Monster has none of the
cookies (`E`), some but not all of them (`IO`), or all (`A`). On the scale the vertices form,
literal *some* holds above the bottom, *all* at the top, and *some* strengthened by its
implicature *not all* strictly between. -/

open Aristotelian

/-- Literal *some* holds above the bottom vertex. -/
abbrev someLiteral : Triangle → Prop := (⊥ < ·)

/-- *All* holds at the top vertex. -/
abbrev allLiteral : Triangle → Prop := (· = ⊤)

/-- *Some* strengthened by *not all* holds strictly between the bottom and top vertices. -/
abbrev someStrengthened : Triangle → Prop := fun t ↦ ⊥ < t ∧ t < ⊤

theorem some_none_some : choice someLiteral ⟨.E, .IO⟩ = some (.visible .IO) := by
  decide

theorem some_some_all_literal : choice someLiteral ⟨.IO, .A⟩ = Option.none := by decide

theorem some_some_all_strengthened :
    choice someStrengthened ⟨.IO, .A⟩ = some (.visible .IO) := by decide

theorem some_none_all_literal : choice someLiteral ⟨.E, .A⟩ = some (.visible .A) := by
  decide

theorem some_none_all_strengthened : choice someStrengthened ⟨.E, .A⟩ = some .covered := by
  decide

theorem all_none_all : choice allLiteral ⟨.E, .A⟩ = some (.visible .A) := by decide

theorem all_some_all : choice allLiteral ⟨.IO, .A⟩ = some (.visible .A) := by decide

theorem all_some_none : choice allLiteral ⟨.IO, .E⟩ = some .covered := by decide

/-! ### Two-knowers -/

/-- A child at knower level `k` has the numerals up to `k` as a count list; the numeral `i` of
that list exhaustified against its known stronger alternatives. -/
def exhKnown (k : ℕ) (i : Fin (k + 1)) (n : ℕ) : Prop :=
  Exhaustification.exhAgainst (· < ·) (fun j : Fin (k + 1) ↦ n ∈ Comparison.ge.interval (j : ℕ)) i

instance (k : ℕ) (i : Fin (k + 1)) : DecidablePred (exhKnown k i) := fun _ ↦
  inferInstanceAs (Decidable (Exhaustification.exhAgainst _ _ _))

/-- The top of the count list has no stronger known alternative, so exhaustification leaves its
lower-bounded meaning as it is. -/
theorem exhKnown_last (k n : ℕ) :
    exhKnown k (Fin.last k) n ↔ n ∈ Comparison.ge.interval k :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun j hj ↦ absurd hj (not_lt.2 (Fin.le_last j))⟩⟩

theorem exhKnown_of_lt {k : ℕ} {i : Fin (k + 1)} (hi : i < Fin.last k) (n : ℕ) :
    exhKnown k i n ↔ n ∈ Comparison.eq.interval (i : ℕ) := by
  have hs : (i : ℕ) + 1 < k + 1 := by have := Fin.lt_def.1 hi; simp at this; omega
  rw [exhKnown, Exhaustification.exhAgainst_lt_iff_succ (s := (⟨i + 1, hs⟩ : Fin (k + 1)))
    (A := fun j : Fin (k + 1) ↦ n ∈ Comparison.ge.interval (j : ℕ))
    (fun j k hjk (hk : (k : ℕ) ≤ n) ↦ show (j : ℕ) ≤ n from le_trans hjk hk)
    (Fin.lt_def.2 (Nat.lt_succ_self _))
    (fun j hj ↦ Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj)))]
  simp only [Comparison.interval_ge, Comparison.interval_eq, Set.mem_Ici, Set.mem_singleton_iff]
  omega

theorem twoKnower_lowerBounded : choice (exhKnown 2 (Fin.last 2)) ⟨1, 3⟩ = some (.visible 3) := by
  decide

theorem threeKnower_exact : choice (exhKnown 3 2) ⟨1, 3⟩ = some .covered := by decide

/-- An implicit alternative *more than two* would exhaustify *two* to its exact meaning, the
route Section 6.1 leaves logically open. -/
theorem atLeast_diff_moreThan_eq_bare (m : ℕ) :
    Comparison.ge.interval m \ Comparison.gt.interval m = Comparison.eq.interval m := by
  simp

end HuangSpelkeSnedeker2013
