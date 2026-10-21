/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs

/-!
# Alignment constraints

This file defines Generalized Alignment, the constraint family requiring each constituent of one
category to share an edge with a constituent of another, assessed categorically.
`Constraint.align R` scores a pair of constituent families with one violation for each member of
the first family that bears `R` to no member of the second. Over the spans of a tree's
constituents (`RoseTree.spans`), `R` comparing right edges gives Align-R, comparing left edges
Align-L, and equality gives the Match constraints of Match Theory, which require both edges to
coincide with those of one constituent of the other family. `Constraint.deficiency R` counts
instead the members left without a partner when partners must be distinct, the MAX of a one-to-one
correspondence. A constraint on candidates of another type is the `Constraint.comap` of either
along the candidate's two families.

## Main definitions

* `Constraint.align`: Generalized Alignment of one family of constituents to another along `R`.
* `Constraint.alignLeft`, `Constraint.alignRight`: Align-L and Align-R over spans, the edges
  compared at their left or their right cut.
* `Constraint.matchingNumber`: the most members of one family pairable with distinct members of
  another along `R`.
* `Constraint.deficiency`: the members of the first family that every one-to-one correspondence
  along `R` leaves without a correspondent.

## Main results

* `Constraint.align_eq_zero_iff`: a pair satisfies `align R` iff each member of the first family
  bears `R` to a member of the second.
* `Constraint.deficiency_le_align`: correspondence along `R` demands no more than alignment along
  a relation contained in `R` that pairs no two members with one, as identity does Match.

## References

* [mccarthy-prince-1993b]
* [mccarthy-prince-1995]
* [selkirk-2011]
-/

@[expose] public section

namespace OptimalityTheory.Constraint

variable {β γ : Type*} (R : β → γ → Prop) [DecidableRel R]

/-- **Generalized Alignment** ([mccarthy-prince-1993b]) of one family of constituents to another
along `R`, assessed categorically: one violation for each member of the first family that bears
`R` to no member of the second. On spans, `R` comparing right or left edges is Align-R or
Align-L, and equality is the Match constraint ([selkirk-2011]). -/
def align : Constraint (List β × List γ) := fun x ↦ x.1.countP fun a ↦ ∀ b ∈ x.2, ¬ R a b

variable {R}

theorem align_eq_zero_iff {x : List β × List γ} : align R x = 0 ↔ ∀ a ∈ x.1, ∃ b ∈ x.2, R a b := by
  simp [align, List.countP_eq_zero]

/-- **Align-L** over spans, `Align(Cat₁, L, Cat₂, L)` ([mccarthy-prince-1993b]): one violation for
each span of the first family whose left cut begins no span of the second. -/
abbrev alignLeft : Constraint (List (ℕ × ℕ) × List (ℕ × ℕ)) := align fun a b ↦ a.1 = b.1

/-- **Align-R** over spans, `Align(Cat₁, R, Cat₂, R)` ([mccarthy-prince-1993b]): one violation for
each span of the first family whose right cut ends no span of the second. -/
abbrev alignRight : Constraint (List (ℕ × ℕ) × List (ℕ × ℕ)) := align fun a b ↦ a.2 = b.2

-- A phrase over two words is right-aligned with the second word, not left-aligned with it, and
-- matches neither.
example : alignRight ([(0, 2)], [(0, 1), (1, 2)]) = 0 := by decide
example : alignLeft ([(1, 2)], [(0, 2)]) = 1 := by decide
example : align Eq ([(0, 2)], [(0, 1), (1, 2)]) = 1 := by decide

/-! ### One-to-one correspondence -/

section Deficiency

private theorem le_foldr {f : γ → ℕ → ℕ} (hf : ∀ b n, n ≤ f b n) (m : List γ) (k : ℕ) :
    k ≤ m.foldr f k := by
  induction m with
  | nil => rfl
  | cons b m ih => exact ih.trans (hf b _)

private theorem le_foldr_of_mem {f : γ → ℕ → ℕ} (hf : ∀ b n, n ≤ f b n) {m : List γ} {b : γ}
    (hb : b ∈ m) {k j : ℕ} (hj : ∀ n, j ≤ f b n) : j ≤ m.foldr f k := by
  induction m with
  | nil => simp at hb
  | cons c m ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hj _
    · exact (ih hb).trans (hf c _)

variable (R) [DecidableEq γ]

/-- The **matching number** of `R` between two lists: the most members of the first that can be
paired with distinct members of the second they bear `R` to. The first member is either left
unpaired or paired with some member of the second list, which is then no longer available. -/
def matchingNumber : List β → List γ → ℕ
  | [], _ => 0
  | a :: l, m => m.foldr (fun b n ↦ if R a b then max n (matchingNumber l (m.erase b) + 1) else n)
      (matchingNumber l m)

/-- **Correspondence** along `R` with no member of the second family answering to two of the
first, MAX under UNIFORMITY ([mccarthy-prince-1995]): one violation for each member of the first
family left without a correspondent by the best such correspondence, the deficiency of `R`. -/
def deficiency : Constraint (List β × List γ) := fun x ↦ x.1.length - matchingNumber R x.1 x.2

variable {R}

private theorem foldr_le_self (a : β) (l : List β) (m : List γ) (b : γ) (n : ℕ) :
    n ≤ (if R a b then max n (matchingNumber R l (m.erase b) + 1) else n) := by
  split_ifs <;> simp

theorem matchingNumber_le_cons (a : β) (l : List β) (m : List γ) :
    matchingNumber R l m ≤ matchingNumber R (a :: l) m :=
  le_foldr (foldr_le_self a l m) m _

theorem matchingNumber_erase_lt_cons {a : β} {b : γ} {m : List γ} (hb : b ∈ m) (h : R a b)
    (l : List β) : matchingNumber R l (m.erase b) < matchingNumber R (a :: l) m :=
  le_foldr_of_mem (foldr_le_self a l m) hb fun _ ↦ by simp [h]

/-- The members of a duplicate-free list bearing `S` to a member of another are pairable with
distinct members of it along `R`, where `S` is contained in `R` and no two members bear `S` to one
member. -/
theorem countP_le_matchingNumber {S : β → γ → Prop} [DecidableRel S] {l : List β} (hl : l.Nodup)
    (hSR : ∀ a ∈ l, ∀ b, S a b → R a b) (hS : ∀ a ∈ l, ∀ a' ∈ l, ∀ b, S a b → S a' b → a = a')
    (m : List γ) : l.countP (fun a ↦ ∃ b ∈ m, S a b) ≤ matchingNumber R l m := by
  induction l generalizing m with
  | nil => simp [matchingNumber]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hl
    have ih := ih hl (fun a' h ↦ hSR a' (List.mem_cons_of_mem a h))
      fun a' h a'' h' ↦ hS a' (List.mem_cons_of_mem a h) a'' (List.mem_cons_of_mem a h')
    by_cases h : ∃ b ∈ m, S a b
    · obtain ⟨b, hb, hab⟩ := h
      have he : l.countP (fun a' ↦ ∃ b' ∈ m.erase b, S a' b') =
          l.countP (fun a' ↦ ∃ b' ∈ m, S a' b') := List.countP_congr fun a' ha' ↦ by
        simp only [decide_eq_true_eq]
        refine ⟨fun ⟨b', hb', h'⟩ ↦ ⟨b', List.mem_of_mem_erase hb', h'⟩, fun ⟨b', hb', h'⟩ ↦
          ⟨b', (List.mem_erase_of_ne ?_).2 hb', h'⟩⟩
        rintro rfl
        exact ha (hS a' (List.mem_cons_of_mem a ha') a List.mem_cons_self b' h' hab ▸ ha')
      have := matchingNumber_erase_lt_cons hb (hSR a List.mem_cons_self b hab) l
      have := ih (m.erase b)
      have hd : decide (∃ b ∈ m, S a b) = true := decide_eq_true ⟨b, hb, hab⟩
      rw [List.countP_cons, ite_eq_left hd]
      omega
    · simp only [List.countP_cons, decide_eq_false h]
      exact (ih m).trans (matchingNumber_le_cons a l m)

/-- **Correspondence asks no more than alignment along a stricter relation**: where `S` is
contained in `R` and no two members of a duplicate-free family bear `S` to one member, the members
left without a correspondent along `R` are among those bearing `S` to none. -/
theorem deficiency_le_align {S : β → γ → Prop} [DecidableRel S] {x : List β × List γ}
    (hx : x.1.Nodup) (hSR : ∀ a ∈ x.1, ∀ b, S a b → R a b)
    (hS : ∀ a ∈ x.1, ∀ a' ∈ x.1, ∀ b, S a b → S a' b → a = a') : deficiency R x ≤ align S x := by
  have h₁ := countP_le_matchingNumber hx hSR hS x.2
  have h₂ := List.length_eq_countP_add_countP (fun a ↦ decide (∃ b ∈ x.2, S a b)) (l := x.1)
  have h₃ : align S x = x.1.countP fun a ↦ ¬ decide (∃ b ∈ x.2, S a b) :=
    List.countP_congr fun a _ ↦ by simp
  simp only [deficiency, h₃]
  omega

end Deficiency

-- Two words overlapping one phrase cannot both have it as correspondent, though both align to it.
example : align (fun a p : ℕ × ℕ ↦ a.1 < p.2 ∧ p.1 < a.2) ([(0, 1), (1, 2)], [(0, 2)]) = 0 := by
  decide
example : deficiency (fun a p : ℕ × ℕ ↦ a.1 < p.2 ∧ p.1 < a.2) ([(0, 1), (1, 2)], [(0, 2)])
    = 1 := by
  decide

end OptimalityTheory.Constraint
