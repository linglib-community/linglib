/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Perm.Subperm

/-!
# The matching number of a relation between two lists

A matching of `R : α → β → Prop` between lists `l` and `m` pairs members of `l` with distinct
members of `m` related to them: a sublist of `l` related pointwise by `List.Forall₂ R` to a
subpermutation of `m`. `List.matchingNumber R l m` is the size of a largest matching.

## Main definitions

* `List.matchingNumber`: the size of a largest matching of `R` between two lists.

## Main results

* `List.le_matchingNumber_iff`: `R` has a matching of size `k` iff `k ≤ matchingNumber R l m`.
* `List.countP_le_matchingNumber`: the members of a duplicate-free list bearing a relation
  contained in `R`, and injective, to members of `m` are pairable.
-/

@[expose] public section

namespace List

variable {α β : Type*}

section MatchingNumber

variable (R : α → β → Prop) [DecidableRel R] [DecidableEq β]

/-- The **matching number** of `R` between `l` and `m`, the most members of `l` that can be paired
along `R` with distinct members of `m`. The head of `l` is either unpaired or paired with a member
of `m`, which is then no longer available. -/
def matchingNumber : List α → List β → ℕ
  | [], _ => 0
  | a :: l, m => max (matchingNumber l m)
      ({b ∈ m.toFinset | R a b}.sup fun b ↦ matchingNumber l (m.erase b) + 1)

variable {R} {l : List α} {m : List β}

@[simp] theorem matchingNumber_nil (m : List β) : matchingNumber R [] m = 0 := rfl

theorem matchingNumber_cons (a : α) (l : List α) (m : List β) :
    matchingNumber R (a :: l) m = max (matchingNumber R l m)
      ({b ∈ m.toFinset | R a b}.sup fun b ↦ matchingNumber R l (m.erase b) + 1) := rfl

/-- `R` has a matching of size `k` between `l` and `m`, a sublist of `l` of length `k` related by
`Forall₂ R` to a subpermutation of `m`, exactly when `k` is at most the matching number. -/
theorem le_matchingNumber_iff {k : ℕ} :
    k ≤ matchingNumber R l m ↔ ∃ l₁ m₁, l₁ <+ l ∧ m₁ <+~ m ∧ Forall₂ R l₁ m₁ ∧ l₁.length = k := by
  induction l generalizing m k with
  | nil =>
    refine ⟨fun h ↦ ⟨[], [], nil_sublist _, nil_subperm, .nil, (Nat.le_zero.1 h).symm⟩, ?_⟩
    rintro ⟨l₁, m₁, hl, -, -, rfl⟩
    simp [sublist_nil.1 hl]
  | cons a l ih =>
    rw [matchingNumber_cons, le_max_iff]
    constructor
    · rintro (h | h)
      · obtain ⟨l₁, m₁, hl, hm, hR, rfl⟩ := ih.1 h
        exact ⟨l₁, m₁, hl.cons a, hm, hR, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨[], [], nil_sublist _, nil_subperm, .nil, rfl⟩
        obtain ⟨b, hb, hkb⟩ := (Finset.le_sup_iff hk).1 h
        rw [Finset.mem_filter, mem_toFinset] at hb
        obtain ⟨l₁, m₁, hl, hm, hR, hlen⟩ := ih.1 (Nat.sub_le_iff_le_add.2 hkb)
        exact ⟨a :: l₁, b :: m₁, hl.cons_cons a,
          ((subperm_cons b).2 hm).trans (perm_cons_erase hb.1).symm.subperm, .cons hb.2 hR,
          by rw [length_cons, hlen]; omega⟩
    · rintro ⟨l₁, m₁, hl, hm, hR, rfl⟩
      rcases sublist_cons_iff.1 hl with hl | ⟨r, rfl, hr⟩
      · exact .inl (ih.2 ⟨l₁, m₁, hl, hm, hR, rfl⟩)
      · obtain ⟨b, m₂, hab, hR₂, rfl⟩ := forall₂_cons_left_iff.1 hR
        have hb : b ∈ m := hm.subset mem_cons_self
        refine .inr (le_trans ?_ (Finset.le_sup (f := fun b ↦ matchingNumber R l (m.erase b) + 1)
          (Finset.mem_filter.2 ⟨mem_toFinset.2 hb, hab⟩)))
        exact Nat.succ_le_succ (ih.2 ⟨r, m₂, hr, by simpa using hm.erase b, hR₂, rfl⟩)

/-- The members of a duplicate-free list bearing `S` to some member of `m` are pairable along `R`,
where `S` is contained in `R` and no two members bear `S` to one member of `m`. -/
theorem countP_le_matchingNumber {S : α → β → Prop} [DecidableRel S] (hl : l.Nodup)
    (hSR : ∀ a ∈ l, ∀ b, S a b → R a b) (hS : ∀ a ∈ l, ∀ a' ∈ l, ∀ b, S a b → S a' b → a = a')
    (m : List β) : l.countP (fun a ↦ ∃ b ∈ m, S a b) ≤ matchingNumber R l m := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := nodup_cons.1 hl
    have ih := ih hl (fun a' h ↦ hSR a' (mem_cons_of_mem a h))
      fun a' h a'' h' ↦ hS a' (mem_cons_of_mem a h) a'' (mem_cons_of_mem a h')
    rw [matchingNumber_cons, countP_cons]
    by_cases h : ∃ b ∈ m, S a b
    · obtain ⟨b, hb, hab⟩ := h
      have he : l.countP (fun a' ↦ ∃ b' ∈ m.erase b, S a' b') =
          l.countP (fun a' ↦ ∃ b' ∈ m, S a' b') := countP_congr fun a' ha' ↦ by
        simp only [decide_eq_true_eq]
        refine ⟨fun ⟨b', hb', h'⟩ ↦ ⟨b', mem_of_mem_erase hb', h'⟩, fun ⟨b', hb', h'⟩ ↦
          ⟨b', (mem_erase_of_ne ?_).2 hb', h'⟩⟩
        rintro rfl
        exact ha (hS a' (mem_cons_of_mem a ha') a mem_cons_self b' h' hab ▸ ha')
      have hle := Finset.le_sup (f := fun b ↦ matchingNumber R l (m.erase b) + 1)
        (Finset.mem_filter.2 ⟨mem_toFinset.2 hb, hSR a mem_cons_self b hab⟩)
      rw [ite_eq_left (decide_eq_true ⟨b, hb, hab⟩)]
      refine le_max_of_le_right (le_trans ?_ hle)
      show _ ≤ matchingNumber R l (m.erase b) + 1
      have := ih (m.erase b)
      omega
    · rw [ite_eq_right (by simpa using h)]
      exact le_max_of_le_left (ih m)

end MatchingNumber

-- Two members related only to one member of the other list: one of them goes unpaired.
example : matchingNumber (fun (a : ℕ) (b : ℕ) ↦ a ≤ b) [0, 1] [1] = 1 := by decide
example : matchingNumber (fun (a : ℕ) (b : ℕ) ↦ a ≤ b) [0, 1] [1, 1] = 2 := by decide

end List
