/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Sublists
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Abel

/-!
# Slicing, splitting and counting `Multiset.powerset`

`powersetCard n` as a slice of `powerset`, sums over the splits `l.sublists'.revzip` of a list,
and the multiplicity of `s` in `t.powerset` as a product of binomial coefficients: a
sub-multiset picks `s.count x` of the `t.count x` copies of each distinct `x`. (This product of
binomials is not `Nat.multinomial`, which is the quotient `(∑ᵢ kᵢ)! / ∏ᵢ kᵢ!`.)

## Main results

* `Multiset.powersetCard_eq_filter`: `powersetCard n` is the `n`-element slice of `powerset`.
* `Multiset.bind_revzip_sublists'_swap`, `Multiset.bind_revzip_sublists'_assoc`: the splits of a
  list are symmetric, and nested splits reassociate.
* `Multiset.count_powerset_of_le`: for `s ≤ t`,
  `t.powerset.count s = ∏ x ∈ t.toFinset, (t.count x).choose (s.count x)`.

## Implementation notes

The count is proved over a fixed ambient `Finset` containing both supports
(`count_powerset_subset`), so the index set stays constant through the induction.
-/

@[expose] public section

namespace Multiset

variable {α : Type*}

/-- `powersetCard n s` is the slice of `powerset s` with `n` elements
(`Finset.powersetCard_eq_filter` analogue). -/
theorem powersetCard_eq_filter {n : ℕ} {s : Multiset α} :
    powersetCard n s = s.powerset.filter fun t ↦ card t = n := by
  induction s using Multiset.induction generalizing n with
  | empty => cases n <;> simp [powersetCard_zero_left, filter_singleton]
  | cons a s ih =>
    cases n with
    | zero => simp [powersetCard_zero_left, filter_map, ← ih]
    | succ n => simp [powersetCard_cons, filter_map, ← ih]

/-! ### Sums over `sublists'.revzip` -/

/-- Swapping the two buckets of every split enumerates the same splits. -/
theorem bind_revzip_sublists'_swap {β : Type*} (l : List α)
    (F : List α → List α → Multiset β) :
    (l.sublists'.revzip : Multiset (List α × List α)).bind (fun p => F p.1 p.2) =
      (l.sublists'.revzip : Multiset (List α × List α)).bind fun p => F p.2 p.1 := by
  conv_rhs => rw [← Multiset.coe_reverse, List.reverse_revzip, ← List.revzip_swap,
    ← Multiset.map_coe, Multiset.bind_map]
  rfl

/-- Nested splits reassociate. Splitting the second bucket of every split enumerates the same
ordered triples as splitting the first bucket. -/
theorem bind_revzip_sublists'_assoc {β : Type*} (l : List α)
    (K : List α → List α → List α → Multiset β) :
    (l.sublists'.revzip : Multiset (List α × List α)).bind (fun p =>
        (p.2.sublists'.revzip : Multiset (List α × List α)).bind fun q => K p.1 q.1 q.2) =
      (l.sublists'.revzip : Multiset (List α × List α)).bind fun p =>
        (p.1.sublists'.revzip : Multiset (List α × List α)).bind fun q => K q.1 q.2 p.2 := by
  induction l generalizing K with
  | nil => simp
  | cons a l ih =>
    simp only [List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind,
      ← Multiset.map_coe, Multiset.bind_map, Prod.map_fst, Prod.map_snd, id_eq,
      Multiset.bind_add]
    rw [ih fun r r' s => K r r' (a :: s), ih fun r r' s => K r (a :: r') s,
      ih fun r r' s => K (a :: r) r' s, add_assoc]

theorem bind_bind_bind_comm {β γ δ : Type*} (m : Multiset α) (n : α → Multiset β)
    (o : Multiset γ) (f : α → β → γ → Multiset δ) :
    (m.bind fun a => (n a).bind fun b => o.bind fun c => f a b c) =
      o.bind fun c => m.bind fun a => (n a).bind fun b => f a b c :=
  (Multiset.bind_congr fun a _ => Multiset.bind_bind (n a) o).trans (Multiset.bind_bind m o)

theorem bind_revzip_sublists'_bind_assoc {β γ : Type*} (l : List α) (S : List α → Multiset β)
    (F : β → List α → List α → Multiset γ) :
    (l.sublists'.revzip : Multiset (List α × List α)).bind (fun p => (S p.1).bind fun a =>
        (p.2.sublists'.revzip : Multiset (List α × List α)).bind fun q => F a q.1 q.2) =
      (l.sublists'.revzip : Multiset (List α × List α)).bind fun q =>
        (q.2.sublists'.revzip : Multiset (List α × List α)).bind fun q' =>
          (S q'.1).bind fun a => F a q.1 q'.2 := by
  induction l generalizing S F with
  | nil => simp
  | cons x l ih =>
    simp only [List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind,
      ← Multiset.map_coe, Multiset.bind_map, Prod.map_fst, Prod.map_snd, id_eq,
      Multiset.bind_add]
    rw [ih S fun a r s => F a r (x :: s), ih S fun a r s => F a (x :: r) s,
      ih (fun r => S (x :: r)) F, add_right_comm]

theorem bind_revzip_sublists'_bind_assoc' {β γ : Type*} (l : List α)
    (S : List α → Multiset β)
    (F : β → List α → List α → Multiset γ) :
    (l.sublists'.revzip : Multiset (List α × List α)).bind (fun p => (S p.1).bind fun a =>
        (p.2.sublists'.revzip : Multiset (List α × List α)).bind fun q => F a q.1 q.2) =
      (l.sublists'.revzip : Multiset (List α × List α)).bind fun q =>
        (q.1.sublists'.revzip : Multiset (List α × List α)).bind fun q' =>
          (S q'.1).bind fun a => F a q'.2 q.2 := by
  rw [bind_revzip_sublists'_swap l fun x y =>
      (x.sublists'.revzip : Multiset (List α × List α)).bind fun q' =>
        (S q'.1).bind fun a => F a q'.2 y,
    ← bind_revzip_sublists'_bind_assoc l S fun a r s => F a s r]
  exact Multiset.bind_congr fun p _ => Multiset.bind_congr fun a _ =>
    bind_revzip_sublists'_swap p.2 fun r s => F a r s

variable [DecidableEq α]

private theorem count_powerset_subset {S : Finset α} {t s : Multiset α} (ht : t.toFinset ⊆ S)
    (hs : s.toFinset ⊆ S) : t.powerset.count s = ∏ x ∈ S, (t.count x).choose (s.count x) := by
  induction t using Multiset.induction_on generalizing s hs with
  | empty =>
    rw [powerset_zero, count_singleton]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨x, hx⟩ := exists_mem_of_ne_zero h
      symm
      rw [← Finset.mul_prod_erase S _ (hs (mem_toFinset.mpr hx)), count_zero,
          Nat.choose_eq_zero_of_lt (count_pos.mpr hx), Nat.zero_mul]
  | cons a t' ih =>
    have haS : a ∈ S := ht (mem_toFinset.mpr (mem_cons_self a t'))
    have ht' : t'.toFinset ⊆ S := (toFinset_subset.mpr (subset_cons t' a)).trans ht
    have hQ : ∏ x ∈ S.erase a, ((a ::ₘ t').count x).choose (s.count x)
        = ∏ x ∈ S.erase a, (t'.count x).choose (s.count x) :=
      Finset.prod_congr rfl fun x hx => by
        rw [count_cons_of_ne (Finset.ne_of_mem_erase hx)]
    rw [powerset_cons, count_add, ih ht' hs,
        ← Finset.mul_prod_erase S (fun x => ((a ::ₘ t').count x).choose (s.count x)) haS,
        ← Finset.mul_prod_erase S (fun x => (t'.count x).choose (s.count x)) haS,
        count_cons_self, hQ]
    by_cases has : a ∈ s
    · have hs' : (s.erase a).toFinset ⊆ S := (toFinset_subset.mpr (erase_subset a s)).trans hs
      have hmap : (t'.powerset.map (Multiset.cons a)).count s
          = t'.powerset.count (s.erase a) := by
        conv_lhs => rw [← cons_erase has]
        exact count_map_eq_count' _ _ (fun _ _ h => (cons_inj_right a).mp h) _
      have hR : ∏ x ∈ S.erase a, (t'.count x).choose ((s.erase a).count x)
          = ∏ x ∈ S.erase a, (t'.count x).choose (s.count x) :=
        Finset.prod_congr rfl fun x hx => by
          rw [count_erase_of_ne (Finset.ne_of_mem_erase hx)]
      rw [hmap, ih ht' hs',
          ← Finset.mul_prod_erase S (fun x => (t'.count x).choose ((s.erase a).count x)) haS,
          count_erase_self, hR, Nat.choose_succ_left _ _ (count_pos.mpr has),
          ← Nat.add_mul, Nat.add_comm ((t'.count a).choose (s.count a))]
    · have hmap : (t'.powerset.map (Multiset.cons a)).count s = 0 :=
        count_eq_zero.mpr fun hmem => by
          obtain ⟨u, -, rfl⟩ := mem_map.mp hmem
          exact has (mem_cons_self a u)
      rw [hmap, count_eq_zero.mpr has]
      simp

/-- Count of a sub-multiset `s ≤ t` among the sub-multisets of `t`: for each distinct
    `x`, choose `s.count x` of the `t.count x` copies. -/
theorem count_powerset_of_le {s t : Multiset α} (h : s ≤ t) :
    t.powerset.count s = ∏ x ∈ t.toFinset, (t.count x).choose (s.count x) :=
  count_powerset_subset Finset.Subset.rfl (toFinset_subset.mpr (subset_of_le h))

@[simp] theorem count_zero_powerset (t : Multiset α) : t.powerset.count 0 = 1 := by
  rw [count_powerset_of_le (zero_le t)]
  simp

@[simp] theorem count_powerset_self (t : Multiset α) : t.powerset.count t = 1 := by
  rw [count_powerset_of_le le_rfl]
  simp

end Multiset
