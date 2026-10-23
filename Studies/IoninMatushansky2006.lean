/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
public import Linglib.Syntax.Category.Numeral.Composition

/-!
# Ionin and Matushansky (2006): The Composition of Complex Cardinals

Ionin and Matushansky treat a simplex cardinal as a modifier of type ⟨⟨e,t⟩,⟨e,t⟩⟩: the cardinal
`n` holds of a plurality with a partition into `n` cells that each satisfy its complement, and a
partition is a `Finpartition`. *Two hundred books* is then iterated modification, so
multiplication needs no rule of its own, in agreement with Hurford's PHRASE projection rule. The
countability presupposition, that the complement denotes pluralities of a single size, is what
makes `n` cells of `k` members count `n * k`. The predicate theory of cardinals fails as §2.2
says, and addition is coordination (§4).

## Main definitions

* `cardMod`: the cardinal as a modifier, (5) with the partitions of (6).
* `Equicardinal`: the countability presupposition (23).
* `coordSem`: coordination of xNPs (52).

## Main results

* `cardMod_atoms_iff`: over the singletons of a set, `n` holds of its `n`-membered pluralities.
* `cardMod_cardMod_atoms`, `iterated_matches_phrase`: iterated modification multiplies.
* `predicate_conjunction_contradictory`, `predicate_theory_undershoots`: the predicate theory
  contradicts itself or undercounts.
* `cardMod_union_of_disjoint`, `no_joint_reading`: coordination adds on the full split, and the
  joint reading is contradictory.

## Implementation notes

Pluralities are finite sets, and the atoms over a set `S` of individuals are its singletons,
`({·} : α → Finset α) '' S`. That the split reading excludes overlap, which the paper attributes
to the maxim of Manner (§4.2.1), is the hypothesis of `cardMod_union_of_disjoint`.

## References

* [ionin-matushansky-2006]
* [hurford-1975]
-/

@[expose] public section

namespace IoninMatushansky2006

open Finset

variable {α : Type*}

/-- The countability presupposition (23) says that a complement denotes pluralities of a single
cardinality `k`. -/
def Equicardinal (P : Finset α → Prop) (k : ℕ) : Prop :=
  ∀ s, P s → #s = k

theorem equicardinal_image_singleton (S : Set α) :
    Equicardinal (· ∈ ({·} : α → Finset α) '' S) 1 := by
  rintro _ ⟨a, -, rfl⟩
  exact card_singleton a

/-- Under predicate conjunction (12), *two hundred books* is contradictory, since no plurality has
two members and a hundred. -/
theorem predicate_conjunction_contradictory (x : Finset α) : ¬ (#x = 2 ∧ #x = 100) := by
  omega

variable [DecidableEq α]

/-! ### The cardinal as a modifier -/

/-- The cardinal `n` as a modifier (5) holds of a plurality with a partition (6) into `n` cells,
each satisfying the complement `P`. -/
def cardMod (n : ℕ) (P : Finset α → Prop) (x : Finset α) : Prop :=
  ∃ Q : Finpartition x, #Q.parts = n ∧ ∀ s ∈ Q.parts, P s

theorem card_of_cardMod {P : Finset α → Prop} {k n : ℕ} {x : Finset α} (hP : Equicardinal P k)
    (h : cardMod n P x) : #x = n * k := by
  obtain ⟨Q, rfl, hQ⟩ := h
  rw [← Q.sum_card_parts, sum_const_nat fun s hs ↦ hP s (hQ s hs)]

theorem cardMod_of_card {P : Finset α → Prop} {k : ℕ} (hk : k ≠ 0) (n : ℕ) {x : Finset α}
    (hP : ∀ y ⊆ x, #y = k → P y) (hx : #x = n * k) : cardMod n P x := by
  have h : n * k + 0 * (k + 1) = #x := by rw [hx, zero_mul, add_zero]
  have hbig := (⊥ : Finpartition x).card_filter_equitabilise_big h
  rw [card_eq_zero, filter_eq_empty_iff] at hbig
  refine ⟨(⊥ : Finpartition x).equitabilise h, by
    rw [Finpartition.card_parts_equitabilise _ _ hk, add_zero], fun t ht ↦ hP t
    (Finpartition.le _ ht) ((Finpartition.card_eq_of_mem_parts_equitabilise ht).resolve_right
    (hbig ht))⟩

/-- *Hundred books* (8) holds of the hundred-membered pluralities of books, since a cardinal over
singletons counts members. -/
theorem cardMod_atoms_iff (n : ℕ) (S : Set α) (x : Finset α) :
    cardMod n (· ∈ ({·} : α → Finset α) '' S) x ↔ #x = n ∧ ↑x ⊆ S := by
  refine ⟨fun h ↦ ⟨by simpa using card_of_cardMod (equicardinal_image_singleton S) h, ?_⟩,
    fun ⟨hn, hx⟩ ↦ ⟨⊥, hn ▸ Finpartition.card_bot x, fun t ht ↦ ?_⟩⟩
  · obtain ⟨Q, -, hQ⟩ := h
    intro a ha
    obtain ⟨t, ht, hat⟩ := Q.exists_mem ha
    obtain ⟨b, hb, rfl⟩ := hQ t ht
    rwa [mem_singleton.1 hat]
  · obtain ⟨a, ha, rfl⟩ := Finpartition.mem_bot_iff.1 ht
    exact ⟨a, hx ha, rfl⟩

/-- *Two hundred books* (9) is iterated modification, which multiplies, so complex cardinals need
no semantic rule beyond composition. -/
theorem cardMod_cardMod_atoms {m : ℕ} (hm : m ≠ 0) (n : ℕ) (S : Set α) (x : Finset α) :
    cardMod n (cardMod m (· ∈ ({·} : α → Finset α) '' S)) x ↔ #x = n * m ∧ ↑x ⊆ S := by
  refine ⟨fun h ↦ ⟨card_of_cardMod (fun s hs ↦ ((cardMod_atoms_iff m S s).1 hs).1) h, ?_⟩,
    fun ⟨hn, hx⟩ ↦ cardMod_of_card hm n (fun y hyx hyc ↦
      (cardMod_atoms_iff m S y).2 ⟨hyc, (coe_subset.2 hyx).trans hx⟩) hn⟩
  obtain ⟨Q, -, hQ⟩ := h
  intro a ha
  obtain ⟨t, ht, hat⟩ := Q.exists_mem ha
  exact ((cardMod_atoms_iff m S t).1 (hQ t ht)).2 hat

/-- Iterated modification computes Hurford's PHRASE projection rule, so `[n m] books` counts
`(Phrase.mk n m).value` members. -/
theorem iterated_matches_phrase (n : Numeral.Number) (m : Numeral.M) (S : Set α)
    (x : Finset α) :
    cardMod n.value (cardMod m.value (· ∈ ({·} : α → Finset α) '' S)) x ↔
      #x = (Numeral.Phrase.mk n m).value ∧ ↑x ⊆ S :=
  cardMod_cardMod_atoms m.value_pos.ne' n.value S x

/-- Under conjoined partition-based predicates (13), scaled to *two four*, a plurality of four
satisfies both conjuncts, where the modifier reading demands eight. -/
theorem predicate_theory_undershoots :
    ∃ x : Finset (Fin 4), cardMod 2 (fun _ ↦ True) x ∧ cardMod 4 (fun _ ↦ True) x ∧ #x = 4 :=
  ⟨univ, cardMod_of_card two_ne_zero 2 (fun _ _ _ ↦ trivial) (by simp),
    cardMod_of_card one_ne_zero 4 (fun _ _ _ ↦ trivial) (by simp), by simp⟩

/-! ### Addition as coordination -/

/-- Coordinated xNPs (52) split the plurality between the two conjuncts. -/
def coordSem (A B : Finset α → Prop) (x : Finset α) : Prop :=
  ∃ y z, x = y ∪ z ∧ A y ∧ B z

/-- On the full split (56b), coordination adds, so *twenty books and two books* holds of
*twenty-two books*. -/
theorem cardMod_union_of_disjoint {S : Set α} {n m : ℕ} {y z : Finset α} (hd : Disjoint y z)
    (hy : cardMod n (· ∈ ({·} : α → Finset α) '' S) y)
    (hz : cardMod m (· ∈ ({·} : α → Finset α) '' S) z) :
    cardMod (n + m) (· ∈ ({·} : α → Finset α) '' S) (y ∪ z) := by
  obtain ⟨rfl, hyS⟩ := (cardMod_atoms_iff _ S y).1 hy
  obtain ⟨rfl, hzS⟩ := (cardMod_atoms_iff _ S z).1 hz
  exact (cardMod_atoms_iff _ S _).2
    ⟨card_union_of_disjoint hd, by rw [coe_union]; exact Set.union_subset hyS hzS⟩

/-- The joint reading (56a) is contradictory for distinct cardinals, since no plurality has `n`
members and `m`. -/
theorem no_joint_reading {S : Set α} {n m : ℕ} (hnm : n ≠ m) (x : Finset α) :
    ¬ (cardMod n (· ∈ ({·} : α → Finset α) '' S) x ∧
      cardMod m (· ∈ ({·} : α → Finset α) '' S) x) := fun ⟨hn, hm⟩ ↦
  hnm (((cardMod_atoms_iff n S x).1 hn).1.symm.trans ((cardMod_atoms_iff m S x).1 hm).1)

end IoninMatushansky2006
