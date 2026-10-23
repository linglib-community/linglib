/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.IntervalCases

/-!
# Number resolution

A target agreeing with all of its conjoined noun phrases takes the number its language gives the
group they form, in Slovene the dual for two singulars and the plural otherwise. Corbett observes
that the values resolution produces match the semantics of number. A system with determinate
values gives a referent of `n` individuals the determinate value of that cardinality if it has
one and the plural otherwise, and the conjuncts denote distinct individuals, so the group's
cardinality is the sum of theirs. When the determinate values form an initial segment of
singular, dual and trial (`Number.System.DeterminateInitial`), the value of the sum depends only
on the values of the parts, so resolution is a function of the conjuncts' numbers. The same
classification gives the number of a target whose system lacks its controller's value, the
plural of a Modern Hebrew verb agreeing with a dual noun.

## Main definitions

* `Number.System.ofCard`: the value a system gives a referent of `n` individuals.
* `Number.System.resolve`: the resolved number of two conjuncts.
* `Number.System.coarsen`: the value a system gives the referent of another system's value.

## Main results

* `Number.System.resolve_ofCard`: in a system whose determinate values are an initial segment,
  conjuncts of `m` and `n` individuals resolve to the value of `m + n`.
* `Number.System.foldl_resolve_ofCard`: any number of conjuncts resolve to the value of the sum
  of their cardinalities.
* `Number.System.resolve_card_union`: conjuncts denoting disjoint pluralities resolve to the
  value of their sum.
* `Number.System.coarsen_ofCard`: a target shows the value of its controller's referent when
  the controller's system has every determinate value of the target's.

## Implementation notes

That resolution is a function of the conjuncts' numbers says that `ofCard`'s kernel is a
congruence for addition on positive cardinalities, the additive counterpart of the person
systems' congruences for union; no consumer reads the quotient, so it is not built. The
approximative values have no fixed cardinality boundary and the minimal and augmented are
relative to person, so neither are classes of cardinalities. `resolve` and `coarsen` send them,
as they send the plural, to the plural; no theorem here reaches them.

## TODO

* Minimal–augmented systems, where the speaker and the addressee, each minimal, sum to the
  minimal inclusive, want person and number resolved together.

## References

* [corbett-1991] §9.1.2, pp. 263–264
* [corbett-2000] §6.1, p. 180; §6.5.2, pp. 198–199
* [corbett-2006] §8.2, pp. 242–243; §8.5.4, p. 257
* [link-1983]
-/

@[expose] public section

namespace Number.System

variable (ns : System)

/-- `ns.ofCard n` is the value a system gives a referent of `n` individuals, the determinate
value of that cardinality if the system has it and the plural otherwise. -/
def ofCard (n : ℕ) : Number :=
  if fromCard n ∈ ns.values then fromCard n else .plural

/-- `ns.resolve a b` is the resolved number of two conjuncts, the value of the sum of their
cardinalities; a conjunct with no fixed cardinality makes it plural. -/
def resolve (a b : Number) : Number :=
  match a.exactCard, b.exactCard with
  | some m, some n => ns.ofCard (m + n)
  | _, _ => .plural

/-- `ns.coarsen v` is the value a system gives the referent of a value `v` of another system,
the value of its cardinality if `v` has one and the plural otherwise. -/
def coarsen (v : Number) : Number :=
  match v.exactCard with
  | some n => ns.ofCard n
  | none => .plural

theorem resolve_comm (a b : Number) : ns.resolve a b = ns.resolve b a := by
  unfold resolve
  cases a.exactCard <;> cases b.exactCard <;> simp [Nat.add_comm]

theorem ofCard_of_three_lt {n : ℕ} (h : 3 < n) : ns.ofCard n = .plural := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp [ofCard, fromCard]

theorem exactCard_ofCard {n : ℕ} (hn : 0 < n) :
    (ns.ofCard n).exactCard = if fromCard n ∈ ns.values ∧ n ≤ 3 then some n else none := by
  by_cases h3 : n ≤ 3
  · interval_cases n <;> simp only [ofCard, fromCard] <;> split_ifs <;> simp_all [exactCard]
  · simp [ofCard_of_three_lt ns (by omega : 3 < n), exactCard, h3]

variable {ns}

theorem resolve_ofCard (h : ns.DeterminateInitial) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ns.resolve (ns.ofCard m) (ns.ofCard n) = ns.ofCard (m + n) := by
  have h₁ : Number.dual ∈ ns.values → Number.singular ∈ ns.values :=
    fun hd ↦ h _ hd 1 (by decide)
  have h₂ : Number.trial ∈ ns.values → Number.dual ∈ ns.values :=
    fun ht ↦ h _ ht 2 (by decide)
  clear h
  rw [resolve, exactCard_ofCard ns hm, exactCard_ofCard ns hn]
  by_cases h4 : 3 < m + n
  · rw [ofCard_of_three_lt ns h4]
    split_ifs <;> simp [ofCard_of_three_lt ns h4]
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
        (m = 1 ∧ n = 1) ∨ (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) := by omega
    all_goals
      by_cases hs : Number.singular ∈ ns.values <;> by_cases hd : Number.dual ∈ ns.values <;>
        by_cases ht : Number.trial ∈ ns.values <;> simp_all [ofCard, fromCard]

-- The hypothesis is needed: a dual without a singular, or a trial without a dual, makes the
-- value of a sum depend on more than the values of its parts.
example : let ns : System := { values := {.dual, .plural} }
    ns.resolve (ns.ofCard 1) (ns.ofCard 1) ≠ ns.ofCard 2 := by decide
example : let ns : System := { values := {.singular, .trial, .plural} }
    ns.resolve (ns.ofCard 2) (ns.ofCard 1) ≠ ns.ofCard 3 := by decide

theorem foldl_resolve_ofCard (h : ns.DeterminateInitial) {m : ℕ} (hm : 0 < m) {ms : List ℕ}
    (hms : ∀ x ∈ ms, 0 < x) :
    (ms.map ns.ofCard).foldl ns.resolve (ns.ofCard m) = ns.ofCard (m + ms.sum) := by
  induction ms generalizing m with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.foldl_cons, resolve_ofCard h hm (hms x (by simp)),
      ih (by omega) fun y hy ↦ hms y (by simp [hy]), List.sum_cons, Nat.add_assoc]

theorem resolve_card_union {α : Type*} [DecidableEq α] (h : ns.DeterminateInitial)
    {s t : Finset α} (hs : s.Nonempty) (ht : t.Nonempty) (hst : Disjoint s t) :
    ns.resolve (ns.ofCard s.card) (ns.ofCard t.card) = ns.ofCard (s ∪ t).card := by
  rw [Finset.card_union_of_disjoint hst, resolve_ofCard h hs.card_pos ht.card_pos]

theorem coarsen_ofCard {src tgt : System}
    (h : ∀ v ∈ tgt.values, v.isDeterminate → v ∈ src.values) (n : ℕ) :
    tgt.coarsen (src.ofCard n) = tgt.ofCard n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coarsen, ofCard, fromCard, exactCard]
  rw [coarsen, exactCard_ofCard src hn]
  split_ifs with hs
  · rfl
  · by_cases h3 : n ≤ 3
    · have : fromCard n ∉ tgt.values := fun ht ↦ hs ⟨h _ ht (by interval_cases n <;> trivial), h3⟩
      simp [ofCard, this]
    · simp [ofCard_of_three_lt tgt (by omega : 3 < n)]

end Number.System
