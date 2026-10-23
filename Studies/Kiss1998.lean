/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Exhaustification.Excluder

/-!
# É. Kiss (1998): Identificational Focus versus Information Focus

This file formalizes [kiss-1998]'s distinction between identificational focus, which in
Hungarian moves to the immediately preverbal position and expresses exhaustive identification,
and information focus, which stays in situ after the verb and merely marks its content as new.
Identificational focus exhaustifies the prejacent over the alternatives evoked by the
contextually given set, the `Exhaustification.exh` of [chierchia-2006], and information focus
asserts the bare prejacent. The paper's characterisation of exhaustive identification, that
the focus "is identified as the exhaustive subset of this set for which the predicate phrase
actually holds", is the theorem `exh_Ici`, and the coordination test and the dialogue test by
which the paper diagnoses exhaustivity come out as theorems on the hat-and-coat scenario of
its examples (`szabolcsi_test`, `farkas_test`). The distributional restrictions of §3 follow
from the same semantics, exhaustive identification being exclusion by identification. A
universal quantifier identifies without excluding (`exh_Ici_restrictor`), a *some*-phrase
excludes without identifying (`exh_nonempty_eq_empty`), and an additive *also* or *even*
phrase contradicts its own presupposition unless the given set has been narrowed by a prior
identification, the paper's (18) (`disjoint_exh_additive`, `additive_exh_of_notMem`).

## Implementation notes

* The scenario tracks only which of the given elements the predicate phrase holds of, so a
  world is a subset of the given set, the proposition that the predicate holds of a group
  `s` is the principal upper set `Set.Ici s`, and exhaustive identification over the given
  set `A` is the interval `Set.Icc s (s ∪ Aᶜ)`, exactly `s` among the given elements with the
  non-given ones unconstrained.
* *csak* 'only' phrases are obligatorily identificational because *csak* assigns the
  identificational focus feature (§8); the exclusion is the position's and *csak* adds an
  evaluative presupposition, which is outside this model.

## TODO

* §4 scope, §5.2 the cleft as the English realisation of identificational focus, §7 focus
  iteration and projection, and §9 the [+exhaustive] and [+contrastive] parametrisation
  across Italian, Romanian, Catalan, Greek, Arabic and Finnish.

## References

* [kiss-1998]
* [chierchia-2006]
-/

@[expose] public section

namespace Kiss1998

open Exhaustification Set

variable {ι : Type*} {A : Set ι} {a b : ι}

/-- The alternatives evoked by a focus over the given set `A`, one for each given element,
saying that the predicate phrase holds of it. -/
def alternatives (A : Set ι) : Set (Set (Set ι)) := (fun i ↦ Ici {i}) '' A

theorem alternatives_eq (A : Set ι) (a : ι) :
    alternatives A = ((fun i ↦ Ici {i}) <$> (⟨a, A⟩ : WithAlternatives ι)).alternatives := by
  ext q
  simp only [alternatives, mem_image, WithAlternatives.mem_alternatives_map]

/-! ### Exhaustive identification (§2) -/

/-- Exhaustive identification of `s` over the given set `A` asserts that the predicate holds of `s`
and of no other given element (9). -/
theorem exh_Ici (A s : Set ι) : exh (alternatives A) (Ici s) = Icc s (s ∪ Aᶜ) := by
  ext w
  simp only [mem_exh, alternatives, mem_Ici, mem_Icc, forall_mem_image, Ici_subset_Ici,
    singleton_subset_iff]
  refine and_congr_right fun _ ↦ ⟨fun h i hiw ↦ ?_, fun h i hiA hiw ↦ ?_⟩
  · exact (mem_union _ _ _).2 ((em (i ∈ A)).imp_left (h · hiw))
  · exact ((mem_union _ _ _).1 (h hiw)).resolve_right (not_not.2 hiA)

theorem exh_Ici_univ (s : Set ι) : exh (alternatives univ) (Ici s) = {s} := by
  rw [exh_Ici, compl_univ, union_empty, Icc_self]

/-- In Szabolcsi's coordination test ((12) against (13)), identificational *a hat* contradicts *a
hat and a coat*, while information-focus *a hat* follows from it. -/
theorem szabolcsi_test (hb : b ∈ A) (hab : a ≠ b) :
    Disjoint (exh (alternatives A) (Ici {a, b})) (exh (alternatives A) (Ici {a})) ∧
      Ici ({a, b} : Set ι) ⊆ Ici {a} := by
  refine ⟨?_, Ici_subset_Ici.2 (singleton_subset_iff.2 (mem_insert a _))⟩
  rw [exh_Ici, exh_Ici, disjoint_left]
  rintro w ⟨hw, -⟩ ⟨-, hw'⟩
  rcases (mem_union _ _ _).1 (hw' (hw (mem_insert_of_mem a (mem_singleton b)))) with h | h
  · exact hab (mem_singleton_iff.1 h).symm
  · exact h hb

/-- In Farkas's dialogue test (15), when Mary picked a coat too, the identificational claim is false
and the information-focus claim true. -/
theorem farkas_test (hb : b ∈ A) (hab : a ≠ b) :
    {a, b} ∉ exh (alternatives A) (Ici {a}) ∧ {a, b} ∈ Ici ({a} : Set ι) := by
  refine ⟨?_, singleton_subset_iff.2 (mem_insert a _)⟩
  rw [exh_Ici, mem_Icc, not_and]
  intro _ h
  rcases (mem_union _ _ _).1 (h (mem_insert_of_mem a (mem_singleton b))) with hba | hbA
  · exact hab (mem_singleton_iff.1 hba).symm
  · exact hbA hb

theorem not_monotone_exh (hb : b ∈ A) (hab : a ≠ b) : ¬ Monotone (exh (alternatives A)) :=
  fun h ↦ (farkas_test hb hab).1 <|
    h (Ici_subset_Ici.2 (singleton_subset_iff.2 (mem_insert a _))) <| by
      rw [exh_Ici]
      exact left_mem_Icc.2 subset_union_left

/-! ### Distributional restrictions (§3)

Exhaustive identification is exclusion by identification. An identificational focus names
the given elements the predicate holds of and excludes the rest, and the constituents barred
from the identificational position, (17b–e), are those for which one half fails. -/

/-- A universal quantifier identifies without excluding (17b), since exhaustifying *every
hat* over its restrictor is vacuous. -/
theorem exh_Ici_restrictor (A : Set ι) : exh (alternatives A) (Ici A) = Ici A := by
  rw [exh_Ici, union_compl_self, ← top_eq_univ, Icc_top]

/-- A *some*-phrase cannot be exhaustively identified (17e), since exhaustifying *something*
over a given set with two elements is contradictory. -/
theorem exh_nonempty_eq_empty (hA : A.Nontrivial) :
    exh (alternatives A) {w | (w ∩ A).Nonempty} = ∅ := by
  refine eq_empty_of_forall_notMem fun w hw ↦ ?_
  obtain ⟨⟨i, hiw, hiA⟩, h⟩ := mem_exh.1 hw
  obtain ⟨j, hjA, hji⟩ := hA.exists_ne i
  exact hji (mem_singleton_iff.1 (singleton_subset_iff.1
    (h _ ⟨i, hiA, rfl⟩ (singleton_subset_iff.2 hiw) ⟨j, mem_singleton j, hjA⟩))).symm

/-- The presupposition of the additive *also a* and *even a*, that the predicate holds of
some other given element. -/
def additive (A : Set ι) (a : ι) : Set (Set ι) := {w | ∃ b ∈ w ∩ A, b ≠ a}

/-- An additive phrase identifies without excluding (17c, 17d), since its presupposition
contradicts the exhaustification of its prejacent. -/
theorem disjoint_exh_additive (A : Set ι) (a : ι) :
    Disjoint (exh (alternatives A) (Ici {a})) (additive A a) := by
  rw [exh_Ici, disjoint_left]
  rintro w ⟨-, hw⟩ ⟨b, ⟨hbw, hbA⟩, hba⟩
  rcases hw hbw with h | h
  · exact hba h
  · exact h hbA

/-- In the cleft *also*-phrase of (18), *it was also `a`* identifies `a` in addition to the earlier
`b`, excluding everybody else. -/
theorem additive_exh_of_notMem (hb : b ∉ A) (hab : b ≠ a) :
    {a, b} ∈ exh (alternatives A) (Ici {a}) ∩ additive (insert b A) a := by
  refine ⟨?_, b, ⟨mem_insert_of_mem a (mem_singleton b), mem_insert b A⟩, hab⟩
  rw [exh_Ici, mem_Icc, insert_subset_iff]
  exact ⟨singleton_subset_iff.2 (mem_insert a _), mem_union_left _ (mem_singleton a),
    singleton_subset_iff.2 (mem_union_right _ hb)⟩

end Kiss1998
