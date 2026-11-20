/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Length
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.Interval.Basic

/-!
# Valency

The *valency* of a word is the dependents it must and may govern. Among the dependents of a
word, its *valents* are those its valency provides for and the rest are *adjuncts*, which any
word takes freely; a valent is obligatory when its quantity is one and optional when its
quantity is zero or one.

In a dependency graph with relations of type `L`, the dependents of a position `v` bear the
multiset of relations `g.relations v`. A valency is a nonempty interval of multisets of
relations: its lower end `val.fst` holds the relations a word must govern and its upper end
`val.snd` those it may. Given the predicate `p` of the relations borne by valents, `v` satisfies
`val` when the relations of its valents, `(g.relations v).filter p`, lie in the interval. The
interval `NonemptyInterval.pure m` is the valency with every valent of `m` obligatory, and
intervals are ordered by inclusion, so a valency lies below every valency that admits whatever
it admits.

## Main definitions

* `Graph.childrenBy g p v` is the dependents of `v` by a relation satisfying `p`.
* `Graph.relations g v` is the multiset of the relations of the dependents of `v`.
* `Valency L` is the type of valencies over the relations `L`, and `Valency.withOptional` is the
  valency with given obligatory and optional valents.
* `Graph.Satisfies g p v val` says that the valents of `v` are those of the valency `val`.

## Main results

* `Graph.satisfies_iff_count`: a position satisfies a valency iff the quantity of each relation
  among its valents lies between the quantities at the two ends.
* `Graph.Satisfies.mono`: satisfaction is monotone in the valency.
* `Graph.satisfies_map`: satisfaction is invariant under a change of linearization.

## Implementation notes

The valents are a multiset because a valency may call for several valents of one relation, as
when relations are syntactic categories and a verb takes three nominals. A valency says nothing
of word order: the side of the head a valent stands on is a property of the relation in a
language, not of the word's valency, and `Graph.satisfies_map` holds for every permutation of
the positions.

## References

* [tesniere-1959]
* [hudson-2010]
* [osborne-2019]
-/

@[expose] public section

open Finset

namespace DependencyGrammar

variable {L : Type*} {n : ℕ}

namespace Graph

variable (g : Graph L n) (p : L → Prop) [DecidablePred p] (v : Fin n)

/-! ### Dependents by relation -/

/-- The dependents of `v` by a relation satisfying `p`. -/
def childrenBy : Finset (Fin n) := {w | ∃ r ∈ g.label v w, p r}

variable {g p v} in
@[simp] theorem mem_childrenBy {w : Fin n} : w ∈ g.childrenBy p v ↔ ∃ r ∈ g.label v w, p r := by
  simp [childrenBy]

/-- The relations of the dependents of `v`, each as often as `v` has a dependent by it. -/
def relations : Multiset L := (univ : Finset (Fin n)).val.filterMap (g.label v)

variable {g v} in
@[simp] theorem mem_relations {r : L} : r ∈ g.relations v ↔ ∃ w, g.label v w = some r := by
  simp [relations]

private theorem card_filter_filterMap {α : Type*} (f : α → Option L) (s : Multiset α) :
    ((s.filterMap f).filter p).card = (s.filter fun a ↦ ∃ r ∈ f a, p r).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    cases h : f a with
    | none => simp [Multiset.filterMap_cons_none _ _ h, h, ih]
    | some r =>
      by_cases hr : p r <;> simp [Multiset.filterMap_cons_some _ _ _ h, h, hr, ih]

/-- The number of relations of `v` satisfying `p` is the number of its dependents by such a
relation. -/
theorem card_filter_relations : ((g.relations v).filter p).card = #(g.childrenBy p v) :=
  card_filter_filterMap p _ _

/-- The quantity of a relation among the valents of `v` is the number of dependents `v` has by
it when it is a relation of valents, and zero otherwise. -/
theorem count_filter_relations [DecidableEq L] (r : L) :
    ((g.relations v).filter p).count r = if p r then #(g.childrenBy (· = r) v) else 0 := by
  rw [Multiset.count_filter]
  split_ifs
  · rw [Multiset.count_eq_card_filter_eq, ← card_filter_relations]
    simp only [eq_comm]
  · rfl

/-- The relations of a position are those of its preimage under a change of linearization. -/
theorem relations_map (σ : Equiv.Perm (Fin n)) :
    (g.map σ).relations v = g.relations (σ.symm v) := by
  have h : (univ : Finset (Fin n)).val.map σ.symm = univ.val :=
    congrArg Finset.val (Finset.map_univ_equiv σ.symm)
  conv_rhs => rw [relations, ← h, Multiset.filterMap_map]
  rfl

end Graph

/-! ### Valencies -/

/-- A valency over the relations `L`: an interval of multisets of relations, from the valents a
word must have to those it may have. -/
abbrev Valency (L : Type*) := NonemptyInterval (Multiset L)

/-- The valency whose obligatory valents are `required` and whose optional valents are
`optional`. -/
def Valency.withOptional (required optional : Multiset L) : Valency L :=
  ⟨(required, required + optional), Multiset.le_add_right _ _⟩

@[simp] theorem Valency.withOptional_zero (m : Multiset L) : withOptional m 0 = .pure m := by
  ext : 2 <;> simp [withOptional]

namespace Graph

variable (g : Graph L n) (p : L → Prop) [DecidablePred p] (v : Fin n) {val val₁ val₂ : Valency L}

/-- The position `v` satisfies the valency `val` when the relations of its valents, the
dependents by a relation satisfying `p`, lie between the obligatory valents of `val` and all
its valents. -/
def Satisfies (val : Valency L) : Prop := (g.relations v).filter p ∈ val

instance [DecidableEq L] (val : Valency L) : Decidable (g.Satisfies p v val) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

variable {g p v}

theorem satisfies_iff :
    g.Satisfies p v val ↔
      val.fst ≤ (g.relations v).filter p ∧ (g.relations v).filter p ≤ val.snd :=
  Iff.rfl

/-- A position satisfies a valency iff the quantity of each relation among its valents is at
least its quantity among the obligatory valents and at most its quantity among all valents. -/
theorem satisfies_iff_count [DecidableEq L] :
    g.Satisfies p v val ↔ ∀ r, val.fst.count r ≤ ((g.relations v).filter p).count r ∧
      ((g.relations v).filter p).count r ≤ val.snd.count r := by
  simp only [satisfies_iff, Multiset.le_iff_count, forall_and]

/-- A position satisfies the valency with every valent obligatory iff its valents are exactly
those. -/
@[simp] theorem satisfies_pure {m : Multiset L} :
    g.Satisfies p v (.pure m) ↔ (g.relations v).filter p = m :=
  NonemptyInterval.mem_pure

/-- A position satisfying a valency satisfies every valency that includes it. -/
theorem Satisfies.mono (h : val₁ ≤ val₂) (hs : g.Satisfies p v val₁) : g.Satisfies p v val₂ :=
  ⟨h.1.trans hs.1, hs.2.trans h.2⟩

/-- Satisfaction of a valency is invariant under a change of linearization. -/
@[simp] theorem satisfies_map (σ : Equiv.Perm (Fin n)) :
    (g.map σ).Satisfies p v val ↔ g.Satisfies p (σ.symm v) val := by
  rw [Satisfies, relations_map, Satisfies]

end Graph

end DependencyGrammar
