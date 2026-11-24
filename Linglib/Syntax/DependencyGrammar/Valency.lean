/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Basic
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.Interval.Basic

/-!
# Valency

The *valency* of a word is the dependents it must and may govern. Among the dependents of a
word, its *valents* are those its valency provides for and the rest are *adjuncts*, which any
word takes freely; a valent is obligatory when its quantity is one and optional when its
quantity is zero or one.

A valency over relations of type `L` is a nonempty interval of multisets of relations: its lower
end `val.fst` holds the relations a word must govern and its upper end `val.snd` those it may.
In a dependency graph, given the predicate `p` of the relations borne by valents, the valents of
a position `v` bear the multiset of relations `g.valents p v`, and `v` satisfies `val` when that
multiset lies in the interval. The interval `NonemptyInterval.pure m` is the valency with every
valent of `m` obligatory, and intervals are ordered by inclusion, so a valency lies below every
valency that admits whatever it admits.

## Main definitions

* `Valency L` is the type of valencies over the relations `L`, and `Valency.withOptional` is the
  valency with given obligatory and optional valents.
* `Graph.dependentsBy g p v` is the dependents of `v` by a relation satisfying `p`.
* `Graph.valents g p v` is the multiset of the relations satisfying `p` that the dependents of
  `v` bear.
* `Graph.Satisfies g p v val` says that the valents of `v` are those of the valency `val`.

## Main results

* `Graph.satisfies_iff_count`: a position satisfies a valency iff the quantity of each relation
  among its valents lies between the quantities at the two ends.
* `Graph.Satisfies.mono`: satisfaction is monotone in the valency.
* `Graph.satisfies_comap_symm`: satisfaction is invariant under a change of linearization.

## Implementation notes

The valents are a multiset because a valency may call for several valents of one relation, as
when relations are syntactic categories and a verb takes three nominals. A valency says nothing
of word order: the side of the head a valent stands on is a property of the relation in a
language, not of the word's valency, and `Graph.satisfies_comap_symm` holds for every permutation of
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

/-! ### Valencies -/

/-- A valency over the relations `L`: an interval of multisets of relations, from the valents a
word must have to those it may have. -/
abbrev Valency (L : Type*) := NonemptyInterval (Multiset L)

namespace Valency

/-- The valency whose obligatory valents are `required` and whose optional valents are
`optional`. -/
def withOptional (required optional : Multiset L) : Valency L :=
  ⟨(required, required + optional), Multiset.le_add_right _ _⟩

@[simp] theorem mem_withOptional {required optional m : Multiset L} :
    m ∈ withOptional required optional ↔ required ≤ m ∧ m ≤ required + optional :=
  Iff.rfl

@[simp] theorem withOptional_zero (m : Multiset L) : withOptional m 0 = .pure m := by
  ext : 2 <;> simp [withOptional]

theorem mem_withOptional_singleton {required m : Multiset L} {a : L} :
    m ∈ withOptional required {a} ↔ m = required ∨ m = required + {a} := by
  rw [mem_withOptional]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.1 h₁
    rcases Multiset.le_singleton.1 (Multiset.add_le_add_iff_left.1 h₂) with rfl | rfl <;> simp
  · rintro (rfl | rfl) <;> simp

end Valency

namespace Graph

/-! ### Valents -/

/-- The dependents of `v` by a relation satisfying `p`. -/
def dependentsBy (g : Graph L (Fin n)) (p : L → Prop) [DecidablePred p] (v : Fin n) :
    Finset (Fin n) :=
  {w | ∃ r ∈ g.label v w, p r}

/-- The relations satisfying `p` that the dependents of `v` bear, each as often as `v` has a
dependent by it. With `p` the predicate of the relations of valents, these are the valents of
`v`. -/
def valents (g : Graph L (Fin n)) (p : L → Prop) [DecidablePred p] (v : Fin n) : Multiset L :=
  (univ : Finset (Fin n)).val.filterMap fun w ↦ (g.label v w).filter p

variable {g : Graph L (Fin n)} {p : L → Prop} [DecidablePred p] {v w : Fin n} {r : L}
  {val val₁ val₂ : Valency L}

@[simp] theorem mem_dependentsBy : w ∈ g.dependentsBy p v ↔ ∃ r ∈ g.label v w, p r := by
  simp [dependentsBy]

@[simp] theorem mem_valents : r ∈ g.valents p v ↔ p r ∧ ∃ w, g.label v w = some r := by
  simp [valents, Option.filter_eq_some_iff, and_comm]

theorem card_valents : (g.valents p v).card = #(g.dependentsBy p v) := by
  rw [valents, dependentsBy, Finset.card_def, Finset.filter_val]
  induction (univ : Finset (Fin n)).val using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    rcases h : g.label v w with _ | r
    · have hw : (g.label v w).filter p = none := by simp [h]
      rw [Multiset.filterMap_cons_none (f := fun w ↦ (g.label v w).filter p) _ _ hw]
      simpa [h] using ih
    · by_cases hr : p r
      · have hw : (g.label v w).filter p = some r := by simp [h, Option.filter, hr]
        rw [Multiset.filterMap_cons_some (fun w ↦ (g.label v w).filter p) _ _ hw]
        simp [h, hr, ih]
      · have hw : (g.label v w).filter p = none := by simp [h, Option.filter, hr]
        rw [Multiset.filterMap_cons_none (f := fun w ↦ (g.label v w).filter p) _ _ hw]
        simpa [h, hr] using ih

theorem filter_valents (q : L → Prop) [DecidablePred q] :
    (g.valents p v).filter q = g.valents (fun r ↦ p r ∧ q r) v := by
  simp only [valents, Multiset.filter_filterMap]
  congr 1
  funext w
  cases g.label v w with
  | none => rfl
  | some r =>
    simp only [Option.filter]
    split_ifs <;> simp_all

theorem count_valents [DecidableEq L] (r : L) :
    (g.valents p v).count r = if p r then #(g.dependentsBy (· = r) v) else 0 := by
  rw [Multiset.count_eq_card_filter_eq, filter_valents, card_valents]
  split_ifs with hr
  · congr 1
    ext w
    simp only [mem_dependentsBy]
    exact ⟨fun ⟨x, hx, _, h⟩ ↦ ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ ↦ ⟨x, hx, h ▸ hr, h.symm⟩⟩
  · rw [Finset.card_eq_zero]
    ext w
    simp only [mem_dependentsBy, notMem_empty, iff_false]
    rintro ⟨x, -, hx, rfl⟩
    exact hr hx

theorem valents_comap_symm (σ : Equiv.Perm (Fin n)) : (g.comap σ.symm).valents p v = g.valents p
    (σ.symm v) := by
  have h : (univ : Finset (Fin n)).val.map σ.symm = univ.val :=
    congrArg Finset.val (Finset.map_univ_equiv σ.symm)
  conv_rhs => rw [valents, ← h, Multiset.filterMap_map]
  rfl

/-! ### Satisfaction -/

/-- The position `v` satisfies the valency `val` when its valents, the relations satisfying `p`
that its dependents bear, lie between the obligatory valents of `val` and all its valents. -/
def Satisfies (g : Graph L (Fin n)) (p : L → Prop) [DecidablePred p] (v : Fin n) (val : Valency L) :
    Prop :=
  g.valents p v ∈ val

instance [DecidableEq L] : Decidable (g.Satisfies p v val) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

theorem satisfies_iff : g.Satisfies p v val ↔ val.fst ≤ g.valents p v ∧ g.valents p v ≤ val.snd :=
  Iff.rfl

/-- A position satisfies a valency iff the quantity of each relation among its valents is at
least its quantity among the obligatory valents and at most its quantity among all valents. -/
theorem satisfies_iff_count [DecidableEq L] :
    g.Satisfies p v val ↔ ∀ r, val.fst.count r ≤ (g.valents p v).count r ∧
      (g.valents p v).count r ≤ val.snd.count r := by
  simp only [satisfies_iff, Multiset.le_iff_count, forall_and]

@[simp] theorem satisfies_pure {m : Multiset L} : g.Satisfies p v (.pure m) ↔ g.valents p v = m :=
  NonemptyInterval.mem_pure

theorem Satisfies.mono (h : val₁ ≤ val₂) (hs : g.Satisfies p v val₁) : g.Satisfies p v val₂ :=
  ⟨h.1.trans hs.1, hs.2.trans h.2⟩

@[simp] theorem satisfies_comap_symm (σ : Equiv.Perm (Fin n)) :
    (g.comap σ.symm).Satisfies p v val ↔ g.Satisfies p (σ.symm v) val := by
  rw [Satisfies, valents_comap_symm, Satisfies]

end Graph

end DependencyGrammar
