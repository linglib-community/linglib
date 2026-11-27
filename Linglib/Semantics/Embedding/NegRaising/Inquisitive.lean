/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Inquisitive.Modal
public import Linglib.Semantics.Embedding.NegRaising.Basic
public import Linglib.Semantics.Presupposition.Strawson

/-!
# Neg-raising predicates with a statement or a question as complement

A neg-raising predicate is a modal base together with a form that every such predicate shares:
over the base `M`, it presupposes that `M` resolves the polar question of its complement and
asserts that `M` resolves the complement. *Believe* has the subject's doxastic state as its base
and *want* her bouletic state.

With the declarative of `p` the presupposition is the excluded middle, that `M` lies within `p` or
within its negation, and the predicate is the presuppositional box of the relation whose states
`M` gives. With a complement that is not informative, as an interrogative is, the polar question
of the complement is the complement, so the predicate asserts what it presupposes and is true
wherever it is defined.

## Main definitions

* `NegRaising.ofModalBase`: the neg-raising predicate over a modal base.

## Main results

* `NegRaising.ofModalBase_ofSet_eq_box`: on a declarative it is the presuppositional box.
* `NegRaising.ofModalBase_ofSet_eq_false_iff`: it is false of a declarative exactly where the base
  lies within the declarative's negation and not within the declarative.
* `NegRaising.isStrawsonUE_ofModalBase`: it is Strawson upward entailing in its complement.
* `NegRaising.ofModalBase_eq_true_of_info_eq_univ`: of a complement that is not informative it is
  true wherever it is defined.

## Implementation notes

The presupposition is stated as resolution of the polar question, which is the disjunction that
the base resolves the complement or its negation. Nothing is assumed of the base: it may be
inconsistent, and it need not contain the world of evaluation.

The complement is an inquisitive proposition and carries no presupposition of its own; the
presuppositional box takes a complement that does, and the two agree on a plain statement.

## References

* [theiler-etal-2019]
* [gajewski-2007]
* [bartsch-1973]
-/

@[expose] public section

namespace NegRaising

open Inquisitive Inquisitive.Proposition ModalLogic SetRel

variable {W : Type*} {M : W → Set W} {P : Proposition (Set W)} {p : Set W} {w : W}

open Classical in
/-- The neg-raising predicate over the modal base `M` presupposes that `M` resolves the polar
question of its complement and asserts that `M` resolves the complement. -/
noncomputable def ofModalBase (M : W → Set W) (P : Proposition (Set W)) : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ w ∈ P.query.resolvedBy M) fun w ↦ w ∈ P.resolvedBy M

/-- The predicate is defined where the base resolves the complement or its negation. -/
theorem ofModalBase_ne_undefined_iff :
    ofModalBase M P w ≠ .undefined ↔ M w ∈ P ∨ M w ∈ Pᶜ := by
  simp [ofModalBase, resolvedBy_query, or_iff_not_imp_left]

/-- Of a declarative, the predicate is defined where the excluded middle holds of the base. -/
theorem ofModalBase_ofSet_ne_undefined_iff :
    ofModalBase M (ofSet p) w ≠ .undefined ↔ M w ⊆ p ∨ M w ⊆ pᶜ := by
  rw [ofModalBase_ne_undefined_iff, compl_eq, info_ofSet]
  rfl

/-- The predicate is false of a declarative exactly where the base lies within the declarative's
negation and not within the declarative, so its denial is the predicate of the negation. -/
theorem ofModalBase_ofSet_eq_false_iff :
    ofModalBase M (ofSet p) w = .false ↔ M w ⊆ pᶜ ∧ ¬ M w ⊆ p := by
  simp only [ofModalBase, Trivalent.condEvent_eq_false_iff, resolvedBy_query, compl_eq,
    info_ofSet, Set.mem_union, mem_resolvedBy, mem_ofSet]
  tauto

open Classical in
/-- Of a complement that is not informative, the predicate asserts what it presupposes, so it is
true wherever it is defined. -/
theorem ofModalBase_eq_true_of_info_eq_univ (h : P.info = Set.univ)
    (hd : ofModalBase M P w ≠ .undefined) : ofModalBase M P w = .true := by
  have hq : w ∈ P.query.resolvedBy M :=
    by_contra fun hn ↦ hd (Trivalent.condEvent_eq_undefined_iff.2 hn)
  exact Trivalent.condEvent_eq_true_iff.2 ⟨hq, resolvedBy_query_of_info_eq_univ h M ▸ hq⟩

/-- Of a polar question, whatever its prejacent and the base, the predicate is true wherever it
is defined. -/
theorem ofModalBase_query_eq_true (hd : ofModalBase M P.query w ≠ .undefined) :
    ofModalBase M P.query w = .true :=
  ofModalBase_eq_true_of_info_eq_univ (info_query P) hd

open Classical in
/-- The predicate is Strawson upward entailing in its complement: where it is defined of both, a
stronger complement it is true of makes it true of a weaker one. -/
theorem isStrawsonUE_ofModalBase (M : W → Set W) :
    Presupposition.IsStrawsonUE (ofModalBase M) :=
  .of_monotone (a := fun P w ↦ w ∈ P.resolvedBy M) (fun _ _ h _ hw ↦ resolvedBy_mono M h hw)
    fun _ _ ↦ Trivalent.condEvent_kLE

private theorem eq_of_iff {a b : Trivalent} (ht : a = .true ↔ b = .true)
    (hu : a = .undefined ↔ b = .undefined) : a = b := by
  cases a <;> cases b <;> simp_all

open Classical in
/-- On a plain statement the predicate over the states of a relation is the presuppositional box
of that relation. -/
theorem ofModalBase_ofSet_eq_box (R H : SetRel W W) (p : Set W) :
    ofModalBase (fun w ↦ {u | w ~[R] u}) (ofSet p) = box R H fun u ↦ Trivalent.ofProp (u ∈ p) := by
  funext w
  refine eq_of_iff ?_ ?_ <;>
    simp [ofModalBase, box, resolvedBy_query, compl_eq, Box, Set.subset_def]

end NegRaising
