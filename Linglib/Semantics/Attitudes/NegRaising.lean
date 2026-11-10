/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.AntiAdditive
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Neg-raising predicates

A neg-raising predicate such as *think* or *want* quantifies universally over a modal base and
presupposes the excluded middle: its subject is settled about the complement. Negation keeps the
presupposition, so a negated neg-raising predicate is true exactly where the modal base is
nonempty and lies outside the complement, which is the predicate applied to the negated
complement (`NegRaising.posExt_negation`). As a function of the complement, the negation is
therefore anti-additive (`NegRaising.isAntiAdditive_posExt_negation`), where the negation of a
plain universal is only antitone.

## Implementation notes

* The predicate takes a modal base and a heritage base, the alternatives into which the
  presupposition of the complement projects. *Think* has its subject's beliefs as both, and
  *want* has desires as modal base and beliefs as heritage base.
* The excluded middle is stated with the complement's full meaning, `φ u ≠ .true` rather than
  `φ u = .false`, so a complement's own presupposition is cancelled inside it and projects only
  through the heritage base.

## References

* [bartsch-1973]
* [gajewski-2007]
-/

@[expose] public section

namespace NegRaising

open ModalLogic SetRel

variable {W : Type*} {R H : SetRel W W} {φ : W → Trivalent} {w : W}

open Classical in
/-- A neg-raising predicate over the modal base `R` and the heritage base `H`, applied to a
complement. It presupposes that the complement is settled throughout the modal base and that the
complement's presupposition holds throughout the heritage base, and it asserts the complement
throughout the modal base. -/
noncomputable def sentence (R H : SetRel W W) (φ : W → Trivalent) : W → Trivalent :=
  Trivalent.condEvent
    (fun w ↦ □[H] (φ · ≠ .undefined) w ∧ (□[R] (φ · = .true) w ∨ □[R] (φ · ≠ .true) w))
    (□[R] (φ · = .true))

/-- A neg-raising predicate is false exactly when the complement's presupposition holds throughout
the heritage base and the complement fails throughout the nonempty modal base. -/
theorem sentence_eq_false_iff :
    sentence R H φ w = .false ↔
      □[H] (φ · ≠ .undefined) w ∧ (∃ u, w ~[R] u) ∧ □[R] (φ · ≠ .true) w := by
  simp only [sentence, Trivalent.condEvent_eq_false_iff]
  refine ⟨fun ⟨⟨hH, hEM⟩, hna⟩ ↦ ⟨hH, ?_, hEM.resolve_left hna⟩,
    fun ⟨hH, ⟨u, hu⟩, hbox⟩ ↦ ⟨⟨hH, .inr hbox⟩, fun hall ↦ hbox u hu (hall u hu)⟩⟩
  by_contra hne
  push Not at hne
  exact hna fun u hu ↦ absurd hu (hne u)

/-- When the heritage base is the modal base, a neg-raising predicate is false exactly when the
complement is false throughout the nonempty modal base. -/
theorem sentence_self_eq_false_iff :
    sentence R R φ w = .false ↔ (∃ u, w ~[R] u) ∧ □[R] (φ · = .false) w := by
  rw [sentence_eq_false_iff]
  refine ⟨fun ⟨hH, hne, hb⟩ ↦ ⟨hne, fun u hu ↦ ?_⟩,
    fun ⟨hne, hb⟩ ↦ ⟨fun u hu ↦ by simp [hb u hu], hne, fun u hu ↦ by simp [hb u hu]⟩⟩
  have := hH u hu
  have := hb u hu
  cases h : φ u <;> simp_all

open Classical in
/-- Negation over a neg-raising predicate with a presuppositionless complement. -/
noncomputable def negation (R H : SetRel W W) (p : Set W) : W → Trivalent :=
  (sentence R H fun u ↦ Trivalent.ofProp (u ∈ p))ᶜ

/-- A negated neg-raising predicate is true exactly where the modal base is nonempty and lies
outside the complement. -/
theorem posExt_negation (R H : SetRel W W) (p : Set W) :
    Trivalent.posExt (negation R H p) = R.dom ∩ R.core pᶜ := by
  ext w
  simp [negation, sentence_eq_false_iff, Box]

/-- A negated neg-raising predicate is nowhere true of the trivial complement. -/
theorem posExt_negation_univ (R H : SetRel W W) :
    Trivalent.posExt (negation R H Set.univ) = ∅ := by
  rw [posExt_negation, Set.compl_univ]
  exact Set.eq_empty_of_forall_notMem fun _ ⟨⟨_, hu⟩, h⟩ ↦ h hu

/-- A negated neg-raising predicate is anti-additive in its complement. -/
theorem isAntiAdditive_posExt_negation (R H : SetRel W W) :
    IsAntiAdditive fun p ↦ Trivalent.posExt (negation R H p) := fun p q ↦ by
  simp only [posExt_negation, Set.sup_eq_union, Set.inf_eq_inter, Set.compl_union, core_inter]
  exact Set.inter_inter_distrib_left ..

end NegRaising
