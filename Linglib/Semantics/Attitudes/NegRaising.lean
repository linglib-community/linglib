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

A neg-raising predicate such as *think* or *want* quantifies universally over a modal base, and its
negation is understood as the predicate applied to the negated complement. The accounts of this
share one proposition, the excluded middle: the modal base settles the complement
(`NegRaising.excludedMiddle`). Together with the negated universal it yields the lowered reading
(`NegRaising.compl_core_inter_excludedMiddle`). The accounts differ on its status. On the
presuppositional account the predicate presupposes it (`NegRaising.box`), so the negation is true
exactly where the modal base is nonempty and lies outside the complement
(`NegRaising.posExt_negation`) and is anti-additive in the complement
(`NegRaising.isAntiAdditive_posExt_negation`). On the scalar account the predicate is the plain
universal `SetRel.core` and the excluded middle is its alternative.

## Implementation notes

* `NegRaising.box` takes a second relation besides the modal base, giving the worlds at which
  the complement's own presupposition must hold. For *think* and for *want* these are the
  subject's belief worlds: the complement's presupposition is inherited as a belief of the subject.
* The excluded middle of `NegRaising.box` is taken about the truth set of the complement, so a
  complement's own presupposition is cancelled inside it and projects only through the second
  relation.

## References

* [bartsch-1973]
* [karttunen-peters-1979]
* [gajewski-2007]
* [romoli-2013b]
-/

@[expose] public section

namespace NegRaising

open ModalLogic SetRel

variable {W : Type*} {R H : SetRel W W} {φ : W → Trivalent} {p : Set W} {w : W}

/-! ### The excluded middle -/

/-- The excluded middle of a modal base about a proposition: the proposition holds throughout the
modal base or fails throughout it. -/
def excludedMiddle (R : SetRel W W) (p : Set W) : Set W := R.core p ∪ R.core pᶜ

@[simp] theorem mem_excludedMiddle : w ∈ excludedMiddle R p ↔ w ∈ R.core p ∨ w ∈ R.core pᶜ :=
  .rfl

theorem core_subset_excludedMiddle (R : SetRel W W) (p : Set W) :
    R.core p ⊆ excludedMiddle R p :=
  Set.subset_union_left

/-- A universal that fails, with the excluded middle, is the universal of the negation over a
nonempty modal base. -/
theorem compl_core_inter_excludedMiddle (R : SetRel W W) (p : Set W) :
    (R.core p)ᶜ ∩ excludedMiddle R p = R.dom ∩ R.core pᶜ := by
  ext w
  refine ⟨fun ⟨hn, h⟩ ↦ ⟨?_, h.resolve_left hn⟩, fun ⟨⟨u, hu⟩, h⟩ ↦ ⟨fun hp ↦ h hu (hp hu), .inr h⟩⟩
  by_contra hd
  exact hn fun u hu ↦ absurd ⟨u, hu⟩ hd

/-! ### The presuppositional account -/

open Classical in
/-- The presuppositional neg-raising predicate over the modal base `R`, as an operator on a
complement ([gajewski-2007]). It presupposes the excluded middle of `R` about the complement's
truth set and that the complement's presupposition holds throughout `H`, and it asserts the
complement throughout `R`. -/
noncomputable def box (R H : SetRel W W) (φ : W → Trivalent) : W → Trivalent :=
  Trivalent.condEvent
    (fun w ↦ □[H] (φ · ≠ .undefined) w ∧ (□[R] (φ · = .true) w ∨ □[R] (φ · ≠ .true) w))
    (□[R] (φ · = .true))

open Classical in
theorem box_ne_undefined_iff :
    box R H φ w ≠ .undefined ↔
      w ∈ H.core (Trivalent.gapExt φ)ᶜ ∧ w ∈ excludedMiddle R (Trivalent.posExt φ) :=
  (not_congr Trivalent.condEvent_eq_undefined_iff).trans not_not

/-- The predicate is false exactly when the complement's presupposition holds throughout `H` and
the complement fails throughout the nonempty modal base. -/
theorem box_eq_false_iff :
    box R H φ w = .false ↔
      □[H] (φ · ≠ .undefined) w ∧ (∃ u, w ~[R] u) ∧ □[R] (φ · ≠ .true) w := by
  simp only [box, Trivalent.condEvent_eq_false_iff]
  refine ⟨fun ⟨⟨hH, hEM⟩, hna⟩ ↦ ⟨hH, ?_, hEM.resolve_left hna⟩,
    fun ⟨hH, ⟨u, hu⟩, hbox⟩ ↦ ⟨⟨hH, .inr hbox⟩, fun hall ↦ hbox u hu (hall u hu)⟩⟩
  by_contra hne
  push Not at hne
  exact hna fun u hu ↦ absurd hu (hne u)

/-- When `H` is the modal base, the predicate is false exactly when the complement is false
throughout the nonempty modal base. -/
theorem box_self_eq_false_iff :
    box R R φ w = .false ↔ (∃ u, w ~[R] u) ∧ □[R] (φ · = .false) w := by
  rw [box_eq_false_iff]
  refine ⟨fun ⟨hH, hne, hb⟩ ↦ ⟨hne, fun u hu ↦ ?_⟩,
    fun ⟨hne, hb⟩ ↦ ⟨fun u hu ↦ by simp [hb u hu], hne, fun u hu ↦ by simp [hb u hu]⟩⟩
  have := hH u hu
  have := hb u hu
  cases h : φ u <;> simp_all

open Classical in
/-- Negation over the presuppositional predicate with a presuppositionless complement. -/
noncomputable def negation (R H : SetRel W W) (p : Set W) : W → Trivalent :=
  (box R H fun u ↦ Trivalent.ofProp (u ∈ p))ᶜ

/-- A negated neg-raising predicate is true exactly where the modal base is nonempty and lies
outside the complement. -/
theorem posExt_negation (R H : SetRel W W) (p : Set W) :
    Trivalent.posExt (negation R H p) = R.dom ∩ R.core pᶜ := by
  ext w
  simp [negation, box_eq_false_iff, Box]

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
