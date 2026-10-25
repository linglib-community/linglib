/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Reference.Rigidity

/-!
# Kripke (1980): Naming and Necessity

A designator is an intension `t : W → E`, rigid when it designates the same object in every
possible world (`IsRigid`). The book gives three equivalent forms of rigidity: the intuitive
test, that nothing other than what it designates might have been it; the truth conditions of
the simple sentences containing it, each the possession of a single property by a single
individual at every world; and the coincidence of the large and small scope readings of a modal
operator governing such a sentence. A name defined synonymously by a description is not rigid unless
the description uses an essential property, so a description that fixes the reference of a
rigid name does not give its meaning, and what it lets one know a priori is contingent.

## Main statements

* `isRigid_iff_forall_ne_not_diamond`: the intuitive test, pp. 48–49.
* `isRigid_iff_forall_exists_forall_iff`: the truth conditions of simple sentences, p. 10.
* `isRigid_iff_largeScope_eq_smallScope`: the equivalence with scope, p. 12 n. 15.
* `not_isRigid_of_not_isEssential`: a name defined by a description is not rigid, p. 57.
* `box_eq_iff_isRigid`: the contingent a priori, p. 56.

## Implementation notes

A designator is total: a name designates its referent even at worlds where the referent would
not have existed (p. 21 n. 21), and existence is a separate domain `D : W → Set E`, consulted by
essence and strong rigidity alone. The scope theorems ignore existence, as n. 15 does.
Metaphysical necessity quantifies over every world, along `Set.univ`. The distinction between
de jure and de facto rigidity (p. 21 n. 21) concerns how an intension is given, not the
intension, and is not formalized.

## References

* [kripke-1980]
-/

@[expose] public section

namespace Kripke1980

open ModalLogic SetRel

variable {W E : Type*} {R : SetRel W W} {t : W → E} {D : W → Set E} {F P : E → W → Prop}
  {w w₀ : W} {x : E}

/-! ### Three forms of rigidity -/

/-- No one other than Nixon might have been Nixon: a designator is rigid iff nothing other than
what it designates at a world might have been designated by it. -/
theorem isRigid_iff_forall_ne_not_diamond :
    IsRigid t ↔ ∀ w x, x ≠ t w → ¬ ◇[Set.univ] (t · = x) w :=
  ⟨fun h w _ hx ⟨v, _, hv⟩ ↦ hx (hv ▸ h v w), fun h v w ↦
    of_not_not fun hne ↦ h w (t v) hne ⟨v, trivial, rfl⟩⟩

/-- A designator is rigid iff the truth condition of each simple sentence predicating something
of it is, at every world, the possession of the property by a single individual. -/
theorem isRigid_iff_forall_exists_forall_iff [Nonempty W] :
    IsRigid t ↔ ∀ P : E → W → Prop, ∃ x, ∀ w, P (t w) w ↔ P x w := by
  refine ⟨fun h P ↦ ?_, fun h v w ↦ ?_⟩
  · obtain ⟨w₀⟩ := ‹Nonempty W›
    exact ⟨t w₀, fun w ↦ by rw [h w w₀]⟩
  · obtain ⟨x, hx⟩ := h fun e w ↦ e = t w
    exact ((hx v).1 rfl).symm.trans ((hx w).1 rfl)

/-! ### Scope

The large and small scope readings of an operator coincide for a rigid designator (p. 12 n. 15)
and come apart for a description: the teacher of Alexander might not have taught Alexander on
the large scope reading and not on the small (p. 62 n. 25). -/

/-- The large scope reading of the operator `O` over the predication of `P` of `t`, which
evaluates `t` at the world of the whole sentence. -/
def largeScope (O : (W → Prop) → W → Prop) (P : E → W → Prop) (t : W → E) (w : W) : Prop :=
  O (P (t w)) w

/-- The small scope reading, which evaluates `t` at each world the operator reaches. -/
def smallScope (O : (W → Prop) → W → Prop) (P : E → W → Prop) (t : W → E) : W → Prop :=
  O fun v ↦ P (t v) v

theorem largeScope_eq_smallScope (h : IsRigid t) (O : (W → Prop) → W → Prop)
    (P : E → W → Prop) : largeScope O P t = smallScope O P t :=
  funext fun w ↦ congrArg (O · w) (funext fun v ↦ by rw [h v w])

theorem forall_largeScope_box_iff :
    (∀ P, largeScope □[R] P t w ↔ smallScope □[R] P t w) ↔ ∀ v, w ~[R] v → t v = t w :=
  ⟨fun h v hv ↦ (h fun e _ ↦ e = t w).1 (fun _ _ ↦ rfl) v hv, fun h _ ↦
    forall₂_congr fun v hv ↦ by simp only [h v hv]⟩

/-- A designator is rigid iff the large and small scope readings of necessity governing any
simple sentence containing it coincide. -/
theorem isRigid_iff_largeScope_eq_smallScope :
    IsRigid t ↔ ∀ P, largeScope □[Set.univ] P t = smallScope □[Set.univ] P t :=
  ⟨fun h P ↦ largeScope_eq_smallScope h _ P, fun h v w ↦
    forall_largeScope_box_iff.1 (fun P ↦ iff_of_eq (congrFun (h P) w)) v trivial⟩

theorem largeScope_diamond_and_not_smallScope (ht : ∀ w, F (t w) w) (h : ¬ F (t w₀) w) :
    largeScope ◇[Set.univ] (fun x v ↦ ¬ F x v) t w₀ ∧
      ¬ smallScope ◇[Set.univ] (fun x v ↦ ¬ F x v) t w₀ :=
  ⟨⟨w, trivial, h⟩, fun ⟨v, _, hv⟩ ↦ hv (ht v)⟩

/-! ### Essence and existence -/

/-- A property is essential to `x` when it holds of `x` at every world where `x` exists. -/
def IsEssential (D : W → Set E) (x : E) (P : E → W → Prop) : Prop := ∀ w, x ∈ D w → P x w

/-- A designator is strongly rigid when it is a rigid designator of a necessary existent. -/
def IsStronglyRigid (D : W → Set E) (t : W → E) : Prop := IsRigid t ∧ ∀ w, t w ∈ D w

theorem IsEssential.apply_of_isRigid (hP : IsEssential D (t w₀) P) (ht : IsRigid t)
    (hw : t w ∈ D w) : P (t w) w := by
  rw [ht w w₀] at hw ⊢
  exact hP w hw

theorem isStronglyRigid_const (h : ∀ w, x ∈ D w) : IsStronglyRigid D fun _ : W ↦ x :=
  ⟨isRigid_const x, h⟩

/-! ### Fixing the reference

A description that fixes the reference of a rigid name does not give its meaning (p. 57), and
the statement that the standard meter is one meter long, known a priori by whoever fixed the
reference of *one meter* by it, is contingent (p. 56). -/

/-- A name synonymous with a description of `F` is not rigid unless `F` is essential to what
the description actually designates. -/
theorem not_isRigid_of_not_isEssential (ht : ∀ w, F (t w) w)
    (hF : ¬ IsEssential D (t w₀) F) : ¬ IsRigid t :=
  fun h ↦ hF fun w _ ↦ h w w₀ ▸ ht w

theorem const_ne_of_not_isEssential (ht : ∀ w, F (t w) w) (hF : ¬ IsEssential D (t w₀) F) :
    (fun _ ↦ t w₀) ≠ t :=
  (isRigid_const _).ne (not_isRigid_of_not_isEssential ht hF)

/-- The stick is one meter long, *one meter* rigidly designating the length the stick actually
has, necessarily iff *the length of the stick* is rigid. -/
theorem box_eq_iff_isRigid : □[Set.univ] (fun w ↦ t w = t w₀) w ↔ IsRigid t :=
  ⟨fun h v u ↦ (h v trivial).trans (h u trivial).symm, fun h v _ ↦ h v w₀⟩

end Kripke1980
