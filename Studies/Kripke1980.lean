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
the simple sentences containing it; and the coincidence of the large and small scope readings
of a modal operator governing such a sentence. A name defined synonymously by a description
is not rigid unless the description uses an essential property. A description can instead fix
the reference of a rigid name, and then an identity between two such names is necessary if
true, while the identity between the descriptions fixing their references may be contingent.

## Main statements

* `isRigid_iff_forall_ne_not_diamond`: the intuitive test, pp. 48–49.
* `forall_largeScope_box_iff_smallScope_box_iff`: the equivalence with scope, p. 12 n. 15.
* `not_isRigid_of_not_isEssential`: a name defined by a description is not rigid, p. 57.
* `box_eq_of_isRigid`: identities between rigid designators are necessary, pp. 104, 143.
* `box_eq_iff_isRigid`: the metaphysical status of the standard meter, p. 56.

## Implementation notes

A designator is total: a name designates its referent even at worlds where the referent would
not have existed (p. 21 n. 21), and existence is a separate domain `D : W → Set E`, consulted by
essence alone. The scope theorems ignore existence, as n. 15 does, and metaphysical necessity
quantifies over every world, along `Set.univ`. The rigid designator whose reference `t` fixes
at `w` is `fun _ ↦ t w`, which takes the large scope reading of `t`
(`largeScope_eq_smallScope_const`), so the corresponding qualitative statement of
pp. 142–143, with each rigid designator replaced by the designator fixing its reference, is the
small scope reading. The distinction between de jure and de facto rigidity (p. 21 n. 21)
concerns how an intension is given, not the intension, and is not formalized.

## TODO

The epistemological statuses are not formalized: that whoever fixed the reference of *one
meter* by the stick knows a priori that it is one meter long (p. 56), and that *Hesperus is
Phosphorus* is known only a posteriori (p. 104).

## References

* [kripke-1980]
-/

@[expose] public section

namespace Kripke1980

open ModalLogic SetRel

variable {W E : Type*} {R : SetRel W W} {t t₁ t₂ : W → E} {D : W → Set E} {F : E → W → Prop}
  {w w₀ : W}

/-! ### Three forms of rigidity

The intuitive test (pp. 48–49), the truth conditions of simple sentences (p. 10), and scope
(p. 12 n. 15). For a description the scope readings come apart: the teacher of Alexander might
not have taught Alexander on the large scope reading and not on the small (p. 62 n. 25). -/

/-- No one other than Nixon might have been Nixon: a designator is rigid iff nothing other than
what it designates at a world might have been designated by it. -/
theorem isRigid_iff_forall_ne_not_diamond :
    IsRigid t ↔ ∀ w x, x ≠ t w → ¬ ◇[Set.univ] (t · = x) w :=
  ⟨fun h w _ hx ⟨v, _, hv⟩ ↦ hx (hv ▸ h v w), fun h v w ↦
    of_not_not fun hne ↦ h w (t v) hne ⟨v, trivial, rfl⟩⟩

theorem isRigid_iff_forall_exists_forall_iff [Nonempty W] :
    IsRigid t ↔ ∀ P : E → W → Prop, ∃ x, ∀ w, P (t w) w ↔ P x w := by
  refine ⟨fun h P ↦ ?_, fun h v w ↦ ?_⟩
  · obtain ⟨w₀⟩ := ‹Nonempty W›
    exact ⟨t w₀, fun w ↦ by rw [h w w₀]⟩
  · obtain ⟨x, hx⟩ := h fun e w ↦ e = t w
    exact ((hx v).1 rfl).symm.trans ((hx w).1 rfl)

/-- The large and small scope readings of necessity along `R` agree at `w` for every simple
sentence iff the designator designates at every world accessible from `w` what it designates
at `w`. -/
theorem forall_largeScope_box_iff_smallScope_box_iff :
    (∀ P, largeScope □[R] P t w ↔ smallScope □[R] P t w) ↔ ∀ v, w ~[R] v → t v = t w :=
  ⟨fun h v hv ↦ (h fun e _ ↦ e = t w).1 (fun _ _ ↦ rfl) v hv, fun h _ ↦
    forall₂_congr fun v hv ↦ by simp only [h v hv]⟩

theorem isRigid_iff_largeScope_eq_smallScope :
    IsRigid t ↔ ∀ P, largeScope □[Set.univ] P t = smallScope □[Set.univ] P t :=
  ⟨fun h P ↦ largeScope_eq_smallScope h _ P, fun h v w ↦
    forall_largeScope_box_iff_smallScope_box_iff.1 (fun P ↦ iff_of_eq (congrFun (h P) w)) v
      trivial⟩

theorem largeScope_diamond_and_not_smallScope (ht : ∀ w, F (t w) w) (h : ¬ F (t w₀) w) :
    largeScope ◇[Set.univ] (fun x v ↦ ¬ F x v) t w₀ ∧
      ¬ smallScope ◇[Set.univ] (fun x v ↦ ¬ F x v) t w₀ :=
  ⟨⟨w, trivial, h⟩, fun ⟨v, _, hv⟩ ↦ hv (ht v)⟩

/-! ### Essence -/

/-- A property is essential to `x` when it holds of `x` at every world where `x` exists. -/
def IsEssential (D : W → Set E) (x : E) (P : E → W → Prop) : Prop := ∀ w, x ∈ D w → P x w

/-! ### Fixing the reference

A description that fixes the reference of a rigid name does not give its meaning (p. 57), and
the statement that the standard meter is one meter long, known a priori by whoever fixed the
reference of *one meter* by it, is contingent (p. 56). An identity between rigid designators is
necessary if true, though the identity between the designators fixing their references may be
contingent (pp. 143–144). -/

/-- A name synonymous with a description of `F` is not rigid unless `F` is essential to what
the description actually designates. -/
theorem not_isRigid_of_not_isEssential (ht : ∀ w, F (t w) w)
    (hF : ¬ IsEssential D (t w₀) F) : ¬ IsRigid t :=
  fun h ↦ hF fun w _ ↦ h w w₀ ▸ ht w

theorem const_ne_of_not_isEssential (ht : ∀ w, F (t w) w) (hF : ¬ IsEssential D (t w₀) F) :
    (fun _ ↦ t w₀) ≠ t :=
  (isRigid_const _).ne (not_isRigid_of_not_isEssential ht hF)

/-- The stick is one meter long, *one meter* rigidly designating the length the stick has at
`w₀`, necessarily iff *the length of the stick* is rigid. -/
theorem box_eq_iff_isRigid : □[Set.univ] (fun w ↦ t w = t w₀) w ↔ IsRigid t :=
  ⟨fun h v u ↦ (h v trivial).trans (h u trivial).symm, fun h v _ ↦ h v w₀⟩

/-- An identity between rigid designators is necessary if true. -/
theorem box_eq_of_isRigid (h₁ : IsRigid t₁) (h₂ : IsRigid t₂) (h : t₁ w = t₂ w) :
    □[R] (fun v ↦ t₁ v = t₂ v) w :=
  fun v _ ↦ congrFun (h₁.eq_of_apply_eq h₂ h) v

/-- Two worlds, `true` actual: `id` and the constant `true` designate the same body at `true`,
so the identity between the rigid designators whose references they fix there is necessary,
while the identity between the designators themselves is contingent. -/
example :
    largeScope □[Set.univ] (fun x _ ↦ x.1 = x.2) (Function.prod id fun _ ↦ true) true ∧
      ¬ smallScope □[Set.univ] (fun x _ ↦ x.1 = x.2)
        (Function.prod (id : Bool → Bool) fun _ ↦ true) true :=
  ⟨box_eq_of_isRigid (isRigid_const _) (isRigid_const _) rfl, fun h ↦
    Bool.false_ne_true (h false trivial)⟩

end Kripke1980
