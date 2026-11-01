/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.GroupTheory.Congruence.Syntactic`.
-/
module

public import Mathlib.GroupTheory.Congruence.Hom

/-!
# The syntactic congruence of a subset

The *syntactic congruence* of a subset `S` of a magma is
[the greatest congruence](##Con.le_syntactic_iff) of which `S` is a union of classes, so the kernel
of a homomorphism lies below it exactly when `S` is
[the preimage of a set](##Con.ker_le_syntactic_iff). In a monoid it identifies `u` and `v` when
[no two-sided context tells them apart](##Con.syntactic_iff), that is when
$xuy \in S \iff xvy \in S$ for all `x` and `y`. It
[commutes with inverse images](##Con.comap_syntactic) along a homomorphism whose range and `1`
cover the target, as a surjection's does and as the embedding of a semigroup in the monoid with an
identity adjoined does. Over a free monoid or a free semigroup it is the syntactic congruence of a
language.

## Implementation notes

The congruence is defined by its universal property, so one definition serves magmas, semigroups
and monoids, and the description by contexts is a theorem where contexts exist.

## References

* [pin-mfa]
-/

@[expose] public section

namespace Con

open Relation

section Mul

variable {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
  {S T : Set M} {c : Con M} {u v : M}

/-- The *syntactic congruence* of `S` is the greatest congruence of which `S` is a union of
classes. -/
@[to_additive /-- The *syntactic congruence* of `S` is the greatest additive congruence of which
`S` is a union of classes. -/]
def syntactic (S : Set M) : Con M :=
  sSup {c | ∀ ⦃u v⦄, c u v → (u ∈ S ↔ v ∈ S)}

/-- Membership in `S` respects the syntactic congruence of `S`: the join of the congruences of which
`S` is a union of classes relates the chains of steps each taken in one of them. -/
@[to_additive]
theorem mem_iff_of_syntactic (h : syntactic S u v) : u ∈ S ↔ v ∈ S := by
  let R : M → M → Prop := fun x y ↦ ∃ c : Con M, (∀ ⦃u v⦄, c u v → (u ∈ S ↔ v ∈ S)) ∧ c x y
  have hr (a : M) {x y : M} (h : EqvGen R x y) : EqvGen R (x * a) (y * a) := by
    induction h with
    | rel _ _ h => obtain ⟨c, hc, h⟩ := h; exact .rel _ _ ⟨c, hc, c.mul h (c.refl a)⟩
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
  have hl (a : M) {x y : M} (h : EqvGen R x y) : EqvGen R (a * x) (a * y) := by
    induction h with
    | rel _ _ h => obtain ⟨c, hc, h⟩ := h; exact .rel _ _ ⟨c, hc, c.mul (c.refl a) h⟩
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
  let E : Con M := ⟨⟨EqvGen R, EqvGen.is_equivalence R⟩, fun h h' ↦ .trans _ _ _ (hr _ h) (hl _ h')⟩
  have hE : EqvGen R u v := (sSup_le fun c hc _ _ h ↦ .rel _ _ ⟨c, hc, h⟩ : syntactic S ≤ E) h
  clear h
  induction hE with
  | rel _ _ h => obtain ⟨c, hc, h⟩ := h; exact hc h
  | refl => exact .rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- The syntactic congruence of `S` is the greatest congruence of which `S` is a union of
classes. -/
@[to_additive]
theorem le_syntactic_iff : c ≤ syntactic S ↔ ∀ ⦃u v⦄, c u v → (u ∈ S ↔ v ∈ S) :=
  ⟨fun h _ _ huv ↦ mem_iff_of_syntactic (h huv), fun h ↦ le_sSup h⟩

/-- The kernel of `f` lies below the syntactic congruence of `S` exactly when `S` is the preimage
of a set under `f`. -/
@[to_additive]
theorem ker_le_syntactic_iff {f : F} : ker f ≤ syntactic S ↔ ∃ P : Set N, S = f ⁻¹' P := by
  refine le_syntactic_iff.trans ⟨fun h ↦ ⟨f '' S, Set.ext fun u ↦ ⟨fun hu ↦ ⟨u, hu, rfl⟩, ?_⟩⟩, ?_⟩
  · rintro ⟨v, hv, hvu⟩
    exact (h ((ker_rel f).2 hvu)).1 hv
  · rintro ⟨P, rfl⟩ u v huv
    simp only [Set.mem_preimage, (ker_rel f).1 huv]

@[to_additive (attr := simp)]
theorem syntactic_compl : syntactic Sᶜ = syntactic S := by
  refine le_antisymm (le_syntactic_iff.2 fun _ _ h ↦ ?_) (le_syntactic_iff.2 fun _ _ h ↦ ?_) <;>
    simpa only [Set.mem_compl_iff, not_iff_not] using mem_iff_of_syntactic h

@[to_additive]
theorem inf_le_syntactic_inter : syntactic S ⊓ syntactic T ≤ syntactic (S ∩ T) :=
  le_syntactic_iff.2 fun _ _ h ↦ and_congr (mem_iff_of_syntactic h.1) (mem_iff_of_syntactic h.2)

@[to_additive]
theorem inf_le_syntactic_union : syntactic S ⊓ syntactic T ≤ syntactic (S ∪ T) :=
  le_syntactic_iff.2 fun _ _ h ↦ or_congr (mem_iff_of_syntactic h.1) (mem_iff_of_syntactic h.2)

@[to_additive]
theorem syntactic_le_syntactic_preimage_mul_left (a : M) :
    syntactic S ≤ syntactic ((a * ·) ⁻¹' S) :=
  le_syntactic_iff.2 fun _ _ h ↦
    mem_iff_of_syntactic (S := S) ((syntactic S).mul ((syntactic S).refl a) h)

@[to_additive]
theorem syntactic_le_syntactic_preimage_mul_right (a : M) :
    syntactic S ≤ syntactic ((· * a) ⁻¹' S) :=
  le_syntactic_iff.2 fun _ _ h ↦
    mem_iff_of_syntactic (S := S) ((syntactic S).mul h ((syntactic S).refl a))

end Mul

section Monoid

variable {M : Type*} [Monoid M] {S : Set M} {u v : M}

/-- In a monoid, the syntactic congruence of `S` identifies `u` and `v` when no two-sided context
distinguishes them as members of `S`. -/
@[to_additive]
theorem syntactic_iff : syntactic S u v ↔ ∀ x y, x * u * y ∈ S ↔ x * v * y ∈ S := by
  refine ⟨fun h x y ↦ mem_iff_of_syntactic
    ((syntactic S).mul ((syntactic S).mul ((syntactic S).refl x) h) ((syntactic S).refl y)),
    fun h ↦ ?_⟩
  let c : Con M :=
    { r u v := ∀ x y, x * u * y ∈ S ↔ x * v * y ∈ S
      iseqv := ⟨fun _ _ _ ↦ .rfl, fun h x y ↦ (h x y).symm,
        fun h h' x y ↦ (h x y).trans (h' x y)⟩
      mul' {a b _ d} hab hcd x y := by
        have h₁ := hcd (x * a) y
        have h₂ := hab x (d * y)
        simp only [mul_assoc] at h₁ h₂ ⊢
        exact h₁.trans h₂ }
  exact le_syntactic_iff.2 (fun _ _ h ↦ by simpa using h 1 1) (show c u v from h)

end Monoid

variable {M N F : Type*} [Mul M] [Monoid N] [FunLike F M N] [MulHomClass F M N] {f : F}

/-- The syntactic congruence of an inverse image is the inverse image of the syntactic congruence,
along a homomorphism whose range and `1` cover its target. -/
@[to_additive]
theorem comap_syntactic (hf : ∀ y, y = 1 ∨ y ∈ Set.range f) (S : Set N) :
    (syntactic S).comap f (map_mul f) = syntactic (f ⁻¹' S) := by
  refine le_antisymm (le_syntactic_iff.2 fun _ _ h ↦ mem_iff_of_syntactic (S := S) h)
    fun u v h ↦ ?_
  have hr {u v : M} (h : syntactic (f ⁻¹' S) u v) (y : N) : f u * y ∈ S ↔ f v * y ∈ S := by
    rcases hf y with rfl | ⟨b, rfl⟩
    · simpa using mem_iff_of_syntactic h
    · rw [← map_mul, ← map_mul]
      exact mem_iff_of_syntactic (S := f ⁻¹' S) ((syntactic _).mul h ((syntactic _).refl b))
  refine show syntactic S (f u) (f v) from syntactic_iff.2 fun x y ↦ ?_
  rcases hf x with rfl | ⟨a, rfl⟩
  · simpa using hr h y
  · rw [← map_mul, ← map_mul]
    exact hr ((syntactic _).mul ((syntactic _).refl a) h) y

end Con
