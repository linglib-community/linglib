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

The *syntactic congruence* of a subset `S` of a monoid identifies `u` and `v` when no two-sided
context tells them apart as members of `S`, that is when $xuy \in S \iff xvy \in S$ for all `x`
and `y`. It is [the greatest congruence](##Con.le_syntactic_iff) of which `S` is a union of
classes, so the kernel of a homomorphism lies below it exactly when `S` is
[the preimage of a set](##Con.ker_le_syntactic_iff). It is unchanged by complement, commutes with
[inverse images along surjective homomorphisms](##Con.comap_syntactic), and refines the syntactic
congruences of the preimages of `S` under multiplication by an element. Over a free monoid it is
the syntactic congruence of a language.

## Implementation notes

The congruence is defined on a monoid, where the two-sided contexts are its elements. On a
semigroup the contexts range over the semigroup with an identity adjoined.

## References

* [pin-mfa]
-/

@[expose] public section

namespace Con

variable {M N : Type*} [Monoid M] [Monoid N] {S T : Set M} {c : Con M} {u v : M}

/-- The *syntactic congruence* of `S` identifies `u` and `v` when no two-sided context
distinguishes them as members of `S`. -/
def syntactic (S : Set M) : Con M where
  r u v := ∀ x y, x * u * y ∈ S ↔ x * v * y ∈ S
  iseqv := ⟨fun _ _ _ ↦ .rfl, fun h x y ↦ (h x y).symm, fun h h' x y ↦ (h x y).trans (h' x y)⟩
  mul' {a b _ d} hab hcd x y := by
    have h₁ := hcd (x * a) y
    have h₂ := hab x (d * y)
    simp only [mul_assoc] at h₁ h₂ ⊢
    exact h₁.trans h₂

theorem syntactic_iff : syntactic S u v ↔ ∀ x y, x * u * y ∈ S ↔ x * v * y ∈ S := Iff.rfl

theorem mem_iff_of_syntactic (h : syntactic S u v) : u ∈ S ↔ v ∈ S := by
  simpa using h 1 1

/-- The syntactic congruence of `S` is the greatest congruence of which `S` is a union of
classes. -/
theorem le_syntactic_iff : c ≤ syntactic S ↔ ∀ ⦃u v⦄, c u v → (u ∈ S ↔ v ∈ S) :=
  ⟨fun h _ _ huv ↦ mem_iff_of_syntactic (h huv),
    fun h _ _ huv x y ↦ h (c.mul (c.mul (c.refl x) huv) (c.refl y))⟩

/-- The kernel of `f` lies below the syntactic congruence of `S` exactly when `S` is the preimage
of a set under `f`. -/
theorem ker_le_syntactic_iff {f : M →* N} : ker f ≤ syntactic S ↔ ∃ T : Set N, S = f ⁻¹' T := by
  refine le_syntactic_iff.trans ⟨fun h ↦ ⟨f '' S, Set.ext fun u ↦ ⟨fun hu ↦ ⟨u, hu, rfl⟩, ?_⟩⟩, ?_⟩
  · rintro ⟨v, hv, hvu⟩
    exact (h ((ker_rel f).2 hvu)).1 hv
  · rintro ⟨T, rfl⟩ u v huv
    simp only [Set.mem_preimage, (ker_rel f).1 huv]

@[simp] theorem syntactic_compl : syntactic Sᶜ = syntactic S :=
  ext fun _ _ ↦ forall₂_congr fun _ _ ↦ not_iff_not

theorem inf_le_syntactic_inter : syntactic S ⊓ syntactic T ≤ syntactic (S ∩ T) :=
  fun {_ _} h x y ↦ and_congr (h.1 x y) (h.2 x y)

theorem inf_le_syntactic_union : syntactic S ⊓ syntactic T ≤ syntactic (S ∪ T) :=
  fun {_ _} h x y ↦ or_congr (h.1 x y) (h.2 x y)

theorem syntactic_le_syntactic_preimage_mul_left (a : M) :
    syntactic S ≤ syntactic ((a * ·) ⁻¹' S) :=
  le_syntactic_iff.2 fun _ _ h ↦
    mem_iff_of_syntactic (S := S) ((syntactic S).mul ((syntactic S).refl a) h)

theorem syntactic_le_syntactic_preimage_mul_right (a : M) :
    syntactic S ≤ syntactic ((· * a) ⁻¹' S) :=
  le_syntactic_iff.2 fun _ _ h ↦
    mem_iff_of_syntactic (S := S) ((syntactic S).mul h ((syntactic S).refl a))

/-- Along a surjective homomorphism, the syntactic congruence of an inverse image is the inverse
image of the syntactic congruence. -/
theorem comap_syntactic {f : N →* M} (hf : Function.Surjective f) (S : Set M) :
    (syntactic S).comap f (map_mul f) = syntactic (f ⁻¹' S) := by
  ext u v
  refine ⟨fun h x y ↦ by simpa only [Set.mem_preimage, map_mul] using h (f x) (f y), fun h x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf x
  obtain ⟨y, rfl⟩ := hf y
  simpa only [Set.mem_preimage, map_mul] using h x y

end Con
