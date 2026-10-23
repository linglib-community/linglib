/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Aperiodic`; mathlib has `Monoid.IsTorsion` but no
aperiodicity notion.
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.MinMax

/-!
# Aperiodic monoids

A monoid is *aperiodic* when a single power stabilizes every element, `x ^ (n + 1) = x ^ n`.
Schützenberger introduced these monoids as the ones with only trivial subgroups, and they are the
algebraic counterpart of the star-free languages.

## Main definitions

* `Monoid.IsAperiodic`: some power stabilizes every element.

## Main results

* `Monoid.isAperiodic_iff_forall_exists`: a finite monoid is aperiodic when the powers of each
  element stabilize.
* `Monoid.IsAperiodic.pow_mul_eq_of_isIdempotentElem`: an idempotent power of `x` absorbs `x`.
* `Monoid.IsAperiodic.of_injective`, `Monoid.IsAperiodic.of_surjective`, `Monoid.IsAperiodic.prod`:
  closure under submonoids, quotients and products.

## References

* [schutzenberger-1965]
* [mcnaughton-papert-1971]
* [pin-mfa]
-/

@[expose] public section

namespace Monoid

variable (M : Type*) [Monoid M]

/-- A monoid is *aperiodic* when some power stabilizes every element. -/
@[to_additive]
def IsAperiodic : Prop := ∃ n : ℕ, ∀ x : M, x ^ (n + 1) = x ^ n

variable {M}

@[to_additive]
theorem IsAperiodic.of_subsingleton [Subsingleton M] : IsAperiodic M :=
  ⟨0, fun _ ↦ Subsingleton.elim _ _⟩

@[to_additive]
theorem pow_succ_stabilizes {x : M} {n : ℕ} (h : x ^ (n + 1) = x ^ n) :
    ∀ m, n ≤ m → x ^ (m + 1) = x ^ m := by
  refine fun m hm ↦ Nat.le_induction h (fun k _ hk ↦ ?_) m hm
  rw [pow_succ x (k + 1), hk, ← pow_succ, hk]

/-- A finite monoid is aperiodic exactly when the powers of each element stabilize. -/
@[to_additive]
theorem isAperiodic_iff_forall_exists [Finite M] :
    IsAperiodic M ↔ ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n := by
  refine ⟨fun ⟨n, hn⟩ x ↦ ⟨n, hn x⟩, fun h ↦ ?_⟩
  choose n hn using h
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max n
  exact ⟨n x₀, fun x ↦ pow_succ_stabilizes (hn x) _ (hx₀ x)⟩

/-- In an aperiodic monoid, an idempotent positive power of `x` absorbs `x`. -/
theorem IsAperiodic.pow_mul_eq_of_isIdempotentElem (h : IsAperiodic M) {x : M} {n : ℕ}
    (hn : n ≠ 0) (he : IsIdempotentElem (x ^ n)) : x ^ n * x = x ^ n := by
  obtain ⟨N, hN⟩ := h
  rw [← he.pow_eq N.add_one_ne_zero, ← pow_mul, ← pow_succ]
  exact pow_succ_stabilizes (hN x) _
    (N.le_succ.trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn)))

/-- Aperiodicity passes along a surjective monoid hom, with the same exponent. -/
@[to_additive]
theorem IsAperiodic.of_surjective {N : Type*} [Monoid N] {f : M →* N}
    (hf : Function.Surjective f) (hM : IsAperiodic M) : IsAperiodic N := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_pow, ← map_pow, hn]

/-- Aperiodicity pulls back along an injective monoid hom, with the same exponent. -/
@[to_additive]
theorem IsAperiodic.of_injective {N : Type*} [Monoid N] {f : M →* N}
    (hf : Function.Injective f) (hN : IsAperiodic N) : IsAperiodic M := by
  obtain ⟨n, hn⟩ := hN
  exact ⟨n, fun x ↦ hf (by rw [map_pow, map_pow, hn])⟩

/-- A binary product of aperiodic monoids is aperiodic (take the larger exponent). -/
@[to_additive]
theorem IsAperiodic.prod {N : Type*} [Monoid N] (hM : IsAperiodic M) (hN : IsAperiodic N) :
    IsAperiodic (M × N) := by
  obtain ⟨nM, hnM⟩ := hM
  obtain ⟨nN, hnN⟩ := hN
  refine ⟨max nM nN, fun x ↦ Prod.ext ?_ ?_⟩
  · exact pow_succ_stabilizes (hnM x.1) _ (le_max_left _ _)
  · exact pow_succ_stabilizes (hnN x.2) _ (le_max_right _ _)

@[to_additive]
theorem IsAperiodic.of_mulEquiv {N : Type*} [Monoid N] (e : M ≃* N) (hM : IsAperiodic M) :
    IsAperiodic N :=
  hM.of_surjective (f := e.toMonoidHom) e.surjective

end Monoid
