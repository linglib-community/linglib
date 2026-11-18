module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniqueness of an embedding of an ordered group into an Archimedean field

An Archimedean ordered group embeds in the reals (`Archimedean.embedReal`). An embedding into an
Archimedean ordered field is [unique up to a positive
factor](##OrderAddMonoidHom.exists_pos_forall_eq_mul): an element's image is fixed, relative to
that of a positive element, by which rational multiples lie below it.

`[UPSTREAM]` candidate for `Mathlib/Algebra/Order/Archimedean/Hom.lean`, beside the uniqueness of
ordered ring homomorphisms.

## References

* [krantz-1971]
-/

@[expose] public section

open Function

variable {M K : Type*} [AddCommGroup M] [LinearOrder M] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

private theorem ratCast_lt_div_iff {h : M →+o K} (hh : StrictMono h) {a : M} (ha : 0 < h a)
    (x : M) (q : ℚ) : (q : K) < h x / h a ↔ q.num • a < (q.den : ℤ) • x := by
  have hden : (0 : K) < q.den := by exact_mod_cast q.den_pos
  rw [← hh.lt_iff_lt, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast,
    lt_div_iff₀ ha, Rat.cast_def, div_mul_eq_mul_div, div_lt_iff₀ hden, mul_comm (h x)]

variable [IsOrderedAddMonoid M] [Archimedean K]

/-- Two injective ordered-group homomorphisms of an ordered group into an Archimedean ordered
field differ by a positive factor. -/
-- [krantz-1971] Theorem 2.5, p. 53
theorem OrderAddMonoidHom.exists_pos_forall_eq_mul (f g : M →+o K) (hf : Injective f)
    (hg : Injective g) : ∃ c : K, 0 < c ∧ ∀ x, g x = c * f x := by
  rcases subsingleton_or_nontrivial M with _ | _
  · exact ⟨1, one_pos, fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero, mul_zero]⟩
  obtain ⟨a, ha⟩ := exists_zero_lt (α := M)
  have hfs : StrictMono f := (OrderHomClass.mono f).strictMono_of_injective hf
  have hgs : StrictMono g := (OrderHomClass.mono g).strictMono_of_injective hg
  have hfa : 0 < f a := by simpa using hfs ha
  have hga : 0 < g a := by simpa using hgs ha
  refine ⟨g a / f a, div_pos hga hfa, fun x ↦ ?_⟩
  have h : g x / g a = f x / f a := eq_of_forall_rat_lt_iff_lt fun q ↦ by
    rw [ratCast_lt_div_iff hgs hga, ratCast_lt_div_iff hfs hfa]
  rw [div_eq_div_iff hga.ne' hfa.ne'] at h
  rw [div_mul_eq_mul_div, eq_div_iff hfa.ne', h, mul_comm]
