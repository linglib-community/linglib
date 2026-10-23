module

public import Linglib.Core.ModelTheory.BijectiveGame
public import Linglib.Semantics.Plurality.Reciprocal
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Peters and Westerståhl (2006): Quantifiers in Language and Logic

The quantifier `LIN` behind Intermediate Reciprocity, which relates any two distinct elements by
a chain, is not definable in `FO(Mon)`, first-order logic with every monadic quantifier added.
Hella's bijective game cannot separate a directed cycle of length `2 ^ (r + 1)` from two directed
cycles of length `2 ^ r` in `r` rounds, so the two satisfy the same sentences of `FO(Mon)` of
quantifier rank `≤ r` (`duplicatorWinsBijective_oneCycle_twoCycles`). `LIN` holds of the first and
fails on the second (`oneCycle_mem_lin`, `twoCycles_not_mem_lin`), so no sentence of `FO(Mon)`
defines it (`lin_not_monDefinable`): the reciprocal reading built on `LIN` is genuinely polyadic.

## Implementation notes

The two models are the successor graphs of `+ 1` on `ZMod (2 ^ (r + 1))` and of `+ (0, 1)` on
`ZMod 2 × ZMod (2 ^ r)`, and the game is won by the general result for successor graphs of
permutations with long cycles, `FirstOrder.Language.duplicatorWinsBijective_successor`.

## TODO

* The relativization of `LIN`, Intermediate Reciprocity, is not definable from monadic quantifiers
  either; stating this needs the language with a unary and a binary relation symbol.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

namespace PetersWesterstahl2006

open FirstOrder Language Relation CategoryTheory

private theorem addRight_zpow_apply {G : Type*} [AddCommGroup G] (a x : G) (d : ℤ) :
    (Equiv.addRight a ^ d) x = x + d • a := by
  induction d using Int.induction_on generalizing x with
  | zero => simp
  | succ d ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, Equiv.coe_addRight, add_zsmul, one_zsmul,
      add_assoc, add_comm a]
  | pred d ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, Equiv.Perm.inv_def, Equiv.addRight_symm,
      Equiv.coe_addRight, sub_zsmul, one_zsmul]
    simp only [add_assoc, add_comm]

private theorem eq_zero_of_zsmul_one_eq_zero {n : ℕ} {d : ℤ} (hd : |d| < n)
    (h : d • (1 : ZMod n) = 0) : d = 0 := by
  rw [zsmul_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Int.eq_zero_of_abs_lt_dvd h hd

private theorem transGen_add_one {n : ℕ} [NeZero n] {x y : ZMod n} (hxy : x ≠ y) :
    TransGen (fun a b : ZMod n ↦ b = a + 1) x y := by
  have chain (k : ℕ) : TransGen (fun a b : ZMod n ↦ b = a + 1) x (x + (k + 1 : ℕ)) := by
    induction k with
    | zero => exact .single (by simp)
    | succ k ih => exact ih.tail (by push_cast; ring)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero
    ((ZMod.val_ne_zero _).2 (sub_ne_zero.2 hxy.symm))
  have := chain k
  rwa [← hk, ZMod.natCast_zmod_val, add_sub_cancel] at this

/-- One directed cycle of length `2 ^ (r + 1)`, as a structure in the language of graphs. -/
def oneCycle (r : ℕ) : Bundled.{0} Language.graph.Structure :=
  ⟨ZMod (2 ^ (r + 1)), graphStructure fun x y ↦ y = Equiv.addRight 1 x⟩

/-- Two directed cycles of length `2 ^ r`, as a structure in the language of graphs. -/
def twoCycles (r : ℕ) : Bundled.{0} Language.graph.Structure :=
  ⟨ZMod 2 × ZMod (2 ^ r), graphStructure fun x y ↦ y = Equiv.addRight (0, 1) x⟩

private theorem eq_zero_of_addRight_one_zpow {n : ℕ} {x : ZMod n} {d : ℤ} (hd : |d| < n)
    (h : (Equiv.addRight (1 : ZMod n) ^ d) x = x) : d = 0 := by
  rw [addRight_zpow_apply, add_eq_left] at h
  exact eq_zero_of_zsmul_one_eq_zero hd h

private theorem eq_zero_of_addRight_zero_one_zpow {n : ℕ} {x : ZMod 2 × ZMod n} {d : ℤ}
    (hd : |d| < n) (h : (Equiv.addRight ((0, 1) : ZMod 2 × ZMod n) ^ d) x = x) : d = 0 := by
  rw [addRight_zpow_apply, add_eq_left, Prod.smul_mk, smul_zero, Prod.mk_eq_zero] at h
  exact eq_zero_of_zsmul_one_eq_zero hd h.2

/-- Duplicator wins `r` rounds of the bijective game between one cycle of length `2 ^ (r + 1)`
and two of length `2 ^ r` (Theorem 7). -/
theorem duplicatorWinsBijective_oneCycle_twoCycles (r : ℕ) :
    Language.graph.DuplicatorWinsBijective r (default : Fin 0 → oneCycle r)
      (default : Fin 0 → twoCycles r) := by
  let : Fintype (oneCycle r) := inferInstanceAs (Fintype (ZMod (2 ^ (r + 1))))
  let : Fintype (twoCycles r) := inferInstanceAs (Fintype (ZMod 2 × ZMod (2 ^ r)))
  have hcard : Fintype.card (ZMod (2 ^ (r + 1))) = Fintype.card (ZMod 2 × ZMod (2 ^ r)) := by
    simp [ZMod.card, pow_succ']
  have hlt : (2 : ℤ) ^ r < ((2 ^ (r + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega : r < r + 1)
  exact duplicatorWinsBijective_successor (M := oneCycle r) (N := twoCycles r)
    (σ := (Equiv.addRight (1 : ZMod (2 ^ (r + 1))) :))
    (τ := (Equiv.addRight ((0, 1) : ZMod 2 × ZMod (2 ^ r)) :)) hcard r
    (fun _ _ hd ↦ eq_zero_of_addRight_one_zpow (hd.trans hlt))
    (fun _ _ hd ↦ eq_zero_of_addRight_zero_one_zpow (by exact_mod_cast hd))

theorem oneCycle_mem_lin (r : ℕ) : oneCycle r ∈ Reciprocal.lin.holds :=
  ⟨ZMod.nontrivial_iff.2 (by have := Nat.one_lt_two_pow_iff.2 r.succ_ne_zero; omega),
    fun _ _ hxy ↦ transGen_add_one hxy⟩

theorem twoCycles_not_mem_lin (r : ℕ) : twoCycles r ∉ Reciprocal.lin.holds := by
  rintro ⟨-, h⟩
  have hfst {a b : ZMod 2 × ZMod (2 ^ r)}
      (hab : TransGen (fun x y ↦ y = Equiv.addRight ((0 : ZMod 2), (1 : ZMod (2 ^ r))) x) a b) :
      a.1 = b.1 := by
    induction hab with
    | single h => simp [h]
    | tail _ h ih => simp [ih, h]
  exact absurd (hfst (h (show ((0, 0) : ZMod 2 × ZMod (2 ^ r)) ≠ (1, 0) by simp)))
    (show (0 : ZMod 2) ≠ 1 by decide)

/-- `LIN` is not definable in `FO(Mon)` (Corollary 8). -/
theorem lin_not_monDefinable : ¬ Language.graph.MonDefinable Set.univ Reciprocal.lin.{0}.holds :=
  not_monDefinable_of_duplicatorWinsBijective fun r ↦
    ⟨oneCycle r, trivial, twoCycles r, trivial, duplicatorWinsBijective_oneCycle_twoCycles r,
      oneCycle_mem_lin r, twoCycles_not_mem_lin r⟩

end PetersWesterstahl2006
