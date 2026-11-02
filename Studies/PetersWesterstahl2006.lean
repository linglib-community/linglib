module

public import Linglib.Core.ModelTheory.BijectiveGame
public import Linglib.Semantics.Plurality.Reciprocal
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Lindstrom

/-!
# Peters and Westerståhl (2006): Quantifiers in Language and Logic

The quantifier `LIN` behind Intermediate Reciprocity, which relates any two distinct elements by
a chain, is not definable in `FO(Mon)`, first-order logic with every monadic quantifier added.
Hella's bijective game cannot separate a directed cycle of length `2 ^ (r + 1)` from two directed
cycles of length `2 ^ r` in `r` rounds, so the two satisfy the same sentences of `FO(Mon)` of
quantifier rank `≤ r` (`duplicatorWinsBijective_oneCycle_twoCycles`). `LIN` holds of the first and
fails on the second (`oneCycle_mem_lin`, `twoCycles_not_mem_lin`), so no sentence of `FO(Mon)`
defines it (`lin_not_monDefinable`): the reciprocal reading built on `LIN` is genuinely polyadic.

Peters and Westerståhl's quantirelation universal has the quantifiers that interpret
quantirelations conservative and satisfying extension, and they claim that the lexical quantifier
expressions denote quantifiers closed under isomorphism. On finite universes the global
determiner denotations meeting both are [exactly the denotations of the binary relations between
`|A \ B|` and `|A ∩ B|`](##PetersWesterstahl2006.conservative_ext_isom_iff_exists_toFamily), the
patterns of the number triangle, and every determiner symbol denotes one. Of the logically
respectable quantifiers the book offers as no determiner's meaning, MO, which holds when the
restrictor has more elements than the scope,
[is not conservative](##PetersWesterstahl2006.not_conservative_mo), while Div and Sqt are
patterns of the triangle, ruled out on empirical grounds alone.

The same triangle decides first-order definability. *At least `k`* [is
definable](##PetersWesterstahl2006.foDefinable_atLeast), while the properly proportional
quantifiers, *most* among them, are closed under isomorphism and yet
[no sentence defines them](##PetersWesterstahl2006.not_foDefinable_thresholdGt), even on finite
universes. Dropping conservativity and extension, a quantifier of type `⟨1⟩` is
[a relation between cardinal numbers](##PetersWesterstahl2006.existsUnique_cardinal_relation).

## Implementation notes

The two models are the successor graphs of `+ 1` on `ZMod (2 ^ (r + 1))` and of `+ (0, 1)` on
`ZMod 2 × ZMod (2 ^ r)`, and the game is won by the general result for successor graphs of
permutations with long cycles, `FirstOrder.Language.duplicatorWinsBijective_successor`.

The universal and the claim are stated of denotations, not of the fragments' entries. An entry's
readings are determiner symbols, which meet both by construction
(`QuantificationalDeterminer.conservative_ext_isom_of_mem_denote`), and the fragments draw some of
their readings from sources later than the book.

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

/-- Duplicator wins the `r`-round bijective game on one `2 ^ (r + 1)`-cycle versus two `2 ^
r`-cycles (Theorem 7). -/
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

theorem oneCycle_mem_lin (r : ℕ) : oneCycle r ∈ Reciprocal.lin :=
  ⟨ZMod.nontrivial_iff.2 (by have := Nat.one_lt_two_pow_iff.2 r.succ_ne_zero; omega),
    fun _ _ hxy ↦ transGen_add_one hxy⟩

theorem twoCycles_not_mem_lin (r : ℕ) : twoCycles r ∉ Reciprocal.lin := by
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
theorem lin_not_monDefinable :
    ¬ Language.graph.MonDefinable Set.univ (Reciprocal.lin.{0} : Set _) :=
  not_monDefinable_of_duplicatorWinsBijective fun r ↦
    ⟨oneCycle r, trivial, twoCycles r, trivial, duplicatorWinsBijective_oneCycle_twoCycles r,
      oneCycle_mem_lin r, twoCycles_not_mem_lin r⟩

/-! ### (QU) and (A) -/

section Universals

open Quantifier

universe u

/-- Fact 11 (b) and Fact 12, on finite universes: a global determiner denotation is conservative,
satisfies extension and is closed under isomorphism, as (QU) and (A) require of lexical
quantirelations, exactly when it is the denotation of a binary relation between `|A \ B|` and
`|A ∩ B|`. -/
theorem conservative_ext_isom_iff_exists_toFamily {Q : Det.Family.{u}} :
    Q.Conservative ∧ Q.Ext ∧ Q.Isom ↔ ∃ q : NumberTree, q.toFamily = Q :=
  ⟨fun ⟨hC, hE, hI⟩ ↦ ⟨_, NumberTree.toFamily_ofFamily hC (Det.Family.constant_iff.2 ⟨hE, hI⟩)⟩,
    fun ⟨q, hq⟩ ↦ hq ▸ ⟨NumberTree.conservative_toFamily q, (NumberTree.constant_toFamily q).ext,
      (NumberTree.constant_toFamily q).isom⟩⟩

example (s : Det.Symbol) : (Det.Symbol.denote.{u} s).Conservative ∧
    (Det.Symbol.denote.{u} s).Ext ∧ (Det.Symbol.denote.{u} s).Isom :=
  conservative_ext_isom_iff_exists_toFamily.2 ⟨s.numberTree, s.denote_eq_toFamily.symm⟩

/-- MO of (38a): the restrictor has more elements than the scope. -/
def mo : Det.Family.{0} := fun _ _ A B ↦ B.ncard < A.ncard

-- p. 14
theorem not_conservative_mo : ¬ mo.Conservative := fun h ↦ by
  have := h Bool {true} {false}
  simp [mo] at this

/-- Div of (38b): `|A ∩ B|` divides `|A|`. -/
def div : Det.Family.{0} := (NumberTree.ofSizes fun x p ↦ x ∣ p).toFamily

/-- Sqt of (38c): `|A ∩ B|` exceeds the square root of `|A|`. -/
def sqt : Det.Family.{0} := (NumberTree.ofSizes fun x p ↦ p < x * x).toFamily

-- p. 14
example : (div.Conservative ∧ div.Ext ∧ div.Isom) ∧ (sqt.Conservative ∧ sqt.Ext ∧ sqt.Isom) :=
  ⟨conservative_ext_isom_iff_exists_toFamily.2 ⟨_, rfl⟩,
    conservative_ext_isom_iff_exists_toFamily.2 ⟨_, rfl⟩⟩

/-! ### Quantifiers as relations between cardinals -/

open Cardinal in
/-- Ch. 3, Fact 4, after Mostowski: a quantifier of type `⟨1⟩` is a unique binary relation between
cardinal numbers, holding of `|M - A|` and `|A|`. -/
theorem existsUnique_cardinal_relation
    (Q : LindstromQuantifier.{0, 0, u} (Language.monadic (Fin 1))) :
    ∃! R : Cardinal.{u} → Cardinal.{u} → Prop, ∀ (M : Type u) (A : Set M),
      (⟨M, monadic.structure ![A]⟩ : Bundled.{u} (Language.monadic (Fin 1)).Structure) ∈ Q ↔
        R #↥Aᶜ #↥A := by
  classical
  let c (k m : Cardinal.{u}) (S : (Language.monadic (Fin 1)).Relations 1 → Prop) : Cardinal.{u} :=
    if S (.pred 0) then m else k
  have hc (M : Type u) (A : Set M) :
      LindstromQuantifier.typeCount (⟨M, monadic.structure ![A]⟩ :
        Bundled.{u} (Language.monadic (Fin 1)).Structure) = c #↥Aᶜ #↥A := funext fun S ↦ by
    have hcell : @unaryType _ M (monadic.structure ![A]) ⁻¹' {S} = {x | x ∈ A ↔ S (.pred 0)} :=
      Set.ext fun x ↦ (unaryType_monadic_structure_eq_iff x S).trans Fin.forall_fin_one
    rw [LindstromQuantifier.typeCount]
    change #↥(@unaryType _ M (monadic.structure ![A]) ⁻¹' {S}) = _
    rw [hcell]
    by_cases hS : S (.pred 0) <;> simp [c, hS, Set.compl_def]
  have key (M : Type u) (A : Set M) :
      (⟨M, monadic.structure ![A]⟩ : Bundled.{u} (Language.monadic (Fin 1)).Structure) ∈ Q ↔
        c #↥Aᶜ #↥A ∈ LindstromQuantifier.ofTypeCount.symm Q := by
    rw [← hc, ← LindstromQuantifier.mem_ofTypeCount, OrderIso.apply_symm_apply]
  refine ⟨fun k m ↦ c k m ∈ LindstromQuantifier.ofTypeCount.symm Q, key, fun R' hR' ↦ ?_⟩
  funext k m
  obtain ⟨⟨M, S⟩, hM⟩ := LindstromQuantifier.typeCount_surjective (c k m)
  obtain ⟨A, rfl⟩ : ∃ A : Set M, S = monadic.structure ![A] :=
    ⟨_, (monadic.eq_structure S).trans (by congr 1; exact funext (Fin.forall_fin_one.2 rfl))⟩
  rw [hc] at hM
  obtain rfl : #↥Aᶜ = k := by simpa [c] using congrFun hM fun _ ↦ False
  obtain rfl : #↥A = m := by simpa [c] using congrFun hM fun _ ↦ True
  exact propext ((hR' M A).symm.trans (key M A))

/-! ### First-order definability on the triangle -/

/-- Ch. 14, Fact 4: no sentence defines a properly proportional quantifier, even on finite
universes, though each is closed under isomorphism and so is a Lindström quantifier. Below any
line of the tree, `(n * (q - p), p * n)` and `(n * (q - p), p * n + 1)` still differ. -/
theorem not_foDefinable_thresholdGt {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    ¬ (NumberTree.thresholdGt p q).toFamily.FODefinable := by
  obtain ⟨r, rfl⟩ : ∃ r, q = p + (r + 1) := ⟨q - p - 1, by omega⟩
  rw [NumberTree.foDefinable_toFamily_iff]
  rintro ⟨n, h, -, -⟩
  have hle : n ≤ p * n := Nat.le_mul_of_pos_left n hp
  have ha : n ≤ n * (r + 1) := Nat.le_mul_of_pos_right n r.succ_pos
  have h' := ((h _ _ ha (by omega : n ≤ p * n + 1)).trans (h _ _ ha hle).symm).1
  simp only [NumberTree.thresholdGt, NumberTree.ofSizes_apply] at h'
  have hlt : p * (n * (r + 1) + (p * n + 1)) < (p + (r + 1)) * (p * n + 1) := by nlinarith
  have heq : p * (n * (r + 1) + p * n) = (p + (r + 1)) * (p * n) := by ring
  exact absurd (h' hlt) (by omega)

-- p. 468
theorem not_foDefinable_threshold {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    ¬ (NumberTree.threshold p q).toFamily.FODefinable := by
  obtain ⟨r, rfl⟩ : ∃ r, q = p + (r + 1) := ⟨q - p - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  rw [NumberTree.foDefinable_toFamily_iff]
  rintro ⟨n, h, -, -⟩
  have ha : n ≤ (n + 1) * (r + 1) := by nlinarith
  have h' := ((h _ _ ha (by omega : n ≤ s * (n + 1) + n + 1)).trans
    (h _ _ ha (by omega : n ≤ s * (n + 1) + n)).symm).1
  simp only [NumberTree.threshold, NumberTree.ofSizes_apply] at h'
  have heq : (s + 1) * ((n + 1) * (r + 1) + (s * (n + 1) + n + 1)) =
      (s + 1 + (r + 1)) * (s * (n + 1) + n + 1) := by ring
  have hlt : (s + 1 + (r + 1)) * (s * (n + 1) + n) <
      (s + 1) * ((n + 1) * (r + 1) + (s * (n + 1) + n)) := by nlinarith
  exact absurd (h' heq.le) (by omega)

-- p. 468
theorem not_foDefinable_most : ¬ (NumberTree.most.toFamily : Det.Family.{u}).FODefinable := by
  rw [← NumberTree.thresholdGt_one_two]
  exact not_foDefinable_thresholdGt one_pos one_lt_two

theorem foDefinable_atLeast (k : ℕ) :
    ((NumberTree.atLeast k).toFamily : Det.Family.{u}).FODefinable :=
  (NumberTree.foDefinable_toFamily_iff _).2
    ⟨k, fun _ _ _ _ ↦ by simp only [NumberTree.atLeast]; omega, fun _ _ _ _ ↦ .rfl,
      fun _ _ _ _ ↦ by simp only [NumberTree.atLeast]; omega⟩

theorem exists_toFamily_eq_thresholdGt (p q : ℕ) :
    ∃ D : Lindstrom.Det.{u}, D.toFamily = (NumberTree.thresholdGt p q).toFamily :=
  Lindstrom.isom_iff_exists_toFamily.1 (NumberTree.constant_toFamily _).isom

end Universals

end PetersWesterstahl2006
