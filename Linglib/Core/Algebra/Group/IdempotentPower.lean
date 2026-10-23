/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Free
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Idempotents in finite semigroups

This file proves the basic facts about idempotents in finite monoids and semigroups. In a finite
monoid the powers of an element must repeat, so some positive power of every element is
idempotent; adjoining an identity transfers this to semigroups, and in particular every nonempty
finite semigroup contains an idempotent.

The main result is the factorization of long products: if `S` is a finite semigroup with `n`
elements, every product `s₁ ⋯ sₙ` has a prefix `s₁ ⋯ sᵢ` fixed on the right by an idempotent `e`,
and so lies in `S e S`.

## Main results

* `Monoid.exists_pos_pow_isIdempotent`: every element of a finite monoid has an idempotent
  positive power.
* `Semigroup.exists_isIdempotentElem`: a nonempty finite semigroup contains an idempotent.
* `Semigroup.exists_isIdempotentElem_map_eq`: a surjective homomorphism of finite semigroups lifts
  idempotents to idempotents.
* `Semigroup.exists_lt_card_isIdempotentElem_mul_eq`: among the first `|S|` terms of a sequence in
  which each term is a right multiple of the previous one, some term is fixed on the right by an
  idempotent.
* `FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul`: a homomorphism out of the free semigroup
  sends every word of length at least `|S|` into `S e S` for an idempotent `e`.

## Implementation notes

The last two results are Proposition II.6.34 and Corollary II.6.35 of Pin's lecture notes.
Products of sequences are expressed through a homomorphism out of `FreeSemigroup α`, which covers
products of arbitrary elements by taking `α = S` and `FreeSemigroup.lift id`.

## References

* [pin-mfa]
* [eilenberg-1976]
-/

@[expose] public section

namespace Monoid

variable {M : Type*} [Monoid M]

/-! ### Periodicity of powers -/

private lemma pow_add_step {x : M} {a b : ℕ} (h : x ^ a = x ^ b) (k : ℕ) :
    x ^ (a + k) = x ^ (b + k) := by
  rw [pow_add, pow_add, h]

private lemma pow_period {x : M} {i j : ℕ} (h_le : i ≤ j) (h_eq : x ^ i = x ^ j)
    {n : ℕ} (hn : i ≤ n) (m : ℕ) : x ^ n = x ^ (n + m * (j - i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have step := pow_add_step h_eq (n - i + m * (j - i))
    rw [show i + (n - i + m * (j - i)) = n + m * (j - i) by omega,
        show j + (n - i + m * (j - i)) = n + m * (j - i) + (j - i) by omega] at step
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact ih.trans step

variable [Finite M]

/-! ### Existence of an idempotent power -/

theorem exists_pow_eq_pow_of_finite (x : M) :
    ∃ i j : ℕ, i < j ∧ x ^ i = x ^ j := by
  obtain ⟨i, j, hij, h_eq⟩ :=
    Set.finite_univ.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ ↦ x ^ n) (fun _ ↦ Set.mem_univ _)
  exact ⟨i, j, hij, h_eq⟩

theorem exists_pos_pow_isIdempotent (x : M) :
    ∃ n > 0, IsIdempotentElem (x ^ n) := by
  obtain ⟨i, j, hij, h_eq⟩ := exists_pow_eq_pow_of_finite x
  have hp : 0 < j - i := Nat.sub_pos_of_lt hij
  have hj : 0 < j := (Nat.zero_le i).trans_lt hij
  refine ⟨j * (j - i), Nat.mul_pos hj hp, ?_⟩
  show x ^ (j * (j - i)) * x ^ (j * (j - i)) = x ^ (j * (j - i))
  rw [← pow_add]
  exact (pow_period hij.le h_eq (hij.le.trans (Nat.le_mul_of_pos_right j hp)) j).symm

end Monoid

/-! ### Semigroups: transfer through `WithOne`

`WithOne S` is a finite monoid when `S` is a finite semigroup, positive
powers of a coerced element are themselves coerced, and `WithOne.coe_inj`
transfers idempotency back. The payoff is the structural fact behind the
equational description of semigroup pseudovarieties: a preimage of an
idempotent need not be idempotent, but an idempotent *power* of a
preimage is one and has the same image. -/

namespace WithOne

variable {S : Type*} [Semigroup S]

/-- `WithOne S` is `Option S`, so it inherits finiteness. -/
instance instFinite [Finite S] : Finite (WithOne S) := inferInstanceAs (Finite (Option S))

@[simp] theorem isIdempotentElem_coe {e : S} :
    IsIdempotentElem ((e : WithOne S)) ↔ IsIdempotentElem e := by
  rw [IsIdempotentElem, ← WithOne.coe_mul, WithOne.coe_inj]; rfl

theorem exists_coe_pow (x : S) : ∀ n : ℕ, 0 < n → ∃ y : S, (x : WithOne S) ^ n = y
  | 1, _ => ⟨x, pow_one _⟩
  | n + 2, _ => by
    obtain ⟨y, hy⟩ := exists_coe_pow x (n + 1) n.succ_pos
    exact ⟨x * y, by rw [pow_succ', hy, ← WithOne.coe_mul]⟩

end WithOne

namespace Semigroup

variable {S T : Type*} [Semigroup S] [Semigroup T] [Finite S]

private theorem exists_pos_pow_isIdempotentElem_coe (x : S) :
    ∃ (n : ℕ) (e : S), 0 < n ∧ (x : WithOne S) ^ n = e ∧ IsIdempotentElem e := by
  obtain ⟨n, hn, hidem⟩ := Monoid.exists_pos_pow_isIdempotent (x : WithOne S)
  obtain ⟨e, he⟩ := WithOne.exists_coe_pow x n hn
  exact ⟨n, e, hn, he, WithOne.isIdempotentElem_coe.1 (he ▸ hidem)⟩

theorem exists_isIdempotentElem [Nonempty S] : ∃ e : S, IsIdempotentElem e :=
  have ⟨x⟩ := ‹Nonempty S›
  have ⟨_, e, _, _, he⟩ := exists_pos_pow_isIdempotentElem_coe x
  ⟨e, he⟩

theorem exists_isIdempotentElem_map_eq {f : S →ₙ* T} (hf : Function.Surjective f) {e' : T}
    (he' : IsIdempotentElem e') : ∃ e : S, IsIdempotentElem e ∧ f e = e' := by
  obtain ⟨x, rfl⟩ := hf e'
  obtain ⟨n, e, hn, he, hidem⟩ := exists_pos_pow_isIdempotentElem_coe x
  refine ⟨e, hidem, ?_⟩
  have hmap : (WithOne.mapMulHom f) ((x : WithOne S) ^ n) = ((f x : T) : WithOne T) ^ n := by
    rw [map_pow, WithOne.mapMulHom_coe]
  rw [he, WithOne.mapMulHom_coe] at hmap
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rwa [(WithOne.isIdempotentElem_coe.2 he').pow_succ_eq, WithOne.coe_inj] at hmap

/-! ### Long products -/

theorem exists_isIdempotentElem_mul_eq {p u : S} (h : p * u = p) :
    ∃ e, IsIdempotentElem e ∧ p * e = p := by
  obtain ⟨n, e, -, hu, he⟩ := exists_pos_pow_isIdempotentElem_coe u
  refine ⟨e, he, WithOne.coe_inj.1 ?_⟩
  have hpow : ∀ k : ℕ, (p : WithOne S) * (u : WithOne S) ^ k = p := fun k ↦ by
    induction k with
    | zero => rw [pow_zero, mul_one]
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, ← WithOne.coe_mul, h]
  rw [WithOne.coe_mul, ← hu, hpow]

theorem exists_lt_card_isIdempotentElem_mul_eq [Nonempty S] {p : ℕ → S}
    (hp : ∀ k, k + 1 < Nat.card S → ∃ s, p (k + 1) = p k * s) :
    ∃ i < Nat.card S, ∃ e, IsIdempotentElem e ∧ p i * e = p i := by
  have chain {i j : ℕ} (hij : i < j) (hj : j < Nat.card S) : ∃ s, p j = p i * s := by
    induction j, hij using Nat.le_induction with
    | base => exact hp i hj
    | succ j hij ih =>
      obtain ⟨s, hs⟩ := ih (by omega)
      obtain ⟨s', hs'⟩ := hp j hj
      exact ⟨s * s', by rw [hs', hs, mul_assoc]⟩
  have fixed {i j : Fin (Nat.card S)} (hij : (i : ℕ) < j) (h : p i = p j) :
      ∃ i < Nat.card S, ∃ e, IsIdempotentElem e ∧ p i * e = p i := by
    obtain ⟨s, hs⟩ := chain hij j.2
    exact ⟨i, i.2, exists_isIdempotentElem_mul_eq (hs.symm.trans h.symm)⟩
  -- Pigeonhole on the first `|S|` terms together with an idempotent `e₀`.
  obtain ⟨e₀, he₀⟩ := exists_isIdempotentElem (S := S)
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.1 fun hinj ↦ by
    simpa using Nat.card_le_card_of_injective
      (fun o : Option (Fin (Nat.card S)) ↦ o.elim e₀ (p ·)) hinj
  rcases x with _ | i <;> rcases y with _ | j <;> simp only [Option.elim] at hxy
  · exact absurd rfl hne
  · exact ⟨j, j.2, e₀, he₀, by rw [← hxy, he₀.eq]⟩
  · exact ⟨i, i.2, e₀, he₀, by rw [hxy, he₀.eq]⟩
  · have hij : (i : ℕ) ≠ j := fun h ↦ hne (congrArg some (Fin.ext h))
    rcases lt_or_gt_of_ne hij with hij | hij
    exacts [fixed hij hxy, fixed hij hxy.symm]

end Semigroup

namespace FreeSemigroup

variable {α S : Type*} [Semigroup S] (f : FreeSemigroup α →ₙ* S)

theorem exists_le_length_map_eq {u : FreeSemigroup α} (hu : IsIdempotentElem (f u)) (n : ℕ) :
    ∃ v, n ≤ v.length ∧ f v = f u := by
  induction n with
  | zero => exact ⟨u, Nat.zero_le _, rfl⟩
  | succ n ih =>
    obtain ⟨v, hv, hfv⟩ := ih
    refine ⟨u * v, ?_, by rw [map_mul, hfv, hu.eq]⟩
    have : 0 < u.length := Nat.succ_pos _
    rw [length_mul]; omega

theorem exists_isIdempotentElem_map_eq_mul_mul [Finite S] {w : FreeSemigroup α}
    (hw : Nat.card S ≤ w.length) : ∃ x e y, IsIdempotentElem e ∧ f w = x * e * y := by
  obtain ⟨a, t⟩ := w
  have : Nonempty S := ⟨f ⟨a, t⟩⟩
  replace hw : Nat.card S ≤ t.length + 1 := hw
  -- The prefix of length `k + 1` extends the prefix of length `k` by the letter `t[k]`.
  obtain ⟨i, -, e, he, hpe⟩ :=
    Semigroup.exists_lt_card_isIdempotentElem_mul_eq (p := fun k ↦ f ⟨a, t.take k⟩) fun k hk ↦ by
      have hk : k < t.length := by omega
      refine ⟨f (of t[k]), ?_⟩
      rw [← map_mul]
      congr 1
      refine FreeSemigroup.ext rfl ?_
      show t.take (k + 1) = t.take k ++ [t[k]]
      rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  rcases h : t.drop i with _ | ⟨b, r⟩
  · refine ⟨f ⟨a, t.take i⟩, e, e, he, ?_⟩
    rw [mul_assoc, he.eq, hpe, List.take_of_length_le (List.drop_eq_nil_iff.1 h)]
  · refine ⟨f ⟨a, t.take i⟩, e, f ⟨b, r⟩, he, ?_⟩
    rw [hpe, ← map_mul]
    congr 1
    refine FreeSemigroup.ext rfl ?_
    show t = t.take i ++ b :: r
    rw [← h, List.take_append_drop]

end FreeSemigroup
