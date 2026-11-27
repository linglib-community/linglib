/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Semantics.Degree.Marginality.Constructions

/-!
# Soritical arguments

A soritical argument for a predicate `P` along a relation `R` has three premises: a base case `a`
with `P`, tolerance, which says that `P` passes from `x` to `y` whenever `R x y`, and a
counterexample `b` without `P`. We define `Sorites P R a b` as their conjunction. Tolerance carries
`P` along every finite chain of `R`-steps from `a`, so the premises are jointly satisfiable by
some predicate exactly when no such chain reaches `b`.

On a marginal scale, a predicate closed downwards, as one true of the degrees below a standard
is, satisfies the premises along at most marginal differences exactly when `a` is largely smaller
than `b`. When the steps add a fixed positive amount `d` in a linearly ordered group, a downward
closed predicate is tolerant along them exactly when it is tolerant along the at most marginal
differences of the scale of the archimedean class of `d`. The premises are then satisfiable
exactly when `a < b` and `d` is negligible against `b - a`, the class of `d` lying above that of
`b - a`, which never happens in an archimedean group.

## Main definitions

* `Sorites`: the premises of a soritical argument.

## Main results

* `exists_sorites_iff`: some predicate satisfies the premises from `a` to `b` exactly when `b` is
  not reachable from `a`.
* `Sorites.swap`: the contrapositive argument, for the negated predicate along the converse
  relation from `b` to `a`.
* `Sorites.comap`: the premises pull back along a map that sends steps to steps.
* `MarginalScale.exists_isLowerSet_sorites_iff`: on a marginal scale, a downward closed
  predicate satisfies the premises along at most marginal differences exactly when `a` is largely
  smaller than `b`.
* `sorites_add_iff_sorites_atMostMarginal`: tolerance along steps of `d` is tolerance in the
  scale of the archimedean class of `d`.
* `exists_isLowerSet_sorites_add_iff`, `exists_isUpperSet_sorites_sub_iff`: along steps of `d` in
  an ordered group, a monotone predicate satisfies the premises exactly when `d` is negligible
  against the distance from `a` to `b`.
* `not_sorites_add_of_archimedean`: no downward closed predicate does in an archimedean group.

## Implementation notes

The conclusion of the argument, that `P` holds of everything reached from `a`, is not a field:
it follows from the base case and tolerance (`Sorites.of_reflTransGen`), and with the
counterexample it is the contradiction of the paradox.
-/

@[expose] public section

open Relation

/-- The premises of a soritical argument: a base case `a` with `P`, tolerance of `P` along `R`,
and a counterexample `b` without `P`. -/
structure Sorites {α : Type*} (P : α → Prop) (R : α → α → Prop) (a b : α) : Prop where
  /-- The base case has the property. -/
  base : P a
  /-- The property passes along a step. -/
  tolerance : ∀ ⦃x y⦄, P x → R x y → P y
  /-- The counterexample lacks the property. -/
  counter : ¬ P b

namespace Sorites

variable {α β : Type*} {P : α → Prop} {R : α → α → Prop} {a b y : α}

/-- The conclusion of a soritical argument: whatever is reached from the base case has the
property. -/
theorem of_reflTransGen (h : Sorites P R a b) (hy : ReflTransGen R a y) : P y := by
  induction hy with
  | refl => exact h.base
  | tail _ hcd ih => exact h.tolerance ih hcd

theorem not_reflTransGen (h : Sorites P R a b) : ¬ ReflTransGen R a b :=
  fun hab ↦ h.counter (h.of_reflTransGen hab)

/-- The contrapositive of a soritical argument is one for the negated predicate along the converse
relation, from the counterexample to the base case. -/
protected theorem swap (h : Sorites P R a b) : Sorites (¬ P ·) (Function.swap R) b a :=
  ⟨h.counter, fun _ _ hx hxy hy ↦ hx (h.tolerance hy hxy), not_not_intro h.base⟩

theorem mono {R' : α → α → Prop} (h : Sorites P R a b) (hR : ∀ x y, R' x y → R x y) :
    Sorites P R' a b :=
  ⟨h.base, fun _ _ hx hxy ↦ h.tolerance hx (hR _ _ hxy), h.counter⟩

/-- A soritical argument pulls back along a map that sends steps to steps. -/
theorem comap {S : β → β → Prop} {a b : β} (f : β → α) (h : Sorites P R (f a) (f b))
    (hf : ∀ x y, S x y → R (f x) (f y)) : Sorites (P ∘ f) S a b :=
  ⟨h.base, fun _ _ hx hxy ↦ h.tolerance hx (hf _ _ hxy), h.counter⟩

end Sorites

variable {α : Type*} {R : α → α → Prop} {a b : α}

theorem sorites_swap_iff {P : α → Prop} :
    Sorites (¬ P ·) (Function.swap R) b a ↔ Sorites P R a b :=
  ⟨fun h ↦ ⟨not_not.1 h.counter, fun _ _ hx hxy ↦ by_contra fun hy ↦ h.tolerance hy hxy hx,
    h.base⟩, Sorites.swap⟩

/-- Some predicate satisfies the premises of a soritical argument from `a` to `b` exactly when no
finite chain of steps leads from `a` to `b`. -/
theorem exists_sorites_iff : (∃ P, Sorites P R a b) ↔ ¬ ReflTransGen R a b :=
  ⟨fun ⟨_, h⟩ ↦ h.not_reflTransGen, fun h ↦ ⟨ReflTransGen R a, .refl, fun _ _ ↦ .tail, h⟩⟩

/-! ### Steps of a fixed amount -/

section Add

variable {M : Type*} [AddMonoid M] {a b d : M}

theorem reflTransGen_add_iff :
    ReflTransGen (fun x y ↦ y = x + d) a b ↔ ∃ n : ℕ, b = a + n • d := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · induction h with
    | refl => exact ⟨0, by simp⟩
    | tail _ hcd ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, by rw [hcd, succ_nsmul, add_assoc]⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => simp [ReflTransGen.refl]
    | succ n ih => exact ih.tail (by rw [succ_nsmul, add_assoc])

/-- A chain of steps of `d` along a map `s` leads from `a` to `b` when `s` is injective and
every intermediate value `s a + m • d` is the value of something. -/
theorem reflTransGen_of_forall_exists_eq_add {s : α → M} {d : M} {a b : α}
    (hs : Function.Injective s) {n : ℕ} (h : ∀ m < n, ∃ x, s x = s a + m • d)
    (hb : s b = s a + n • d) :
    ReflTransGen (fun x y ↦ s y = s x + d) a b := by
  induction n generalizing b with
  | zero =>
    obtain rfl : b = a := hs (by simpa using hb)
    exact .refl
  | succ n ih =>
    obtain ⟨x, hx⟩ := h n n.lt_succ_self
    exact (ih (fun m hm ↦ h m (hm.trans n.lt_succ_self)) hx).tail
      (by rw [hb, hx, succ_nsmul, add_assoc])

end Add

/-! ### Marginal scales -/

namespace MarginalScale

variable {α : Type*} [LinearOrder α] {ml : MarginalScale α} {a b S : α}

/-- Lying no further than the block of a standard is tolerant along at most marginal
differences. -/
theorem sorites_toBlock_le (ha : ml.toBlock a ≤ ml.toBlock S) (hb : ml.LargelyLT S b) :
    Sorites (fun x ↦ ml.toBlock x ≤ ml.toBlock S) ml.AtMostMarginal a b :=
  ⟨ha, fun _ _ hx hxy ↦ toBlock_eq_toBlock.2 hxy ▸ hx, (toBlock_lt_toBlock.2 hb).not_ge⟩

/-- A downward closed predicate satisfies the premises of a soritical argument from `a` to `b`
along at most marginal differences exactly when `a` is largely smaller than `b`. -/
theorem exists_isLowerSet_sorites_iff :
    (∃ P : α → Prop, IsLowerSet {x | P x} ∧ Sorites P ml.AtMostMarginal a b) ↔
      ml.LargelyLT a b :=
  ⟨fun ⟨_, hP, h⟩ ↦ largelyLT_iff_lt_and_not_atMostMarginal.2
      ⟨lt_of_not_ge fun hba ↦ h.counter (hP hba h.base),
        fun hab ↦ h.counter (h.tolerance h.base hab)⟩,
    fun h ↦ ⟨fun x ↦ ml.toBlock x ≤ ml.toBlock a, (IsLowerSet.Iic (ml.toBlock a)).preimage ml.toBlock_mono,
      sorites_toBlock_le le_rfl h⟩⟩

end MarginalScale

/-! ### Steps of a fixed amount in an ordered group -/

section OrderedGroup

open ArchimedeanClass MarginalScale

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] {a b d : M}

/-- A downward closed predicate is tolerant along steps of `d > 0` exactly when it is tolerant
along the at most marginal differences of the scale of the archimedean class of `d`. -/
theorem sorites_add_iff_sorites_atMostMarginal {P : M → Prop} (hd : 0 < d)
    (hP : IsLowerSet {x | P x}) : Sorites P (fun x y ↦ y = x + d) a b ↔
      Sorites P (ofArchimedeanClass (mk d)).AtMostMarginal a b := by
  refine ⟨fun h ↦ ⟨h.base, fun x y hx hxy ↦ ?_, h.counter⟩, fun h ↦ h.mono fun x y hxy ↦ ?_⟩
  · obtain ⟨n, hn⟩ := mk_le_mk.1 (ofArchimedeanClass_atMostMarginal_iff.1 hxy)
    rw [abs_of_pos hd] at hn
    exact hP (sub_le_iff_le_add'.1 ((le_abs_self _).trans hn))
      ((Sorites.mk hx h.tolerance h.counter).of_reflTransGen (reflTransGen_add_iff.2 ⟨n, rfl⟩))
  · rw [ofArchimedeanClass_atMostMarginal_iff, hxy, add_sub_cancel_left]

/-- Along steps of `d > 0`, a downward closed predicate satisfies the premises of a soritical
argument from `a` to `b` exactly when `a < b` and `d` is negligible against `b - a`. -/
theorem exists_isLowerSet_sorites_add_iff (hd : 0 < d) :
    (∃ P : M → Prop, IsLowerSet {x | P x} ∧ Sorites P (fun x y ↦ y = x + d) a b) ↔
      a < b ∧ mk (b - a) < mk d := by
  rw [← ofArchimedeanClass_largelyLT_iff, ← exists_isLowerSet_sorites_iff]
  exact exists_congr fun P ↦ and_congr_right (sorites_add_iff_sorites_atMostMarginal hd)

/-- Along steps of `-d < 0`, an upward closed predicate satisfies the premises of a soritical
argument from `a` to `b` exactly when `b < a` and `d` is negligible against `a - b`. -/
theorem exists_isUpperSet_sorites_sub_iff (hd : 0 < d) :
    (∃ P : M → Prop, IsUpperSet {x | P x} ∧ Sorites P (fun x y ↦ y = x - d) a b) ↔
      b < a ∧ mk (a - b) < mk d := by
  have hsw : Function.swap (fun x y : M ↦ y = x - d) = fun x y ↦ y = x + d := by
    ext x y
    exact eq_sub_iff_add_eq.trans eq_comm
  rw [← exists_isLowerSet_sorites_add_iff hd]
  refine ⟨fun ⟨P, hP, h⟩ ↦ ⟨(¬ P ·), fun x y hyx hx hy ↦ hx (hP hyx hy), hsw ▸ h.swap⟩,
    fun ⟨P, hP, h⟩ ↦ ⟨(¬ P ·), fun x y hxy hx hy ↦ hx (hP hxy hy), ?_⟩⟩
  rw [← hsw] at h
  convert h.swap using 1

/-- In an archimedean group no downward closed predicate satisfies the premises of a soritical
argument along steps of a positive amount. -/
theorem not_sorites_add_of_archimedean [Archimedean M] {P : M → Prop} (hd : 0 < d)
    (hP : IsLowerSet {x | P x}) : ¬ Sorites P (fun x y ↦ y = x + d) a b := fun h ↦
  not_ofArchimedeanClass_largelyLT hd.ne' <| exists_isLowerSet_sorites_iff.1
    ⟨P, hP, (sorites_add_iff_sorites_atMostMarginal hd hP).1 h⟩

end OrderedGroup
