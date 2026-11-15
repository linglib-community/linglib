/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Data.List.Lex
public import Mathlib.Order.Interval.Finset.Defs
public import Linglib.Core.Data.List.Infix
public import Linglib.Core.Order.LeftLinear

/-!
# Gorn addresses

A `GornAddress` is a position in a tree, written as in [gorn-1967]: the list of daughter indices
on the way down from the root. Addresses chain, with the root address as identity, so they form
the free monoid on `ℕ`, and his partial ordering of addresses puts an address below those it is a
head of: [`p ≤ q` exactly when `q = p * r` for some `r`](##GornAddress.le_iff_exists_mul), which
is divisibility. Under it the addresses form the rooted tree in which every node has a daughter for
each natural number, with the order structure of `Mathlib/Order/SuccPred/Tree.lean`: the root `1`
is least, `Order.pred` drops the last index, `p ⊓ q` is the longest common head, and strict
dominance is well founded. An address
[is covered exactly by its immediate successors `p * of i`](##GornAddress.covBy_iff), and
[lies below at most one of them](##GornAddress.of_inj_of_mul_of_le). Chaining on the left is an
order embedding and the depth of an address is additive. The addresses of a concrete tree form a
set closed under predecessors (`RoseTree.validPaths`); [gorn-1967] calls a finite such set, closed
also under earlier sisters, a tree domain.

`p` precedes `q` when the two part at some address with `p` taking the earlier daughter.
[Precedence is lexicographic order between addresses neither of which dominates the
other](##GornAddress.precedes_iff_lt_and_not_le). It is a decidable strict order, it passes to
dominated addresses, and [any two addresses are related by dominance or by
precedence](##GornAddress.Precedes.trichotomy).

Two addresses are left-aligned when they differ only in trailing first-daughter steps, so that the
subtrees at them begin with the same leaf, which is to say that
[descending through first daughters from each reaches a common
address](##GornAddress.leftAligned_iff_exists). Left-alignment is a decidable equivalence relation,
and left-aligned addresses lie on one branch.

## Implementation notes

The type is a structure over `List ℕ`, not a synonym of `FreeMonoid ℕ`, because lists carry the
lexicographic order that precedence compares against dominance; `GornAddress.toFreeMonoid` is the
isomorphism. Dominance unfolds to the prefix relation on the lists, and is divisibility by
`GornAddress.le_iff_dvd`. The order is one-sided: chaining on the left is monotone, chaining on the
right is
not, so the addresses are not a canonically ordered monoid.

## References

* [gorn-1967]
-/

@[expose] public section

/-- A Gorn address: the daughter indices on the way down from the root of a tree. -/
@[ext]
structure GornAddress where
  /-- The daughter indices, from the root down. -/
  toList : List ℕ
  deriving DecidableEq, Repr

attribute [coe] GornAddress.toList

/-- An address is read as its list of indices wherever a list is expected. -/
instance : CoeOut GornAddress (List ℕ) := ⟨GornAddress.toList⟩

namespace GornAddress

variable {p q r : GornAddress}

/-! ### Chaining -/

/-- The root address. -/
instance : One GornAddress := ⟨⟨[]⟩⟩

/-- Chaining: the address reached by following `q` from `p`. -/
instance : Mul GornAddress := ⟨fun p q ↦ ⟨p.toList ++ q.toList⟩⟩

@[simp] theorem toList_one : (1 : GornAddress).toList = [] := rfl

@[simp] theorem toList_mul (p q : GornAddress) : (p * q).toList = p.toList ++ q.toList := rfl

theorem toList_injective : Function.Injective toList := fun _ _ ↦ GornAddress.ext

instance : CancelMonoid GornAddress where
  mul_assoc _ _ _ := GornAddress.ext (List.append_assoc ..)
  one_mul _ := GornAddress.ext (List.nil_append _)
  mul_one _ := GornAddress.ext (List.append_nil _)
  mul_left_cancel _ _ _ h := GornAddress.ext (List.append_cancel_left (congrArg toList h))
  mul_right_cancel _ _ _ h := GornAddress.ext (List.append_cancel_right (congrArg toList h))

/-- The address of the `i`th daughter of the root. -/
def of (i : ℕ) : GornAddress := ⟨[i]⟩

@[simp] theorem toList_of (i : ℕ) : (of i).toList = [i] := rfl

theorem of_injective : Function.Injective of := fun _ _ h ↦ by
  simpa using congrArg toList h

/-- Addresses are the free monoid on the daughter indices. -/
def toFreeMonoid : GornAddress ≃* FreeMonoid ℕ where
  toFun p := FreeMonoid.ofList p.toList
  invFun w := ⟨FreeMonoid.toList w⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-! ### The partial ordering of addresses -/

/-- An address dominates the addresses it is a head of. -/
instance : LE GornAddress := ⟨fun p q ↦ p.toList <+: q.toList⟩

theorem le_def : p ≤ q ↔ p.toList <+: q.toList := Iff.rfl

/-- An address dominates another exactly when the other is obtained from it by chaining. -/
protected theorem le_iff_exists_mul : p ≤ q ↔ ∃ r, q = p * r :=
  ⟨fun ⟨l, hl⟩ ↦ ⟨⟨l⟩, GornAddress.ext hl.symm⟩,
    fun ⟨r, hr⟩ ↦ ⟨r.toList, (congrArg toList hr).symm⟩⟩

/-- Dominance is divisibility in the monoid of addresses. -/
theorem le_iff_dvd : p ≤ q ↔ p ∣ q := GornAddress.le_iff_exists_mul

@[simp] theorem mk_le_mk {l m : List ℕ} : (⟨l⟩ : GornAddress) ≤ ⟨m⟩ ↔ l <+: m := Iff.rfl

instance : DecidableLE GornAddress := fun _ _ ↦ decidable_of_iff _ le_def.symm

instance : PartialOrder GornAddress where
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ h₁ h₂ := GornAddress.ext
    ((le_def.1 h₁).eq_of_length ((le_def.1 h₁).length_le.antisymm (le_def.1 h₂).length_le))

instance : DecidableLT GornAddress := fun _ _ ↦ decidable_of_iff _ lt_iff_le_not_ge.symm

/-- The root address is the least address. -/
instance : OrderBot GornAddress where
  bot := 1
  bot_le _ := List.nil_prefix

instance : IsBotOneClass GornAddress := ⟨fun _ ↦ bot_le⟩

@[simp] theorem bot_toList : (⊥ : GornAddress).toList = [] := rfl

instance : ExistsMulOfLE GornAddress := ⟨GornAddress.le_iff_exists_mul.1⟩

instance : MulLeftMono GornAddress :=
  ⟨fun r _ _ h ↦ (List.prefix_append_right_inj r.toList).2 h⟩

instance : MulLeftReflectLE GornAddress :=
  ⟨by intro r p q h; exact le_def.2 ((List.prefix_append_right_inj r.toList).1 (le_def.1 h))⟩

instance : MulLeftReflectLT GornAddress :=
  ⟨by
    intro r p q h
    exact lt_of_le_of_ne (le_of_mul_le_mul_left' h.le) fun e ↦ h.ne (by rw [e])⟩

protected theorem le_mul_right (p q : GornAddress) : p ≤ p * q := List.prefix_append _ _

/-- Chaining an address on the left is an order embedding of addresses. -/
def mulLeft (r : GornAddress) : GornAddress ↪o GornAddress where
  toFun p := r * p
  inj' := mul_right_injective r
  map_rel_iff' := mul_le_mul_iff_left r

@[simp] theorem mulLeft_apply (r p : GornAddress) : mulLeft r p = r * p := rfl

/-- An address above a chained one is above the first part or is itself chained from it. -/
theorem le_mul_iff {s : GornAddress} : r ≤ s * p ↔ r ≤ s ∨ ∃ q, q ≤ p ∧ s * q = r := by
  constructor
  · intro hr
    have hr' : r.toList ∈ (s.toList ++ p.toList).inits := (List.mem_inits _ _).mpr hr
    rw [List.inits_append, List.mem_append] at hr'
    rcases hr' with hr' | hr'
    · exact .inl ((List.mem_inits _ _).mp hr')
    · obtain ⟨l, hl, e⟩ := List.mem_map.mp hr'
      exact .inr ⟨⟨l⟩, (List.mem_inits _ _).mp (List.mem_of_mem_tail hl), GornAddress.ext e⟩
  · rintro (hr | ⟨q, hq, rfl⟩)
    · exact hr.trans (GornAddress.le_mul_right s p)
    · exact mul_le_mul_right hq s

/-! ### Depth -/

/-- The depth of an address: the number of steps from the root. -/
def depth (p : GornAddress) : ℕ := p.toList.length

@[simp] theorem depth_one : depth 1 = 0 := rfl

@[simp] theorem depth_of (i : ℕ) : depth (of i) = 1 := rfl

@[simp] theorem depth_mul (p q : GornAddress) : depth (p * q) = depth p + depth q :=
  List.length_append

theorem depth_eq_zero : depth p = 0 ↔ p = 1 :=
  List.length_eq_zero_iff.trans GornAddress.ext_iff.symm

theorem depth_strictMono : StrictMono depth := fun _ _ h ↦
  (le_def.1 h.le).length_le.lt_of_ne fun hlen ↦
    h.ne (GornAddress.ext ((le_def.1 h.le).eq_of_length hlen))

instance : WellFoundedLT GornAddress := depth_strictMono.wellFoundedLT

/-- The addresses at or above an address are its heads, finitely many. -/
instance : LocallyFiniteOrderBot GornAddress :=
  .ofIic GornAddress (fun p ↦ (p.toList.inits.map GornAddress.mk).toFinset) fun a p ↦ by
    simp only [List.mem_toFinset, List.mem_map, List.mem_inits]
    exact ⟨fun ⟨l, hl, e⟩ ↦ e ▸ le_def.2 hl, fun h ↦ ⟨p.toList, le_def.1 h, rfl⟩⟩

/-! ### Parents -/

/-- The parent of an address drops its last index. The root is its own parent. -/
def parent (p : GornAddress) : GornAddress := ⟨p.toList.dropLast⟩

@[simp] theorem parent_toList (p : GornAddress) : p.parent.toList = p.toList.dropLast := rfl

@[simp] theorem parent_one : parent 1 = 1 := rfl

@[simp] theorem parent_mul_of (p : GornAddress) (i : ℕ) : (p * of i).parent = p :=
  GornAddress.ext (by simp)

theorem parent_mul (s : GornAddress) (hp : p ≠ 1) : (s * p).parent = s * p.parent :=
  GornAddress.ext (List.dropLast_append_of_ne_nil fun e ↦ hp (GornAddress.ext e))

theorem parent_le (p : GornAddress) : p.parent ≤ p := le_def.2 (List.dropLast_prefix p.toList)

theorem le_parent_of_lt (h : p < q) : p ≤ q.parent := by
  obtain ⟨s, hs⟩ := le_def.1 h.le
  have hs' : s ≠ [] := by
    rintro rfl
    exact h.ne (GornAddress.ext (by simpa using hs))
  rw [le_def, parent_toList, ← hs, List.dropLast_append_of_ne_nil hs']
  exact List.prefix_append _ _

instance : PredOrder GornAddress where
  pred := parent
  pred_le := parent_le
  min_of_le_pred {p} h := by
    have := (le_def.mp h).length_le
    rw [parent_toList, List.length_dropLast] at this
    obtain rfl : p = ⊥ := GornAddress.ext (List.eq_nil_of_length_eq_zero (by omega))
    exact isMin_bot
  le_pred_of_lt := le_parent_of_lt

@[simp] theorem pred_eq_parent (p : GornAddress) : Order.pred p = p.parent := rfl

/-! ### Immediate successors -/

theorem lt_mul_of (p : GornAddress) (i : ℕ) : p < p * of i :=
  lt_of_le_of_ne (GornAddress.le_mul_right p _) fun e ↦ by simpa using congrArg depth e

theorem covBy_mul_of (p : GornAddress) (i : ℕ) : p ⋖ p * of i := by
  simpa using Order.pred_covBy_of_not_isMin (not_isMin_of_lt (lt_mul_of p i))

/-- An address is covered exactly by its immediate successors. -/
theorem covBy_iff : p ⋖ q ↔ ∃ i, q = p * of i := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hq : q.toList ≠ [] := fun hq ↦ ne_bot_of_gt h.lt (GornAddress.ext hq)
    refine ⟨q.toList.getLast hq, GornAddress.ext ?_⟩
    rw [← Order.pred_eq_of_covBy h]
    exact (List.dropLast_concat_getLast hq).symm
  · rintro ⟨i, rfl⟩
    exact covBy_mul_of p i

/-- An address lies below at most one immediate successor of an address. -/
theorem of_inj_of_mul_of_le {i j : ℕ} (hi : p * of i ≤ q) (hj : p * of j ≤ q) : i = j :=
  of_injective <| mul_right_injective p <|
    IsLeftLinear.eq_of_covBy_of_le (covBy_mul_of p i) (covBy_mul_of p j) hi hj

/-- The addresses below distinct immediate successors are disjoint. -/
theorem disjoint_Ici_mul_of (p : GornAddress) {i j : ℕ} (h : i ≠ j) :
    Disjoint (Set.Ici (p * of i)) (Set.Ici (p * of j)) :=
  Set.disjoint_left.2 fun _ hi hj ↦ h (of_inj_of_mul_of_le hi hj)

/-! ### Least common ancestors -/

/-- The meet of two addresses is their longest common head, the deepest address dominating
both. -/
instance : SemilatticeInf GornAddress where
  inf p q := ⟨List.commonPrefix p.toList q.toList⟩
  inf_le_left p q := le_def.2 (List.commonPrefix_prefix_left p.toList q.toList)
  inf_le_right p q := le_def.2 (List.commonPrefix_prefix_right p.toList q.toList)
  le_inf _ _ _ h₁ h₂ := le_def.2 (List.prefix_commonPrefix (le_def.1 h₁) (le_def.1 h₂))

/-! ### Linear precedence -/

/-- `p` precedes `q` when, at some common address, `p` continues into an earlier daughter than
`q`. -/
def Precedes (p q : GornAddress) : Prop :=
  ∃ (r : GornAddress) (i j : ℕ), i < j ∧ r * of i ≤ p ∧ r * of j ≤ q

namespace Precedes

/-- An address comes lexicographically before every address it precedes. -/
protected theorem lt (h : Precedes p q) : p.toList < q.toList := by
  obtain ⟨r, i, j, hij, ⟨s, hp⟩, ⟨s', hq⟩⟩ := h
  rw [← hp, ← hq, toList_mul, toList_mul, toList_of, List.append_assoc, List.append_assoc]
  exact List.append_left_lt (List.cons_lt_cons_iff.mpr (.inl hij))

protected theorem not_le (h : Precedes p q) : ¬ p ≤ q := fun hle ↦ by
  obtain ⟨r, i, j, hij, hi, hj⟩ := h
  exact hij.ne (of_inj_of_mul_of_le (hi.trans hle) hj)

protected theorem not_ge (h : Precedes p q) : ¬ q ≤ p := fun hqp ↦ by
  obtain ⟨s, hs⟩ := le_def.1 hqp
  exact List.le_append_left (hs ▸ h.lt)

protected theorem mono {p' q' : GornAddress} (h : Precedes p q) (hp : p ≤ p') (hq : q ≤ q') :
    Precedes p' q' :=
  let ⟨r, i, j, hij, hi, hj⟩ := h
  ⟨r, i, j, hij, hi.trans hp, hj.trans hq⟩

/-- Precedence is preserved by chaining on the left. -/
theorem mul_left (s : GornAddress) (h : Precedes p q) : Precedes (s * p) (s * q) :=
  let ⟨r, a, b, hab, ha, hb⟩ := h
  ⟨s * r, a, b, hab, mul_assoc s r _ ▸ mul_le_mul_right ha s,
    mul_assoc s r _ ▸ mul_le_mul_right hb s⟩

theorem cons (i : ℕ) (h : Precedes p q) : Precedes ⟨i :: p.toList⟩ ⟨i :: q.toList⟩ :=
  h.mul_left (of i)

end Precedes

theorem precedes_cons_of_lt {i j : ℕ} (hij : i < j) (p q : GornAddress) :
    Precedes ⟨i :: p.toList⟩ ⟨j :: q.toList⟩ :=
  ⟨1, i, j, hij, le_def.2 (by simp), le_def.2 (by simp)⟩

/-- `p` precedes `q` exactly when `p` comes lexicographically before `q` without dominating it. -/
theorem precedes_iff_lt_and_not_le :
    Precedes p q ↔ p.toList < q.toList ∧ ¬ p ≤ q := by
  refine ⟨fun h ↦ ⟨h.lt, h.not_le⟩, fun ⟨hlt, hle⟩ ↦ ?_⟩
  rcases List.lt_iff_exists.mp hlt with ⟨h, -⟩ | ⟨i, h₁, h₂, heq, hi⟩
  · exact absurd (le_def.2 (List.prefix_iff_eq_take.mpr h)) hle
  · have htake : p.toList.take i = q.toList.take i := List.ext_getElem (by simp; omega)
      fun k hk _ ↦ by simp only [List.length_take] at hk; simpa using heq k (by omega)
    refine ⟨⟨p.toList.take i⟩, _, _, hi, le_def.2 ?_, le_def.2 ?_⟩
    · rw [toList_mul, toList_of, List.take_concat_get']
      exact List.take_prefix _ _
    · rw [toList_mul, toList_of, htake, List.take_concat_get']
      exact List.take_prefix _ _

instance (p q : GornAddress) : Decidable (Precedes p q) :=
  decidable_of_iff _ precedes_iff_lt_and_not_le.symm

namespace Precedes

protected theorem irrefl (p : GornAddress) : ¬ Precedes p p := fun h ↦ lt_irrefl _ h.lt

protected theorem asymm (h : Precedes p q) : ¬ Precedes q p := fun h' ↦ lt_asymm h.lt h'.lt

protected theorem trans (h₁ : Precedes p q) (h₂ : Precedes q r) : Precedes p r := by
  refine precedes_iff_lt_and_not_le.mpr ⟨h₁.lt.trans h₂.lt, fun hpr ↦ ?_⟩
  obtain ⟨s, k, l, hkl, hk, hl⟩ := h₂
  have hpr' := le_def.1 hpr
  have hk' : s.toList ++ [k] <+: q.toList := le_def.1 hk
  have hl' : s.toList ++ [l] <+: r.toList := le_def.1 hl
  rcases le_or_gt p.toList.length s.toList.length with hlen | hlen
  · -- `p` dominates the address where `q` and `r` part, hence dominates `q`
    exact h₁.not_le <| le_def.2 <| (List.prefix_of_prefix_length_le hpr'
      ((List.prefix_append _ _).trans hl') hlen).trans ((List.prefix_append _ _).trans hk')
  · -- `p` lies inside `r`'s branch at that address, so `q` precedes `p`
    exact h₁.asymm ⟨s, k, l, hkl, hk,
      le_def.2 (List.prefix_of_prefix_length_le hl' hpr' (by simpa))⟩

instance : IsStrictOrder GornAddress Precedes where
  irrefl := Precedes.irrefl
  trans _ _ _ := Precedes.trans

/-- Any two addresses are related by dominance or by precedence. -/
protected theorem trichotomy (p q : GornAddress) :
    p ≤ q ∨ q ≤ p ∨ Precedes p q ∨ Precedes q p := by
  by_cases hpq : p ≤ q
  · exact .inl hpq
  by_cases hqp : q ≤ p
  · exact .inr (.inl hqp)
  rcases lt_trichotomy p.toList q.toList with h | h | h
  · exact .inr (.inr (.inl (precedes_iff_lt_and_not_le.mpr ⟨h, hpq⟩)))
  · exact absurd (GornAddress.ext h).le hpq
  · exact .inr (.inr (.inr (precedes_iff_lt_and_not_le.mpr ⟨h, hqp⟩)))

end Precedes

/-! ### Left edges -/

/-- Two positions are left-aligned when their addresses agree once trailing first-daughter steps
are dropped, so that the subtrees at them begin with the same leaf. -/
def LeftAligned (p q : GornAddress) : Prop :=
  p.toList.reverse.dropWhile (· == 0) = q.toList.reverse.dropWhile (· == 0)

instance : DecidableRel LeftAligned := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

namespace LeftAligned

variable {p q r : GornAddress}

@[refl] protected theorem refl (p : GornAddress) : LeftAligned p p := rfl

@[symm] protected theorem symm (h : LeftAligned p q) : LeftAligned q p := Eq.symm h

@[trans] protected theorem trans (h₁ : LeftAligned p q) (h₂ : LeftAligned q r) :
    LeftAligned p r :=
  Eq.trans h₁ h₂

end LeftAligned

private theorem dropWhile_reverse_append_replicate (l : List ℕ) (k : ℕ) :
    (l ++ List.replicate k 0).reverse.dropWhile (· == 0) = l.reverse.dropWhile (· == 0) := by
  rw [List.reverse_append, List.reverse_replicate]
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.dropWhile_cons_of_pos rfl, ih]

private theorem exists_eq_reverse_dropWhile_append (l : List ℕ) :
    ∃ k, l = (l.reverse.dropWhile (· == 0)).reverse ++ List.replicate k 0 := by
  refine ⟨(l.reverse.takeWhile (· == 0)).length, ?_⟩
  have h := congrArg List.reverse (List.takeWhile_append_dropWhile (p := (· == 0)) (l := l.reverse))
  rw [List.reverse_append, List.reverse_reverse] at h
  rw [← List.eq_replicate_iff.2 ⟨List.length_reverse, fun x hx ↦ ?_⟩, h]
  exact beq_iff_eq.1 (List.all_eq_true.1 List.all_takeWhile x (List.mem_reverse.1 hx))

/-- Positions are left-aligned exactly when descending through first daughters from each reaches
a common position. -/
theorem leftAligned_iff_exists {p q : GornAddress} :
    LeftAligned p q ↔
      ∃ j k, p.toList ++ List.replicate j 0 = q.toList ++ List.replicate k 0 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_eq_reverse_dropWhile_append p.toList
    obtain ⟨k, hk⟩ := exists_eq_reverse_dropWhile_append q.toList
    refine ⟨k, j, ?_⟩
    rw [hj, hk, h, List.append_assoc, List.append_assoc, List.replicate_append_replicate,
      List.replicate_append_replicate, Nat.add_comm]
  · rintro ⟨j, k, h⟩
    simpa only [LeftAligned, dropWhile_reverse_append_replicate] using
      congrArg (fun l ↦ l.reverse.dropWhile (· == 0)) h

theorem LeftAligned.le_or_ge {p q : GornAddress} (h : LeftAligned p q) : p ≤ q ∨ q ≤ p := by
  obtain ⟨j, k, h⟩ := leftAligned_iff_exists.1 h
  have hq : q.toList <+: p.toList ++ List.replicate j 0 := h ▸ List.prefix_append _ _
  exact (List.prefix_or_prefix_of_prefix (List.prefix_append _ _) hq).imp le_def.2 le_def.2

end GornAddress
