/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Dimensioned parthood

Mereological syntax builds structure by Subjoin, which makes one syntactic object a proper part
of another. No new object is formed: after `x` subjoins to `y`, the object `y` has `x` as a part.
An object has parts in two dimensions. Its 1-part is its extended-projection complement and its
2-part is its specifier. In *you jumped*, `V` is the 1-part of `v` and `v` the 1-part of `T`, and
the subject is the 2-part of `v` and also of `T`. An object may be a part of several others in
this way, which is how one object occupies several positions.

A parthood structure on `α` is a function `part : Dim → α → Option α` giving the immediate
`n`-part of each object, if it has one. `x` is an `n`-part of `y` when it is reached from `y`
through immediate `n`-parts: `P.NPart n` is the transitive closure of `P.Imm n`. So the 1-parts of
an object are the heads below it in its extended projection, and its 2-parts are its specifier,
the specifier of that, and so on. Parthood is transitive within a dimension only. A 1-part of a
specifier of `y` is inside `y`, in the sense of `P.Descendant`, the closure through both
dimensions, but that does not make it a 1-part or a 2-part of `y`. The locality principle of
mereological syntax is stated with this difference.

A structure is acyclic when no object is inside itself. In an acyclic structure each `P.NPart n`
is a strict partial order, as proper parthood is required to be, and no two objects are parts of
each other, in the same dimension or in different ones.

Structures are ordered by inclusion of immediate parthood, and the least structure is the one in
which nothing has a part. Subjoining `x` to `y` makes `x` the immediate part of `y` in the first
dimension in which `y` has no part: the first subjunction to an object gives it a complement and
the second a specifier. There is no third, so Subjoin is undefined on an object with both parts,
and structures branch at most twice. Where it is defined, Subjoin adds one immediate part and
removes none, so it moves up in the order.

## Main definitions

* `MereologicalSyntax.Parthood`: the immediate parts of each object, in each dimension.
* `Parthood.NPart`: parthood within a dimension.
* `Parthood.Acyclic`: no object is its own descendant.
* `Parthood.subjoin`: Subjoin, in the next free dimension of the target.

## Main results

* `Parthood.Acyclic.isStrictOrder`: in an acyclic structure, parthood within a dimension is a
  strict partial order.
* `Parthood.imm_subjoin_iff`: Subjoin adds exactly one immediate part, in the dimension that
  Dimensionality assigns.
* `Parthood.subjoin_eq_none_iff`: Subjoin is undefined exactly on a target with a part in both
  dimensions.

## Implementation notes

* A structure is a function into `Option`, not a relation with a uniqueness proof. An object has
  at most one immediate `n`-part, so its `n`-parts form a chain, and on a finite type `NPart n`
  is decided by following the function (`Relation.ReflTransGen.decidable_TransGen_of_option`).
  `Descendant` branches, and is decided by closing a set.
* [adger-2025] requires proper parthood to be irreflexive, transitive and asymmetric, with
  transitivity confined to a dimension. `Acyclic` excludes every cycle of immediate parts, one
  that changes dimension included, and these conditions follow from it. It is a property of
  structures and not a check inside `subjoin`; the licensed subjunctions of `Parthood.Subjoins`
  preserve it.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax

/-- The two dimensions of parthood, the extended-projection complement (1-part) and the specifier
(2-part). -/
inductive Parthood.Dim
  | one
  | two
  deriving DecidableEq, Repr, Fintype

/-- A dimensioned parthood structure on `α` gives each object at most one immediate part in each
dimension. -/
@[ext]
structure Parthood (α : Type*) where
  /-- The immediate `n`-part of an object, if any. -/
  part : Parthood.Dim → α → Option α

namespace Parthood

open Relation

variable {α : Type*} (P : Parthood α)

instance [Fintype α] [DecidableEq α] : DecidableEq (Parthood α) := fun _ _ ↦
  decidable_of_iff _ Parthood.ext_iff.symm

/-! ### Parthood relations -/

/-- `x` is the immediate `n`-part of `y`: its complement for `n = 1`, its specifier for `n = 2`. -/
def Imm (n : Dim) (x y : α) : Prop := P.part n y = some x

/-- `x` is an `n`-part of `y`, through a chain of immediate `n`-parts. -/
def NPart (n : Dim) : α → α → Prop := TransGen (P.Imm n)

/-- `x` is inside `y`: it is reached from `y` through parts of either dimension. -/
def Descendant : α → α → Prop := TransGen fun x y ↦ ∃ n, P.Imm n x y

/-- `x` is a part of something, and so not a root. -/
def IsPart (x : α) : Prop := ∃ n y, P.Imm n x y

/-- No object is inside itself, through parts of either dimension. -/
def Acyclic : Prop := ∀ x, ¬ P.Descendant x x

/-- Only an object with a 1-part has a 2-part, since Subjoin fills the first dimension first. -/
def Dimensional : Prop := ∀ y, (P.part .two y).isSome → (P.part .one y).isSome

instance [DecidableEq α] (n : Dim) : DecidableRel (P.Imm n) := fun _ _ ↦
  inferInstanceAs (Decidable (_ = _))

section Fintype

variable [Fintype α] [DecidableEq α]

instance (n : Dim) : DecidableRel (P.NPart n) := fun x y ↦
  haveI := ReflTransGen.decidable_TransGen_of_option (P.part n) y x
  decidable_of_iff _ transGen_swap

instance : DecidableRel P.Descendant := fun x y ↦
  haveI := ReflTransGen.decidable_TransGen_of_fintype_step
    (r := Function.swap fun x y ↦ ∃ n, P.Imm n x y)
    (fun y ↦ Finset.univ.biUnion fun n ↦ (P.part n y).toFinset)
    (fun _ _ ↦ by simp [Function.swap, Imm]) y x
  decidable_of_iff _ transGen_swap

instance : DecidablePred P.IsPart := fun _ ↦ inferInstanceAs (Decidable (∃ _ _, _))

instance : Decidable P.Acyclic := inferInstanceAs (Decidable (∀ _, _))

instance : Decidable P.Dimensional := inferInstanceAs (Decidable (∀ _, _))

end Fintype

variable {P} {Q : Parthood α} {m n : Dim} {x y z : α}

/-- An object has at most one immediate `n`-part. -/
theorem leftUnique_imm : Relator.LeftUnique (P.Imm n) := fun _ _ _ h h' ↦
  Option.some_injective _ (h.symm.trans h')

instance : IsTrans α (P.NPart n) := ⟨fun _ _ _ ↦ TransGen.trans⟩

theorem NPart.trans (h₁ : P.NPart n x y) (h₂ : P.NPart n y z) : P.NPart n x z :=
  TransGen.trans h₁ h₂

theorem descendant_of_nPart (h : P.NPart n x y) : P.Descendant x y :=
  TransGen.mono (fun _ _ h ↦ ⟨n, h⟩) _ _ h

theorem Descendant.trans (h₁ : P.Descendant x y) (h₂ : P.Descendant y z) : P.Descendant x z :=
  TransGen.trans h₁ h₂

theorem Descendant.isPart (h : P.Descendant x y) : P.IsPart x :=
  let ⟨_, hxb, _⟩ := TransGen.head'_iff.1 h
  let ⟨n, hn⟩ := hxb
  ⟨n, _, hn⟩

/-- The `n`-parts of an object are its immediate `n`-part and the `n`-parts of that part. -/
theorem NPart.eq_or_nPart_of_imm (hz : P.Imm n z y) (h : P.NPart n x y) :
    x = z ∨ P.NPart n x z := by
  obtain ⟨z', hxz', hz'y⟩ := TransGen.tail'_iff.1 h
  obtain rfl := leftUnique_imm hz'y hz
  exact (reflTransGen_iff_eq_or_transGen.1 hxz').imp_left Eq.symm

/-! ### Acyclic structures -/

namespace Acyclic

theorem not_nPart_self (hP : P.Acyclic) : ¬ P.NPart n x x := fun h ↦
  hP x (descendant_of_nPart h)

/-- In an acyclic structure no two objects are parts of each other, in whatever dimensions. -/
theorem not_nPart_of_nPart (hP : P.Acyclic) (h : P.NPart n x y) : ¬ P.NPart m y x := fun h' ↦
  hP x ((descendant_of_nPart h).trans (descendant_of_nPart h'))

/-- In an acyclic structure, parthood within a dimension is a strict partial order. -/
theorem isStrictOrder (hP : P.Acyclic) (n : Dim) : IsStrictOrder α (P.NPart n) where
  irrefl _ := hP.not_nPart_self

end Acyclic

/-! ### Extension -/

theorem imm_injective : Function.Injective (Imm : Parthood α → Dim → α → α → Prop) :=
  fun _ _ h ↦ Parthood.ext <| funext₂ fun n y ↦ Option.ext fun x ↦ iff_of_eq congr($h n x y)

/-- `P ≤ Q` when every immediate part in `P` is one in `Q`. -/
instance : PartialOrder (Parthood α) := PartialOrder.lift Imm imm_injective

theorem le_iff : P ≤ Q ↔ ∀ n x y, P.Imm n x y → Q.Imm n x y := Iff.rfl

/-- Immediate parthood, as an order embedding of structures into families of relations. -/
def immOrderEmbedding : Parthood α ↪o (Dim → α → α → Prop) := ⟨⟨Imm, imm_injective⟩, Iff.rfl⟩

@[simp] theorem coe_immOrderEmbedding : ⇑(immOrderEmbedding (α := α)) = Imm := rfl

/-- The structure in which nothing has a part, from which a derivation starts. -/
instance : OrderBot (Parthood α) where
  bot := ⟨fun _ _ ↦ none⟩
  bot_le _ _ _ _ h := nomatch h

@[simp] theorem part_bot (n : Dim) (y : α) : (⊥ : Parthood α).part n y = none := rfl

@[simp] theorem not_imm_bot : ¬ (⊥ : Parthood α).Imm n x y := nofun

theorem Imm.mono (h : P ≤ Q) (hxy : P.Imm n x y) : Q.Imm n x y := h n x y hxy

theorem NPart.mono (h : P ≤ Q) (hxy : P.NPart n x y) : Q.NPart n x y :=
  TransGen.mono (fun _ _ ↦ Imm.mono h) _ _ hxy

theorem Descendant.mono (h : P ≤ Q) (hxy : P.Descendant x y) : Q.Descendant x y :=
  TransGen.mono (fun _ _ ⟨n, hn⟩ ↦ ⟨n, hn.mono h⟩) _ _ hxy

theorem IsPart.mono (h : P ≤ Q) (hx : P.IsPart x) : Q.IsPart x :=
  let ⟨n, y, hy⟩ := hx
  ⟨n, y, hy.mono h⟩

theorem Acyclic.anti (h : P ≤ Q) (hQ : Q.Acyclic) : P.Acyclic := fun x hx ↦ hQ x (hx.mono h)

@[simp] theorem not_isPart_bot : ¬ (⊥ : Parthood α).IsPart x := fun ⟨_, _, h⟩ ↦ not_imm_bot h

@[simp] theorem acyclic_bot : (⊥ : Parthood α).Acyclic := fun _ h ↦ not_isPart_bot h.isPart

@[simp] theorem dimensional_bot : (⊥ : Parthood α).Dimensional := nofun

/-! ### Subjoin -/

variable (P) in
/-- The dimension of the next subjunction to `y`: the first if `y` has no 1-part, the second if it
has a 1-part only, and none if it has both (Dimensionality). -/
def nextDim (y : α) : Option Dim :=
  match P.part .one y, P.part .two y with
  | none, _ => some .one
  | some _, none => some .two
  | some _, some _ => none

theorem nextDim_eq_one_iff : P.nextDim y = some .one ↔ P.part .one y = none := by
  unfold nextDim
  split <;> simp_all

theorem nextDim_eq_two_iff :
    P.nextDim y = some .two ↔ (P.part .one y).isSome ∧ P.part .two y = none := by
  unfold nextDim
  split <;> simp_all

theorem nextDim_eq_none_iff :
    P.nextDim y = none ↔ (P.part .one y).isSome ∧ (P.part .two y).isSome := by
  unfold nextDim
  split <;> simp_all

theorem part_eq_none_of_nextDim (h : P.nextDim y = some n) : P.part n y = none := by
  cases n
  exacts [nextDim_eq_one_iff.1 h, (nextDim_eq_two_iff.1 h).2]

theorem nextDim_eq_two (h₁ : (P.part .one y).isSome) (h : P.nextDim y = some n) : n = .two := by
  cases n
  · simp [nextDim_eq_one_iff.1 h] at h₁
  · rfl

variable [DecidableEq α]

variable (P) in
/-- `P` with `x` as the immediate `n`-part of `y`. -/
def addPart (n : Dim) (x y : α) : Parthood α :=
  ⟨Function.update P.part n (Function.update (P.part n) y (some x))⟩

variable (P) in
/-- Subjoin `x` to `y`, adding it in the next free dimension of `y`: as its complement if it has
none, and otherwise as its specifier. -/
def subjoin (x y : α) : Option (Parthood α) := (P.nextDim y).map (P.addPart · x y)

theorem part_addPart (m : Dim) (b : α) :
    (P.addPart n x y).part m b = if m = n ∧ b = y then some x else P.part m b := by
  by_cases hm : m = n
  · subst hm
    simp [addPart, Function.update_apply]
  · simp [addPart, hm]

theorem imm_addPart_iff (h : P.part n y = none) {a b : α} :
    (P.addPart n x y).Imm m a b ↔ P.Imm m a b ∨ (m = n ∧ a = x ∧ b = y) := by
  simp only [Imm, part_addPart]
  split_ifs with hmb
  · obtain ⟨rfl, rfl⟩ := hmb
    simp [h, eq_comm]
  · exact ⟨.inl, fun h ↦ h.resolve_right fun ⟨h₁, _, h₂⟩ ↦ hmb ⟨h₁, h₂⟩⟩

theorem le_addPart (h : P.part n y = none) : P ≤ P.addPart n x y := fun _ _ _ hab ↦
  (imm_addPart_iff h).2 (.inl hab)

theorem subjoin_eq_some_iff :
    P.subjoin x y = some Q ↔ ∃ n, P.nextDim y = some n ∧ P.addPart n x y = Q :=
  Option.map_eq_some_iff

/-- Subjoin is undefined exactly on a target with a part in both dimensions (Dimensionality). -/
theorem subjoin_eq_none_iff :
    P.subjoin x y = none ↔ (P.part .one y).isSome ∧ (P.part .two y).isSome := by
  rw [subjoin, Option.map_eq_none_iff, nextDim_eq_none_iff]

theorem imm_subjoin_iff (h : P.subjoin x y = some Q) :
    ∃ n, P.nextDim y = some n ∧ ∀ m a b, Q.Imm m a b ↔ P.Imm m a b ∨ (m = n ∧ a = x ∧ b = y) := by
  obtain ⟨n, hn, rfl⟩ := subjoin_eq_some_iff.1 h
  exact ⟨n, hn, fun _ _ _ ↦ imm_addPart_iff (part_eq_none_of_nextDim hn)⟩

theorem le_of_subjoin (h : P.subjoin x y = some Q) : P ≤ Q := by
  obtain ⟨n, hn, rfl⟩ := subjoin_eq_some_iff.1 h
  exact le_addPart (part_eq_none_of_nextDim hn)

theorem Dimensional.subjoin (hP : P.Dimensional) (h : P.subjoin x y = some Q) :
    Q.Dimensional := by
  obtain ⟨n, hn, rfl⟩ := subjoin_eq_some_iff.1 h
  intro b hb
  by_cases hby : b = y
  · subst hby
    cases n
    · simp [part_addPart]
    · simpa [part_addPart] using (nextDim_eq_two_iff.1 hn).1
  · simpa [part_addPart, hby] using hP b (by simpa [part_addPart, hby] using hb)

end Parthood

end MereologicalSyntax
