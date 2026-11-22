/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Linglib.Syntax.Minimalist.Label.Head

/-!
# Selection states

A head merges with the constituents it selects. This file defines the state a constituent has for
selection, its projecting head with what that head has yet to select, and the product of two
states at a binary node, for an arbitrary account of what it is to select.

A *selection discipline* on a type `R` of residues gives `select r b u`, the residue left to a
head with residue `r` once it selects a constituent whose head is `b` and whose residue is `u`,
where it can select it. At a binary node the sister that selects the other projects. Where each
can select the other the discipline says which head outranks the other, and where neither can, or
neither outranks, the node has no head. The states form a commutative magma with zero, `0` being
the failure of Merge, whatever the discipline, so a selection state extends from lexical items to
syntactic objects as a morphism of magmas (`Minimalist.Licensing`).

## Main definitions

* `Minimalist.Selection`: a selection discipline on residues.
* `Minimalist.SelectionState`: the projecting head with its residue, a `CommMagma` and
  `MulZeroClass`.
* `Minimalist.selCombine`, `Minimalist.selSide`: the decision at a binary node, and which
  daughter projects.
* `Minimalist.SelectionState.map`: the state with its head relabelled.

## Main results

* `Minimalist.selCombine_comm`, `Minimalist.selSide_comm`: the decision does not depend on the
  order of the sisters, the formal content of Merge's unordered output.
* `Minimalist.SelectionState.mul_self`: no constituent merges with itself.
* `Head (SelectionState R)`: the head of a product is a factor's head.
* `Minimalist.SelectionState.foldl_mul_of`: along a spine the product is iterated selection.

## Implementation notes

`SelectionState R` is a one-field structure over `Option (LexicalItem.Token × R)`, so that the
product can be an instance on it: the `Option` is implementation, and `0` is the public spelling
of the failure, the off-domain value of a partial head function. There is no `One` and no
associativity claim, so the structure is `CommMagma` and `MulZeroClass` only.

## References

* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
* [adger-2003]
-/

@[expose] public section

namespace Minimalist

/-- A selection discipline on residues `R`: how what a head has yet to select changes when it
selects a constituent, and which of two heads projects when each could select the other. -/
class Selection (R : Type*) where
  /-- `select r b u` is the residue left to a head with residue `r` once it selects a constituent
  whose head is `b` and whose residue is `u`, and `none` when it cannot select it. -/
  select : R → LexicalItem.Token → R → Option R
  /-- `Outranks a b` holds when, of two sisters that can each select the other, the one headed
  by `a` projects over the one headed by `b`. -/
  Outranks : LexicalItem.Token → LexicalItem.Token → Prop := fun _ _ ↦ False
  /-- Outranking is decidable, so that the product computes. -/
  [decidableOutranks : DecidableRel Outranks]
  /-- No two heads outrank each other. -/
  outranks_asymm : ∀ ⦃a b⦄, Outranks a b → ¬ Outranks b a := by exact fun _ _ h ↦ h.elim

attribute [instance_reducible, instance] Selection.decidableOutranks

/-- A constituent's selection state is its projecting head with the residue that head has yet to
select, and `0` where Merge has failed. -/
structure SelectionState (R : Type*) where
  /-- The head and its residue, `none` for `0`. -/
  toOption : Option (LexicalItem.Token × R)
  deriving DecidableEq

namespace SelectionState

variable {R : Type*}

/-- The state with projecting head `tok` and residue `r`. -/
def of (tok : LexicalItem.Token) (r : R) : SelectionState R := ⟨some (tok, r)⟩

instance : Zero (SelectionState R) := ⟨⟨none⟩⟩

/-- Recursor for `SelectionState` using the preferred forms `0` and `of tok r`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recZeroOf {motive : SelectionState R → Sort*} (zero : motive 0)
    (of : ∀ tok r, motive (of tok r)) : ∀ x, motive x
  | ⟨none⟩ => zero
  | ⟨some (tok, r)⟩ => of tok r

/-- The projecting head, and `none` for `0`. -/
def head (x : SelectionState R) : Option LexicalItem.Token := x.toOption.map (·.1)

/-- The residue of the projecting head, and `none` for `0`. -/
def residual (x : SelectionState R) : Option R := x.toOption.map (·.2)

@[simp] theorem head_of (tok : LexicalItem.Token) (r : R) : (of tok r).head = some tok := rfl

@[simp] theorem head_zero : (0 : SelectionState R).head = none := rfl

@[simp] theorem residual_of (tok : LexicalItem.Token) (r : R) : (of tok r).residual = some r :=
  rfl

@[simp] theorem residual_zero : (0 : SelectionState R).residual = none := rfl

@[simp] theorem of_ne_zero (tok : LexicalItem.Token) (r : R) : of tok r ≠ 0 :=
  mt (congrArg toOption) (Option.some_ne_none _)

/-- The state with its head relabelled by `f`. -/
def map (f : LexicalItem.Token → LexicalItem.Token) (x : SelectionState R) : SelectionState R :=
  ⟨x.toOption.map (Prod.map f id)⟩

@[simp] theorem head_map (f : LexicalItem.Token → LexicalItem.Token) (x : SelectionState R) :
    (x.map f).head = x.head.map f := by
  simp [map, head, Option.map_map, Function.comp_def]

end SelectionState

/-! ### The product -/

section Product

variable {R : Type*} [Selection R] (x y : SelectionState R)

/-- The decision at a binary node: whether the left sister projects, the projecting head, and its
residue. The sister that selects the other projects, the outranking one where each selects the
other, and the value is `none` where no sister projects. -/
def selCombine : SelectionState R → SelectionState R → Option (Bool × LexicalItem.Token × R)
  | ⟨some (a, r)⟩, ⟨some (b, u)⟩ =>
    match Selection.select r b u, Selection.select u a r with
    | some r', none => some (true, a, r')
    | none, some u' => some (false, b, u')
    | some r', some u' =>
      if Selection.Outranks R a b then some (true, a, r')
      else if Selection.Outranks R b a then some (false, b, u') else none
    | none, none => none
  | _, _ => none

/-- The projecting daughter, `some true` for the left and `some false` for the right. -/
def selSide : Option Bool := (selCombine x y).map (·.1)

theorem selCombine_comm : selCombine x y = (selCombine y x).map fun p ↦ (!p.1, p.2) := by
  rcases x with ⟨_ | ⟨a, r⟩⟩ <;> rcases y with ⟨_ | ⟨b, u⟩⟩ <;> try rfl
  simp only [selCombine]
  rcases Selection.select r b u with _ | r' <;> rcases Selection.select u a r with _ | u' <;>
    try rfl
  by_cases h : Selection.Outranks R a b
  · simp [h, Selection.outranks_asymm h]
  · by_cases h' : Selection.Outranks R b a <;> simp [h, h']

/-- Swapping the sisters swaps the side that projects. -/
theorem selSide_comm : selSide x y = (selSide y x).map Bool.not := by
  simp only [selSide, selCombine_comm x y, Option.map_map]; rfl

/-- The product of two selection states is the head and residue of the decision at the node, and
`0` where no sister projects. -/
instance : MulZeroClass (SelectionState R) where
  mul x y := ⟨(selCombine x y).map (·.2)⟩
  zero := ⟨none⟩
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | _⟩ <;> rfl

theorem SelectionState.mul_def : x * y = ⟨(selCombine x y).map (·.2)⟩ := rfl

instance : CommMagma (SelectionState R) where
  mul_comm x y := by
    simp only [SelectionState.mul_def, selCombine_comm x y, Option.map_map]; rfl

/-- No constituent merges with itself, since no head outranks itself. -/
@[simp] theorem SelectionState.mul_self : x * x = 0 := by
  rcases x with ⟨_ | ⟨a, r⟩⟩
  · rfl
  · have h : ¬ Selection.Outranks R a a := fun h ↦ Selection.outranks_asymm h h
    rw [SelectionState.mul_def]
    simp only [selCombine]
    rcases Selection.select r a r with _ | r' <;> simp [h] <;> rfl

variable {x y}

theorem selCombine_eq_some {b : Bool} {hd : LexicalItem.Token} {res : R}
    (h : selCombine x y = some (b, hd, res)) : (bif b then x else y).head = some hd := by
  rcases x with ⟨_ | ⟨a, r⟩⟩ <;> rcases y with ⟨_ | ⟨c, u⟩⟩ <;> try cases h
  simp only [selCombine] at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · split_ifs at h <;> cases h <;> rfl
  · cases h

/-- The head of a product of selection states is one of its factors' heads. -/
instance : Head (SelectionState R) where
  head := SelectionState.head
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y r} h := by
    simp only [Option.mem_def, SelectionState.mul_def, SelectionState.head, Option.map_map,
      Option.map_eq_some_iff] at h
    obtain ⟨⟨b, _, _⟩, hproj, rfl⟩ := h
    cases b
    exacts [Or.inr (selCombine_eq_some hproj), Or.inl (selCombine_eq_some hproj)]

/-- A relabelling of heads that selection does not see commutes with the product. -/
theorem SelectionState.map_mul {f : LexicalItem.Token → LexicalItem.Token}
    (hsel : ∀ (r : R) b u, Selection.select r (f b) u = Selection.select r b u)
    (hout : ∀ a b, Selection.Outranks R (f a) (f b) ↔ Selection.Outranks R a b)
    (x y : SelectionState R) : (x * y).map f = x.map f * y.map f := by
  rcases x with ⟨_ | ⟨a, r⟩⟩ <;> rcases y with ⟨_ | ⟨b, u⟩⟩ <;> try rfl
  simp only [SelectionState.mul_def, SelectionState.map, selCombine, Option.map_some, Prod.map,
    id, hsel, hout]
  rcases Selection.select r b u with _ | r' <;> rcases Selection.select u a r with _ | u' <;>
    try rfl
  by_cases h : Selection.Outranks R a b
  · simp [h]
  · by_cases h' : Selection.Outranks R b a <;> simp [h, h']

/-! ### Spines -/

private theorem foldl_mul_zero {α : Type*} (f : α → SelectionState R) (l : List α) :
    l.foldl (fun x a ↦ x * f a) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, zero_mul, ih]

/-- Along a spine, the product is iterated selection: when no sister can select the head `h`,
merging them in turn leaves `h` projecting with the residue of selecting each, and fails where
`h` cannot select one. -/
theorem SelectionState.foldl_mul_of (h : LexicalItem.Token) (r : R)
    (args : List (LexicalItem.Token × R))
    (hargs : ∀ a ∈ args, ∀ r', Selection.select a.2 h r' = none) :
    args.foldl (fun x a ↦ x * of a.1 a.2) (of h r) =
      (args.foldlM (fun r a ↦ Selection.select r a.1 a.2) r).elim 0 (of h) := by
  induction args generalizing r with
  | nil => rfl
  | cons a args ih =>
    obtain ⟨b, u⟩ := a
    have hu := hargs (b, u) List.mem_cons_self r
    have key : of h r * of b u = (Selection.select r b u).elim 0 (of h) := by
      simp only [SelectionState.mul_def, of, selCombine, hu]
      cases Selection.select r b u <;> rfl
    rw [List.foldl_cons, List.foldlM_cons, key]
    cases Selection.select r b u with
    | none => exact foldl_mul_zero _ _
    | some r' => exact ih r' fun a ha ↦ hargs a (List.mem_cons_of_mem _ ha)

end Product

end Minimalist
