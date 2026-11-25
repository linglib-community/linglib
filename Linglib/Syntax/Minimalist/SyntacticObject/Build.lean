/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Tree
public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Building and reading syntactic objects

Merge on the carrier is written `*`: External Merge of two objects, and the Merge of a term of an
object with that object in Internal Merge. The objects form a commutative magma and the ordered
objects a noncommutative one. Concrete objects are built ordered, as `PlanarSyntacticObject α`s,
and forgotten to the carrier by `toSyntacticObject`, a homomorphism of magmas with none going
back. The accessors read the items in order and the item of a leaf.

## Main definitions

* `Minimalist.PlanarSyntacticObject.yield`: the items of a planar object, in order.
* `Minimalist.SyntacticObject.token?`: the item of a leaf.

## Main results

* `Minimalist.PlanarSyntacticObject.isEmpty_mulHom`: no homomorphism of magmas forgets in the
  other direction.

## References

* [marcolli-chomsky-berwick-2025], §1.13.1 (Lemma 1.13.1)
-/

@[expose] public section

namespace Minimalist

variable {α β : Type}

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-- An item is a leaf. -/
instance : Coe α (SyntacticObject α) := ⟨leaf⟩

/-- Merge in braces, as [marcolli-chomsky-berwick-2025] writes it: `{l, r} = l * r`, with
    `{s} = s`. -/
instance : Insert (SyntacticObject α) (SyntacticObject α) := ⟨merge⟩

instance : Singleton (SyntacticObject α) (SyntacticObject α) := ⟨id⟩

@[simp] theorem insert_def (l r : SyntacticObject α) : ({l, r} : SyntacticObject α) = l * r := rfl

end SyntacticObject

namespace PlanarSyntacticObject

/-- An item is a leaf. -/
instance : Coe α (PlanarSyntacticObject α) := ⟨leaf⟩

instance : Coe (PlanarSyntacticObject α) (SyntacticObject α) := ⟨toSyntacticObject⟩

theorem mul_inj {l r l' r' : PlanarSyntacticObject α} : l * r = l' * r' ↔ l = l' ∧ r = r' :=
  ⟨fun h ↦ by injection h with h₁ h₂; exact ⟨h₁, h₂⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem mul_ne_left (l r : PlanarSyntacticObject α) : l * r ≠ l := fun h ↦ by
  have := congrArg (·.toRoseTree.numNodes) h
  simp only [toRoseTree_mul, RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at this
  omega

/-- No magma homomorphism maps syntactic objects to planar ones ([marcolli-chomsky-berwick-2025]
Lemma 1.13.1). -/
theorem isEmpty_mulHom [Nonempty α] : IsEmpty (SyntacticObject α →ₙ* PlanarSyntacticObject α) := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨fun φ ↦ ?_⟩
  have h := congrArg φ (mul_comm (leaf a : SyntacticObject α) (leaf a * leaf a))
  simp only [map_mul, mul_inj] at h
  exact mul_ne_left _ _ h.1.symm

/-- The items of a planar object, left to right. -/
def yield (p : PlanarSyntacticObject α) : List α := p.toRoseTree.leafList.filterMap id

@[simp] theorem yield_of (a : α) : yield (FreeMagma.of a : PlanarSyntacticObject α) = [a] := rfl

/-! ### Merge in braces

[marcolli-chomsky-berwick-2025] writes Merge as set formation, `{α, β}`. Lean's `{a, b}` is
`insert a {b}`, so with `{p} = p` the object `{T, {V, PossP}}` is `T * (V * PossP)`, in the given
order; its elements are objects, a head entering as its leaf. -/

instance : Singleton (PlanarSyntacticObject α) (PlanarSyntacticObject α) := ⟨id⟩

instance : Insert (PlanarSyntacticObject α) (PlanarSyntacticObject α) := ⟨merge⟩

@[simp] theorem singleton_def (p : PlanarSyntacticObject α) :
    ({p} : PlanarSyntacticObject α) = p := rfl

@[simp] theorem insert_def (l r : PlanarSyntacticObject α) :
    (insert l r : PlanarSyntacticObject α) = l * r := rfl

end PlanarSyntacticObject

namespace SyntacticObject

/-! ### Accessors -/

/-- The item of a leaf, `none` of a Merge. -/
def token? : SyntacticObject α → Option α :=
  FreeCommMagma.elim some (fun _ _ _ _ ↦ none) fun _ _ _ _ ↦ rfl

@[simp] theorem token?_of (a : α) : token? (FreeCommMagma.of a) = some a := rfl

@[simp] theorem token?_mul (l r : SyntacticObject α) : (l * r).token? = none :=
  FreeCommMagma.elim_mul ..

theorem token?_eq_some_iff {s : SyntacticObject α} {a : α} :
    s.token? = some a ↔ s = FreeCommMagma.of a := by
  induction s using FreeCommMagma.inductionOn with
  | of b => simp [FreeCommMagma.of_injective.eq_iff]
  | mul l r _ _ => simp [(FreeCommMagma.of_ne_mul a l r).symm]

theorem token?_map (f : α → β) (s : SyntacticObject α) : (s.map f).token? = s.token?.map f := by
  induction s using FreeCommMagma.inductionOn with
  | of a => rfl
  | mul l r _ _ => simp

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance [Repr α] : Repr (SyntacticObject α) where
  reprPrec s _ := match s.token? with
    | some a => f!"SyntacticObject.leaf {repr a}"
    | none => f!"⟨SyntacticObject merge, {UnorderedTree.numLeaves s.toUnorderedTree} leaves⟩"

end SyntacticObject

end Minimalist
