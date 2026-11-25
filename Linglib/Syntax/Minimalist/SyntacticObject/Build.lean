/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Tree
public import Linglib.Core.Computability.Edge
public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Building and reading syntactic objects

Merge on the carrier is written `*`: External Merge of two objects, and the re-merge of a mover
with the remainder in Internal Merge. The objects form a commutative magma and the ordered
objects a noncommutative one. Concrete objects are built ordered, as `PlanarSyntacticObject
(SyntacticObject.Leaf L ι)`s,
and forgotten to the carrier by `toSyntacticObject`, a homomorphism of magmas with none going
back. The accessors read the pronounced tokens and the token at the root.

## Main definitions

* `Minimalist.SyntacticObject.yield`, `Minimalist.PlanarSyntacticObject.yield`: the pronounced
  tokens, and the same in order.
* `Minimalist.SyntacticObject.token?`: the token of a lexical leaf.

## Main results

* `Minimalist.PlanarSyntacticObject.isEmpty_mulHom`: no homomorphism of magmas forgets in the
  other direction.
* `Minimalist.PlanarSyntacticObject.coe_yield`: a planar object pronounces the tokens of its
  object.

## References

* [marcolli-chomsky-berwick-2025], §1.13.1 (Lemma 1.13.1)
-/

@[expose] public section

namespace Minimalist

variable {L ι : Type}

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-- The default syntactic object is the bare trace. -/
instance : Inhabited (SyntacticObject (SyntacticObject.Leaf L ι)) := ⟨trace⟩

/-! ### Merge as multiplication -/

@[simp] theorem mul_def (l r : SyntacticObject (SyntacticObject.Leaf L ι)) : l * r = merge l r :=
    rfl

/-- A lexical item is a leaf. -/
instance : Coe L (SyntacticObject (SyntacticObject.Leaf L L)) := ⟨leaf⟩

/-- Merge in braces, as [marcolli-chomsky-berwick-2025] writes it: `{l, r} = merge l r`, with
    `{s} = s`. -/
instance : Insert (SyntacticObject (SyntacticObject.Leaf L ι))
    (SyntacticObject (SyntacticObject.Leaf L ι)) := ⟨merge⟩

instance : Singleton (SyntacticObject (SyntacticObject.Leaf L ι))
    (SyntacticObject (SyntacticObject.Leaf L ι)) := ⟨id⟩

@[simp] theorem insert_def (l r : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ({l, r} : SyntacticObject (SyntacticObject.Leaf L ι)) = merge l r := rfl

/-- The pronounced tokens of a syntactic object, its lexical leaves; traces are unpronounced. -/
def yield (s : SyntacticObject (SyntacticObject.Leaf L ι)) : Multiset L :=
  s.toUnorderedTree.leaves.filterMap (·.bind (Leaf.elim some fun _ ↦ none))

@[simp] theorem yield_leaf (tok : L) :
    (leaf tok : SyntacticObject (SyntacticObject.Leaf L ι)).yield = {tok} := rfl

@[simp] theorem yield_trace : (trace : SyntacticObject (SyntacticObject.Leaf L ι)).yield = 0 := rfl

@[simp] theorem yield_labelledTrace (i : ι) :
    (labelledTrace i : SyntacticObject (SyntacticObject.Leaf L ι)).yield = 0 := rfl

@[simp] theorem yield_merge (l r : SyntacticObject (SyntacticObject.Leaf L ι)) :
    (merge l r).yield = l.yield + r.yield := by
  rw [yield, toUnorderedTree_merge, show ({l.toUnorderedTree, r.toUnorderedTree} : Multiset _) =
      l.toUnorderedTree ::ₘ {r.toUnorderedTree} from rfl,
    UnorderedTree.leaves_node_cons]
  simp [yield, Multiset.filterMap_add]

end SyntacticObject

namespace PlanarSyntacticObject

@[simp] theorem mul_def (l r : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) : l * r = merge l
    r := rfl

/-- A lexical item is a leaf. -/
instance : Coe L (PlanarSyntacticObject (SyntacticObject.Leaf L L)) := ⟨leaf⟩

/-- An ordered object is an object. -/
instance {α : Type} : Coe (PlanarSyntacticObject α) (SyntacticObject α) := ⟨toSyntacticObject⟩

theorem merge_inj {l r l' r' : PlanarSyntacticObject (SyntacticObject.Leaf L ι)} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' :=
  ⟨fun h ↦ by injection h with h₁ h₂; exact ⟨h₁, h₂⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem merge_ne_left (l r : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) : merge l r ≠ l :=
    fun h ↦ by
  have := congrArg (·.toRoseTree.numNodes) h
  simp only [toRoseTree_merge, RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at this
  omega

/-- No magma homomorphism maps syntactic objects to planar ones ([marcolli-chomsky-berwick-2025]
Lemma 1.13.1). -/
theorem isEmpty_mulHom : IsEmpty
    (SyntacticObject (SyntacticObject.Leaf L ι) →ₙ* PlanarSyntacticObject
    (SyntacticObject.Leaf L ι)) := by
  refine ⟨fun φ ↦ ?_⟩
  have h := congrArg φ
      (mul_comm (default : SyntacticObject (SyntacticObject.Leaf L ι)) (default * default))
  simp only [map_mul, mul_def, merge_inj] at h
  exact merge_ne_left _ _ h.1.symm


/-- The pronounced tokens of a planar object, left to right; traces are unpronounced. -/
def yield (p : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) : List L :=
  p.toRoseTree.leafList.filterMap (·.bind (Leaf.elim some fun _ ↦ none))

theorem yield_toSyntacticObject (p : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) :
    p.toSyntacticObject.yield =
      p.toRoseTree.leaves.filterMap (·.bind (Leaf.elim some fun _ ↦ none)) := by
  rw [SyntacticObject.yield, toUnorderedTree_toSyntacticObject]
  rfl

/-- The pronounced tokens of a planar object are those of its object, in order. -/
theorem coe_yield (p : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) :
    (p.yield : Multiset L) = p.toSyntacticObject.yield := by
  rw [yield, ← Multiset.filterMap_coe, RoseTree.coe_leafList, yield_toSyntacticObject]

/-! ### Merge in braces

[marcolli-chomsky-berwick-2025] writes Merge as set formation, `{α, β}`. Lean's `{a, b}` is
`insert a {b}`, so with `{p} = p` the object `{T, {V, PossP}}` is `T * (V * PossP)`, in the given
order; its elements are objects, a head entering as its leaf. -/

instance : Singleton (PlanarSyntacticObject (SyntacticObject.Leaf L ι))
    (PlanarSyntacticObject (SyntacticObject.Leaf L ι)) := ⟨id⟩

instance : Insert (PlanarSyntacticObject (SyntacticObject.Leaf L ι))
    (PlanarSyntacticObject (SyntacticObject.Leaf L ι)) := ⟨merge⟩

@[simp] theorem singleton_def (p : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) :
    ({p} : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) = p := rfl

@[simp] theorem insert_def (l r : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) :
    (insert l r : PlanarSyntacticObject (SyntacticObject.Leaf L ι)) = merge l r := rfl

end PlanarSyntacticObject

namespace SyntacticObject

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def token? (s : SyntacticObject (SyntacticObject.Leaf L ι)) : Option L :=
  (UnorderedTree.value s.toUnorderedTree).bind (Leaf.elim some fun _ ↦ none)

@[simp] theorem token?_leaf (tok : L) :
    (SyntacticObject.leaf tok : SyntacticObject (SyntacticObject.Leaf L ι)).token? = some tok := rfl

@[simp] theorem token?_trace : (trace : SyntacticObject (SyntacticObject.Leaf L ι)).token? = none
    := rfl

@[simp] theorem token?_labelledTrace (i : ι) :
    (labelledTrace i : SyntacticObject (SyntacticObject.Leaf L ι)).token? = none := rfl

theorem traceOf_ne_trace (tok : L) : traceOf tok ≠ trace := by
  intro h
  have h' : (some (.traceOf tok) : Option (SyntacticObject.Leaf L L)) = some .trace :=
    congrArg (fun s : SyntacticObject (SyntacticObject.Leaf L L) ↦ UnorderedTree.value
        s.toUnorderedTree) h
  simp at h'

@[simp] theorem token?_merge (l r : SyntacticObject (SyntacticObject.Leaf L ι)) :
    (merge l r).token? = none := by
  rw [token?, toUnorderedTree_merge, UnorderedTree.value_node]
  rfl

theorem token?_eq_some_iff {s : SyntacticObject (SyntacticObject.Leaf L ι)} {tok : L} :
    s.token? = some tok ↔ s = leaf tok := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ token?_leaf tok⟩
  rcases s.exists_form with ⟨tok', rfl⟩ | rfl | ⟨tok', rfl⟩ | ⟨l, r, rfl⟩ <;> simp_all

theorem token?_map {L' : Type} (f : L → L') (s : SyntacticObject (SyntacticObject.Leaf L L)) :
    (s.map f).token? = s.token?.map f := by
  rcases s.exists_form with ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨l, r, rfl⟩ <;> simp

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance [Repr L] : Repr (SyntacticObject (SyntacticObject.Leaf L ι)) where
  reprPrec s _ := match s.token? with
    | some tok => f!"SyntacticObject.leaf {repr tok}"
    | none =>
      let n := UnorderedTree.numLeaves s.toUnorderedTree
      if n = 1 then f!"SyntacticObject.trace" else f!"⟨SyntacticObject merge, {n} leaves⟩"

end SyntacticObject

end Minimalist
