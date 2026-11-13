/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Basic
public import Linglib.Core.Computability.Edge
public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Building and reading syntactic objects

Merge on the carrier is written `*`: External Merge of two objects, and the re-merge of a mover
with the remainder in Internal Merge. The objects form a commutative magma and the ordered
objects a noncommutative one. Concrete objects are built ordered, as `PlanarSyntacticObject L`s,
and forgotten to the carrier by `toSyntacticObject`, a homomorphism of magmas with none going
back. The accessors read the root token, the leaf and node counts, and the trace predicate,
which recognizes the trace leaves, bare or indexed.

## Main definitions

* `Minimalist.PlanarSyntacticObject.toSyntacticObjectHom`: forgetting the order.
* `Minimalist.SyntacticObject.yield`: the pronounced tokens.
* `Minimalist.PlanarSyntacticObject.attach`, `yield`: Merge on a given edge, and the pronounced
  tokens in order.
* `Minimalist.SyntacticObject.mkLeaf`, `mkLeafPhon`: lexical leaves from features.
* `Minimalist.SyntacticObject.token?`, `isTrace`, `leafCount`, `nodeCount`, `IsLeaf`.

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

variable {L : Type}

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-- The default syntactic object is the bare trace. -/
instance : Inhabited (SyntacticObject L) := ⟨trace⟩

/-! ### Merge as multiplication -/

@[simp] theorem mul_def (l r : SyntacticObject L) : l * r = merge l r := rfl

/-- A lexical item is a leaf. -/
instance : Coe L (SyntacticObject L) := ⟨leaf⟩

/-- Merge in braces, as [marcolli-chomsky-berwick-2025] writes it: `{l, r} = merge l r`, with
    `{s} = s`. -/
instance : Insert (SyntacticObject L) (SyntacticObject L) := ⟨merge⟩

instance : Singleton (SyntacticObject L) (SyntacticObject L) := ⟨id⟩

@[simp] theorem insert_def (l r : SyntacticObject L) :
    ({l, r} : SyntacticObject L) = merge l r := rfl

/-- The pronounced tokens of a syntactic object, its lexical leaves; traces are unpronounced. -/
def yield (s : SyntacticObject L) : Multiset L :=
  s.toUnorderedTree.leaves.filterMap (Sum.elim id fun _ ↦ none)

@[simp] theorem yield_leaf (tok : L) : (leaf tok).yield = {tok} := rfl

@[simp] theorem yield_trace : (trace : SyntacticObject L).yield = 0 := rfl

@[simp] theorem yield_traceOf (tok : L) : (traceOf tok).yield = 0 := rfl

@[simp] theorem yield_merge (l r : SyntacticObject L) : (merge l r).yield = l.yield + r.yield := by
  rw [yield, toUnorderedTree_merge, show ({l.toUnorderedTree, r.toUnorderedTree} : Multiset _) =
      l.toUnorderedTree ::ₘ {r.toUnorderedTree} from rfl,
    UnorderedTree.leaves_node_cons]
  simp [yield, Multiset.filterMap_add]

end SyntacticObject

namespace PlanarSyntacticObject

@[simp] theorem mul_def (l r : PlanarSyntacticObject L) : l * r = merge l r := rfl

/-- A lexical item is a leaf. -/
instance : Coe L (PlanarSyntacticObject L) := ⟨leaf⟩

/-- An ordered object is an object. -/
instance : Coe (PlanarSyntacticObject L) (SyntacticObject L) := ⟨toSyntacticObject⟩

theorem merge_inj {l r l' r' : PlanarSyntacticObject L} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' :=
  ⟨fun h ↦ by injection h with h₁ h₂; exact ⟨h₁, h₂⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem merge_ne_left (l r : PlanarSyntacticObject L) : merge l r ≠ l := fun h ↦ by
  have := congrArg (·.toRoseTree.numNodes) h
  simp only [toRoseTree_merge, RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at this
  omega

/-- No magma homomorphism maps syntactic objects to planar ones ([marcolli-chomsky-berwick-2025]
Lemma 1.13.1). -/
theorem isEmpty_mulHom : IsEmpty (SyntacticObject L →ₙ* PlanarSyntacticObject L) := by
  refine ⟨fun φ ↦ ?_⟩
  have h := congrArg φ (mul_comm (default : SyntacticObject L) (default * default))
  simp only [map_mul, mul_def, merge_inj] at h
  exact merge_ne_left _ _ h.1.symm

/-- `p.attach e d` merges `d` into `p` as the daughter on edge `e`. -/
def attach (p : PlanarSyntacticObject L) (e : Edge) (d : PlanarSyntacticObject L) :
    PlanarSyntacticObject L :=
  match e with
  | .left => merge d p
  | .right => merge p d

@[simp] theorem attach_left (p d : PlanarSyntacticObject L) :
    p.attach .left d = merge d p := rfl

@[simp] theorem attach_right (p d : PlanarSyntacticObject L) : p.attach .right d = merge p d :=
  rfl

theorem attach_swap (p d : PlanarSyntacticObject L) (e : Edge) :
    p.attach e.swap d = d.attach e p := by
  cases e <;> rfl

@[simp] theorem toSyntacticObject_attach (p d : PlanarSyntacticObject L) (e : Edge) :
    (p.attach e d).toSyntacticObject = SyntacticObject.merge d.toSyntacticObject p.toSyntacticObject
    := by
  cases e
  · exact toSyntacticObject_merge d p
  · exact (toSyntacticObject_merge p d).trans (SyntacticObject.merge_comm _ _)

@[simp] theorem attach_map {L' : Type} (f : L → L') (p d : PlanarSyntacticObject L) (e : Edge) :
    (p.attach e d).map f = (p.map f).attach e (d.map f) := by
  cases e <;> simp

/-- The pronounced tokens of a planar object, left to right; traces are unpronounced. -/
def yield (p : PlanarSyntacticObject L) : List L :=
  p.toRoseTree.leafList.filterMap (Sum.elim id fun _ ↦ none)

theorem yield_toSyntacticObject (p : PlanarSyntacticObject L) :
    p.toSyntacticObject.yield = p.toRoseTree.leaves.filterMap (Sum.elim id fun _ ↦ none) := rfl

/-- The pronounced tokens of a planar object are those of its object, in order. -/
theorem coe_yield (p : PlanarSyntacticObject L) :
    (p.yield : Multiset L) = p.toSyntacticObject.yield := by
  rw [yield, ← Multiset.filterMap_coe, RoseTree.coe_leafList]
  rfl

theorem yield_attach (p : PlanarSyntacticObject L) (e : Edge)
    (d : PlanarSyntacticObject L) :
    (p.attach e d).toSyntacticObject.yield =
      d.toSyntacticObject.yield + p.toSyntacticObject.yield := by
  cases e <;>
    simp only [yield_toSyntacticObject, attach, toRoseTree_merge, RoseTree.leaves_node_cons,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Multiset.filterMap_add]
  exact add_comm _ _

/-! ### Merge in braces

[marcolli-chomsky-berwick-2025] writes Merge as set formation, `{α, β}`. Lean's `{a, b}` is
`insert a {b}`, so with `{p} = p` the object `{T, {V, PossP}}` is `T * (V * PossP)`, in the given
order; its elements are objects, a head entering as its leaf. -/

instance : Singleton (PlanarSyntacticObject L) (PlanarSyntacticObject L) := ⟨id⟩

instance : Insert (PlanarSyntacticObject L) (PlanarSyntacticObject L) := ⟨merge⟩

@[simp] theorem singleton_def (p : PlanarSyntacticObject L) :
    ({p} : PlanarSyntacticObject L) = p := rfl

@[simp] theorem insert_def (l r : PlanarSyntacticObject L) :
    (insert l r : PlanarSyntacticObject L) = merge l r := rfl

end PlanarSyntacticObject

namespace SyntacticObject

/-! ### Lexical leaves from features -/

/-- A lexical leaf with a phonological form. -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.of cat sel (phonForm := phon), id⟩

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def token? (s : SyntacticObject L) : Option L :=
  match UnorderedTree.value s.toUnorderedTree with
  | .inl o => o
  | .inr _ => none

@[simp] theorem token?_leaf (tok : L) : (SyntacticObject.leaf tok).token?
    = some tok := rfl

@[simp] theorem token?_trace : (trace : SyntacticObject L).token? = none := rfl

@[simp] theorem token?_traceOf (tok : L) : (traceOf tok).token? = none := rfl

/-- `s` is a lexical leaf whose item's category is `c`. -/
def isLeafOf (c : Cat) (s : SyntacticObject) : Prop :=
  s.token?.map (·.item.cat) = some c

instance (c : Cat) : DecidablePred (isLeafOf c) := fun _ ↦ inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeafOf_leaf (c : Cat) (tok : LexicalItem.Token) :
    isLeafOf c (SyntacticObject.leaf tok) ↔ tok.item.cat = c := by
  simp [isLeafOf]

@[simp] theorem not_isLeafOf_trace (c : Cat) : ¬ isLeafOf c trace := by simp [isLeafOf]

theorem traceOf_ne_trace (tok : L) : traceOf tok ≠ trace := by
  intro h
  have h' : (Sum.inr (some tok) : Vertex L) = Sum.inr none :=
    congrArg (fun s : SyntacticObject L ↦ UnorderedTree.value s.toUnorderedTree) h
  simp at h'

@[simp] theorem token?_merge (l r : SyntacticObject L) : (merge l r).token? = none := by
  rw [token?, toUnorderedTree_merge, UnorderedTree.value_node]

theorem token?_eq_some_iff {s : SyntacticObject L} {tok : L} :
    s.token? = some tok ↔ s = leaf tok := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ token?_leaf tok⟩
  rcases s.exists_form with ⟨tok', rfl⟩ | rfl | ⟨tok', rfl⟩ | ⟨l, r, rfl⟩ <;> simp_all

theorem token?_map {L' : Type} (f : L → L') (s : SyntacticObject L) :
    (s.map f).token? = s.token?.map f := by
  rcases s.exists_form with ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨l, r, rfl⟩ <;> simp

theorem isLeafOf_map {f : LexicalItem.Token → LexicalItem.Token}
    (hcat : ∀ t, (f t).item.cat = t.item.cat) (c : Cat) (s : SyntacticObject) :
    isLeafOf c (s.map f) ↔ isLeafOf c s := by
  simp [isLeafOf, token?_map, Option.map_map, Function.comp_def, hcat]

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance [Repr L] : Repr (SyntacticObject L) where
  reprPrec s _ := match s.token? with
    | some tok => f!"SyntacticObject.leaf {repr tok}"
    | none =>
      let n := UnorderedTree.numLeaves s.toUnorderedTree
      if n = 1 then f!"SyntacticObject.trace" else f!"⟨SyntacticObject merge, {n} leaves⟩"

end SyntacticObject

end Minimalist
