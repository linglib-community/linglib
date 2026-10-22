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
objects a noncommutative one. Concrete objects are built ordered, as `PlanarSyntacticObject`s,
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

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-- The default syntactic object is the bare trace. -/
instance : Inhabited SyntacticObject := ⟨trace⟩

/-! ### Merge as multiplication -/

/-- Merge on the carrier is written `l * r`, the commutative magma of the objects. -/
noncomputable instance : CommMagma SyntacticObject where
  mul := merge
  mul_comm := merge_comm

@[simp] theorem mul_def (l r : SyntacticObject) : l * r = merge l r := rfl

/-- A lexical item is a leaf. -/
instance : Coe LexicalItem.Token SyntacticObject := ⟨leaf⟩

/-- Merge in braces, as [marcolli-chomsky-berwick-2025] writes it: `{l, r} = merge l r`, with
    `{s} = s`. -/
noncomputable instance : Insert SyntacticObject SyntacticObject := ⟨merge⟩

instance : Singleton SyntacticObject SyntacticObject := ⟨id⟩

@[simp] theorem insert_def (l r : SyntacticObject) : ({l, r} : SyntacticObject) = merge l r := rfl

/-- The pronounced tokens of a syntactic object, its lexical leaves; traces are unpronounced. -/
def yield (s : SyntacticObject) : Multiset LexicalItem.Token :=
  s.val.leaves.filterMap (Sum.elim id fun _ ↦ none)

@[simp] theorem yield_leaf (tok : LexicalItem.Token) : (leaf tok).yield = {tok} := rfl

@[simp] theorem yield_trace : trace.yield = 0 := rfl

@[simp] theorem yield_traceOf (tok : LexicalItem.Token) : (traceOf tok).yield = 0 := rfl

@[simp] theorem yield_merge (l r : SyntacticObject) : (merge l r).yield = l.yield + r.yield := by
  rw [yield, merge_val, show ({l.val, r.val} : Multiset _) = l.val ::ₘ {r.val} from rfl,
    UnorderedTree.leaves_node_cons]
  simp [yield, Multiset.filterMap_add]

end SyntacticObject

namespace PlanarSyntacticObject

/-- Merge on the ordered carrier, in the given order, is written `l * r`. -/
instance : Mul PlanarSyntacticObject := ⟨merge⟩

@[simp] theorem mul_def (l r : PlanarSyntacticObject) : l * r = merge l r := rfl

/-- A lexical item is a leaf. -/
instance : Coe LexicalItem.Token PlanarSyntacticObject := ⟨leaf⟩

/-- An ordered object is an object. -/
instance : Coe PlanarSyntacticObject SyntacticObject := ⟨toSyntacticObject⟩

/-- Forgetting the order is a homomorphism of magmas ([marcolli-chomsky-berwick-2025]
    Lemma 1.13.1). -/
def toSyntacticObjectHom : PlanarSyntacticObject →ₙ* SyntacticObject :=
  ⟨toSyntacticObject, toSyntacticObject_merge⟩

@[simp] theorem toSyntacticObjectHom_apply (p : PlanarSyntacticObject) :
    toSyntacticObjectHom p = p.toSyntacticObject := rfl

theorem merge_inj {l r l' r' : PlanarSyntacticObject} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' := by
  refine ⟨fun h ↦ ?_, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩
  obtain ⟨hl, hr⟩ : l.val = l'.val ∧ r.val = r'.val := by simpa using congrArg Subtype.val h
  exact ⟨Subtype.ext hl, Subtype.ext hr⟩

theorem merge_ne_left (l r : PlanarSyntacticObject) : merge l r ≠ l := fun h ↦ by
  have := congrArg (·.val.numNodes) h
  simp only [merge_val, RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at this
  omega

/-- No homomorphism of magmas forgets in the other direction, since the ordered objects have no
    commutative submagma: the images of `t * (t * t)` and `(t * t) * t` would coincide
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.1). -/
theorem isEmpty_mulHom : IsEmpty (SyntacticObject →ₙ* PlanarSyntacticObject) := by
  refine ⟨fun φ ↦ ?_⟩
  have h := congrArg φ (mul_comm (default : SyntacticObject) (default * default))
  simp only [map_mul, mul_def, merge_inj] at h
  exact merge_ne_left _ _ h.1.symm

/-- `p.attach e d` merges `d` into `p` as the daughter on edge `e`. -/
def attach (p : PlanarSyntacticObject) (e : Edge) (d : PlanarSyntacticObject) :
    PlanarSyntacticObject :=
  match e with
  | .left => merge d p
  | .right => merge p d

@[simp] theorem attach_left (p d : PlanarSyntacticObject) : p.attach .left d = merge d p := rfl

@[simp] theorem attach_right (p d : PlanarSyntacticObject) : p.attach .right d = merge p d := rfl

theorem attach_swap (p d : PlanarSyntacticObject) (e : Edge) :
    p.attach e.swap d = d.attach e p := by
  cases e <;> rfl

/-- Merge on either edge forgets to Merge. -/
@[simp] theorem toSyntacticObject_attach (p d : PlanarSyntacticObject) (e : Edge) :
    (p.attach e d).toSyntacticObject = SyntacticObject.merge d.toSyntacticObject p.toSyntacticObject
    := by
  cases e
  · exact toSyntacticObject_merge d p
  · exact (toSyntacticObject_merge p d).trans (SyntacticObject.merge_comm _ _)

/-- The pronounced tokens of a planar object, left to right; traces are unpronounced. -/
def yield (p : PlanarSyntacticObject) : List LexicalItem.Token :=
  p.val.leafList.filterMap (Sum.elim id fun _ ↦ none)

theorem yield_toSyntacticObject (p : PlanarSyntacticObject) :
    p.toSyntacticObject.yield = p.val.leaves.filterMap (Sum.elim id fun _ ↦ none) := rfl

/-- The pronounced tokens of a planar object are those of its object, in order. -/
theorem coe_yield (p : PlanarSyntacticObject) :
    (p.yield : Multiset LexicalItem.Token) = p.toSyntacticObject.yield := by
  rw [yield, ← Multiset.filterMap_coe, RoseTree.coe_leafList]
  rfl

theorem yield_attach (p : PlanarSyntacticObject) (e : Edge) (d : PlanarSyntacticObject) :
    (p.attach e d).toSyntacticObject.yield =
      d.toSyntacticObject.yield + p.toSyntacticObject.yield := by
  cases e <;>
    simp only [yield_toSyntacticObject, attach, merge_val, RoseTree.leaves_node_cons,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Multiset.filterMap_add]
  exact add_comm _ _

/-! ### Merge in braces

[marcolli-chomsky-berwick-2025] writes Merge as set formation, `{α, β}`. Lean's `{a, b}` is
`insert a {b}`, so with `{p} = p` the object `{T, {V, PossP}}` is `T * (V * PossP)`, in the given
order; its elements are objects, a head entering as its leaf. -/

instance : Singleton PlanarSyntacticObject PlanarSyntacticObject := ⟨id⟩

instance : Insert PlanarSyntacticObject PlanarSyntacticObject := ⟨merge⟩

@[simp] theorem singleton_def (p : PlanarSyntacticObject) : ({p} : PlanarSyntacticObject) = p := rfl

@[simp] theorem insert_def (l r : PlanarSyntacticObject) :
    ({l, r} : PlanarSyntacticObject) = merge l r := rfl

end PlanarSyntacticObject

namespace SyntacticObject

/-! ### Lexical leaves from features -/

/-- A lexical leaf from a category and selectional stack. -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.of cat sel, id⟩

/-- A lexical leaf with a phonological form. -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.of cat sel (phonForm := phon), id⟩

/-! ### Accessors -/

/-- The lexical token at the root, if the root is a lexical leaf. -/
def token? (s : SyntacticObject) : Option LexicalItem.Token :=
  match UnorderedTree.value s.val with
  | .inl o => o
  | .inr _ => none

@[simp] theorem token?_leaf (tok : LexicalItem.Token) : (SyntacticObject.leaf tok).token?
    = some tok := rfl

@[simp] theorem token?_trace : trace.token? = none := rfl

@[simp] theorem token?_traceOf (tok : LexicalItem.Token) : (traceOf tok).token? = none := rfl

/-- `s` is a lexical leaf whose item's category is `c`. -/
def isLeafOf (c : Cat) (s : SyntacticObject) : Prop :=
  s.token?.map (·.item.cat) = some c

instance (c : Cat) : DecidablePred (isLeafOf c) := fun _ ↦ inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeafOf_leaf (c : Cat) (tok : LexicalItem.Token) :
    isLeafOf c (SyntacticObject.leaf tok) ↔ tok.item.cat = c := by
  simp [isLeafOf]

@[simp] theorem not_isLeafOf_trace (c : Cat) : ¬ isLeafOf c trace := by simp [isLeafOf]

theorem traceOf_ne_trace (tok : LexicalItem.Token) : traceOf tok ≠ trace := by
  intro h
  have h' : (Sum.inr (some tok) : Vertex) = Sum.inr none :=
    congrArg (fun s : SyntacticObject ↦ UnorderedTree.value s.val) h
  simp at h'

@[simp] theorem token?_merge (l r : SyntacticObject) : (merge l r).token? = none := by
  rw [token?, merge_val, UnorderedTree.value_node]

/-- A trace leaf, bare or indexed. -/
def isTrace (s : SyntacticObject) : Prop :=
  (UnorderedTree.value s.val).isRight = true ∧ UnorderedTree.numNodes s.val = 1

instance (s : SyntacticObject) : Decidable (isTrace s) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem isTrace_traceOf (tok : LexicalItem.Token) : isTrace (traceOf tok) := ⟨rfl, rfl⟩

@[simp] theorem not_isTrace_leaf (tok : LexicalItem.Token) :
    ¬ isTrace (SyntacticObject.leaf tok) := fun h ↦
  Bool.false_ne_true h.1

@[simp] theorem isTrace_trace : isTrace trace := ⟨rfl, rfl⟩

/-- The number of leaves, traces included. -/
def leafCount (s : SyntacticObject) : Nat := UnorderedTree.numLeaves s.val

/-- An object is a lexical or trace leaf exactly when its leaf count is one. -/
def IsLeaf (s : SyntacticObject) : Prop := s.leafCount = 1

instance : DecidablePred IsLeaf := fun _ ↦ inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeaf_leaf (tok : LexicalItem.Token) : IsLeaf (SyntacticObject.leaf tok) := rfl
@[simp] theorem isLeaf_trace : IsLeaf trace := rfl

/-- A shape summary; the full tree is a quotient with no faithful readout. -/
instance : Repr SyntacticObject where
  reprPrec s _ := match s.token? with
    | some tok => f!"SyntacticObject.leaf {repr tok}"
    | none =>
      if s.IsLeaf then f!"SyntacticObject.trace"
      else f!"⟨SyntacticObject merge, {s.leafCount} leaves⟩"

/-- `nodeCount s = leafCount s - 1`, the number of internal vertices of a full binary tree. -/
def nodeCount (s : SyntacticObject) : Nat := UnorderedTree.numLeaves s.val - 1

@[simp] theorem leafCount_leaf (tok : LexicalItem.Token) :
    (SyntacticObject.leaf tok).leafCount = 1 := rfl
@[simp] theorem leafCount_trace : trace.leafCount = 1 := rfl

end SyntacticObject

/-! ### Carrier tests -/

private def demoTok (i : ℕ) : LexicalItem.Token := ⟨.of .N [], i⟩

private def demoVP : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf (demoTok 0))
    (PlanarSyntacticObject.leaf (demoTok 1))).toSyntacticObject

/-- The DSL-built tree is a genuine syntactic object. -/
example : IsSyntacticObject demoVP.val := by decide
/-- Its head token reads back via `token?` of the left leaf. -/
example : (SyntacticObject.leaf (demoTok 0)).token? = some (demoTok 0) := by decide
/-- It has two leaves and one internal node. -/
example : demoVP.leafCount = 2 ∧ demoVP.nodeCount = 1 := by decide
/-- The trace leaf is recognized; a lexical leaf is not a trace. -/
example : isTrace SyntacticObject.trace ∧ ¬ isTrace (SyntacticObject.leaf
    (demoTok 0)) := by decide
/-- A bare binary node over a lexical leaf and a bare trace, the shape of an Internal-Merge
    result, is a syntactic object. -/
example :
    IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare
      [.leaf (Vertex.lex (demoTok 0)), .leaf Vertex.trace])) := by decide
/-- A lexical item with children is rejected: lexical items are leaves. -/
example :
    ¬ IsSyntacticObject (UnorderedTree.mk (.node (Vertex.lex (demoTok 0)) [.leaf
      Vertex.trace])) := by decide
/-- A ternary bare node is rejected: syntactic objects are binary. -/
example :
    ¬ IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare
      [.leaf Vertex.trace, .leaf Vertex.trace, .leaf Vertex.trace])) := by decide

end Minimalist
