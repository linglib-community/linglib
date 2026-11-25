/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# Minimal search on a syntactic object

Minimal search from a syntactic object finds the closest heads it contains. On an object in which
what has moved out has left a trace, the search is a morphism of magmas: a lexical item is found
as a head, a trace offers nothing, a head merged with anything else is found alone, two heads
merged are both found, and two phrases merged offer the heads of both. `SearchState` is the
commutative magma of these outcomes, `SyntacticObject.search` the morphism, and
`SyntacticObject.searchHeads` the heads found.

The search depends on the object alone, so a condition on the label of what moves is a condition
on the mover, with no reference to the stage it moves at. `PlanarSyntacticObject.labels` computes
the same search on the positions of a planar object, where lower copies are present and invisible.

## TODO

* `t.labels x = x.searchHeads` for a term `x` of the object `t` a derivation with traces derives.

## References

* [chomsky-2013]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

/-- What minimal search finds in an object: a head, nothing in a trace, or the heads of a
phrase. -/
inductive SearchState
  | head (a : LexicalItem.Token)
  | trace
  | phrase (S : Finset LexicalItem.Token)
  deriving DecidableEq

namespace SearchState

/-- The heads found. -/
def heads : SearchState → Finset LexicalItem.Token
  | head a => {a}
  | trace => ∅
  | phrase S => S

instance : Mul SearchState where
  mul
    | head a, head b => phrase {a, b}
    | head a, _ => phrase {a}
    | _, head a => phrase {a}
    | x, y => phrase (x.heads ∪ y.heads)

instance : CommMagma SearchState where
  mul_comm x y := by
    cases x <;> cases y <;> simp [HMul.hMul, Mul.mul, Finset.pair_comm, Finset.union_comm]

@[simp] theorem head_mul_head (a b : LexicalItem.Token) : head a * head b = phrase {a, b} := rfl

@[simp] theorem head_mul_trace (a : LexicalItem.Token) : head a * trace = phrase {a} := rfl

@[simp] theorem head_mul_phrase (a : LexicalItem.Token) (S : Finset LexicalItem.Token) :
    head a * phrase S = phrase {a} := rfl

@[simp] theorem trace_mul_trace : trace * trace = phrase ∅ :=
  congrArg phrase (Finset.empty_union ∅)

@[simp] theorem trace_mul_phrase (S : Finset LexicalItem.Token) : trace * phrase S = phrase S :=
  congrArg phrase (Finset.empty_union S)

@[simp] theorem phrase_mul_phrase (S S' : Finset LexicalItem.Token) :
    phrase S * phrase S' = phrase (S ∪ S') := rfl

end SearchState

namespace SyntacticObject

/-- Minimal search as a morphism of magmas: Merge multiplies what search finds in the daughters. -/
def search : SyntacticObject TokenLeaf →ₙ* SearchState :=
  FreeCommMagma.lift (Leaf.elim SearchState.head fun _ ↦ SearchState.trace)

/-- The heads minimal search finds in a syntactic object. -/
def searchHeads (s : SyntacticObject TokenLeaf) : Finset LexicalItem.Token := (search s).heads

@[simp] theorem search_leaf (tok : LexicalItem.Token) : search (leaf tok) = .head tok := rfl

@[simp] theorem search_traceOf (tok : LexicalItem.Token) : search (traceOf tok) = .trace := rfl

@[simp] theorem search_merge (l r : SyntacticObject TokenLeaf) :
    search (merge l r) = search l * search r :=
  map_mul search l r

end SyntacticObject

end Minimalist
