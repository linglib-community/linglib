/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Basic
public import Mathlib.Data.List.Basic

/-!
# Context towers

A context tower is an origin, Kaplan's speech-act context, with the contexts bound by the
embeddings above an expression, from outermost to innermost; an expression reads a coordinate of
the context at some depth. Kaplanian indexicals read the origin and shifted indexicals the innermost
context. The origin survives every embedding, so an indexical can read it whatever the clauses
between read: the binding account of indexical shift, against which Anand and Nevins argue that
shifting overwrites the context.

## Main definitions

* `ContextTower`: an origin with its bound contexts; `contextAt k` is the `k`-th of them,
  `innermost` the last, and `push` binds one more.
* `ContextTower.AccessPattern`: a depth, given relative to the tower, and a coordinate;
  `AccessPattern.origin` and `AccessPattern.innermost`.
* `AccessPattern.Stable`: binding another context leaves the pattern's value unchanged.

## Main results

* `push_innermost`, `push_contextAt_of_le`: a push binds the innermost context alone.
* `AccessPattern.stable_origin`, `AccessPattern.stable_innermost_iff`: a pattern reading the origin
  is stable, one reading the innermost context only if its coordinate is constant.

## References

* [kaplan-1989]
* [schlenker-2003]
* [anand-nevins-2004]
-/

@[expose] public section

universe u

/-- A context tower is an origin with the contexts bound above it, from outermost to innermost. -/
structure ContextTower (C : Type*) where
  /-- The root context, the speech-act context. -/
  origin : C
  /-- The bound contexts, the first bound by the outermost embedding. -/
  bound : List C

namespace ContextTower

variable {C : Type*} (t : ContextTower C) (c : C) {k : ℕ}

/-- The embedding depth is the number of bound contexts. -/
def depth : ℕ := t.bound.length

/-- The context at depth `k` is the `k`-th bound context, saturating at the innermost one. -/
def contextAt (k : ℕ) : C := (t.bound.take k).getLastD t.origin

/-- The innermost context is the last bound context. -/
def innermost : C := t.bound.getLastD t.origin

/-- The trivial tower over a context. -/
def root : ContextTower C := ⟨c, []⟩

/-- Embed one level deeper, binding `c`. -/
def push : ContextTower C := ⟨t.origin, t.bound ++ [c]⟩

@[simp] theorem root_origin : (root c).origin = c := rfl
@[simp] theorem root_innermost : (root c).innermost = c := rfl
@[simp] theorem root_depth : (root c).depth = 0 := rfl
@[simp] theorem root_contextAt : (root c).contextAt k = c := by simp [root, contextAt]
@[simp] theorem contextAt_zero : t.contextAt 0 = t.origin := by simp [contextAt]
@[simp] theorem push_origin : (t.push c).origin = t.origin := rfl
@[simp] theorem push_depth : (t.push c).depth = t.depth + 1 := by simp [push, depth]
@[simp] theorem push_innermost : (t.push c).innermost = c := by simp [push, innermost]

@[simp] theorem contextAt_depth : t.contextAt t.depth = t.innermost := by
  simp [contextAt, innermost, depth]

/-- Past the tower depth, `contextAt` saturates at the innermost context. -/
theorem contextAt_saturates (hk : t.depth ≤ k) : t.contextAt k = t.innermost := by
  simp [contextAt, innermost, List.take_of_length_le hk]

/-- Below the tower depth, a push leaves the context at each depth unchanged. -/
theorem push_contextAt_of_le (hk : k ≤ t.depth) : (t.push c).contextAt k = t.contextAt k := by
  simp only [contextAt, push]
  rw [List.take_append_of_le_length hk]

/-- Beyond the tower depth, a push saturates at the bound context. -/
theorem push_contextAt_of_lt (hk : t.depth < k) : (t.push c).contextAt k = c := by
  rw [contextAt_saturates _ (by rw [push_depth]; exact hk), push_innermost]

@[simp] theorem push_contextAt_succ_depth : (t.push c).contextAt (t.depth + 1) = c :=
  push_contextAt_of_lt _ _ (Nat.lt_succ_self _)

end ContextTower

namespace ContextTower

/-- An expression reads a tower at the origin, at the innermost context, or at a fixed depth. -/
inductive DepthSpec where
  | origin
  | local
  | relative (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

namespace DepthSpec

/-- The depth read at a tower of the given depth. -/
def resolve (d : DepthSpec) (towerDepth : ℕ) : ℕ :=
  match d with
  | .origin => 0
  | .local => towerDepth
  | .relative k => k

@[simp] theorem origin_resolve (n : ℕ) : DepthSpec.origin.resolve n = 0 := rfl
@[simp] theorem local_resolve (n : ℕ) : DepthSpec.local.resolve n = n := rfl
@[simp] theorem relative_resolve (k n : ℕ) : (DepthSpec.relative k).resolve n = k := rfl

end DepthSpec

/-- An access pattern, what a context-dependent expression reads, is a depth specification and a
projection. English *I* is `origin Context.agent`; Amharic *I* is
`innermost Context.agent`. -/
structure AccessPattern (C : Type*) (R : Type*) where
  /-- Which depth to read from. -/
  depth : DepthSpec
  /-- Which coordinate to extract. -/
  project : C → R

namespace AccessPattern

variable {C R : Type*} (ap : AccessPattern C R) (t : ContextTower C) (f : C → R)

/-- Resolve an access pattern against a tower. -/
def resolve : R := ap.project (t.contextAt (ap.depth.resolve t.depth))

instance : Functor (AccessPattern C) where
  map f ap := ⟨ap.depth, f ∘ ap.project⟩

instance : LawfulFunctor (AccessPattern C) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

section map

variable {R S : Type u} (ap : AccessPattern C R) (g : R → S)

@[simp] theorem map_depth : (g <$> ap).depth = ap.depth := rfl
@[simp] theorem map_project : (g <$> ap).project = g ∘ ap.project := rfl
@[simp] theorem resolve_map : (g <$> ap).resolve t = g (ap.resolve t) := rfl

end map

/-- Read the coordinate `f` of the speech-act context: a Kaplanian pure indexical. -/
def origin : AccessPattern C R := ⟨.origin, f⟩

/-- A shifted indexical reads the coordinate `f` of the innermost context. -/
def innermost : AccessPattern C R := ⟨.local, f⟩

@[simp] theorem origin_resolve : (origin f).resolve t = f t.origin := by simp [origin, resolve]

@[simp] theorem innermost_resolve : (innermost f).resolve t = f t.innermost := by
  simp [innermost, resolve]

/-- An access pattern is stable when binding another context on any tower leaves its resolution
unchanged: Kaplan's thesis for the indexicals of English, and the Fixity Thesis of Schlenker. -/
def Stable : Prop := ∀ t c, ap.resolve (t.push c) = ap.resolve t

/-- A pattern reading the speech-act context is stable. -/
theorem stable_origin : (origin f).Stable := fun t c ↦ by simp

/-- A pattern reading the innermost context is stable iff its coordinate is constant. -/
theorem stable_innermost_iff : (innermost f).Stable ↔ ∀ c c', f c = f c' :=
  ⟨fun h c c' ↦ by simpa using h (root c') c, fun h t c ↦ by simpa using h c t.innermost⟩

end AccessPattern

end ContextTower
