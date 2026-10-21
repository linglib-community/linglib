/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Semantics.Reference.Rigidity
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Context towers

A context tower is an origin, Kaplan's speech-act context, with a stack of shifts from outermost to
innermost, each an element of the monoid `Function.End C`; an expression reads a coordinate of the
context at some depth. Kaplanian indexicals read the origin and shifted indexicals the innermost
context. The origin survives every shift, so an indexical can read it whatever the clauses between
read: the binding account of indexical shift, against which Anand and Nevins argue that shifting
overwrites the context.

## Main definitions

* `ContextTower`: an origin with its shifts; `contextAt k` is the first `k` shifts acting on the
  origin, `innermost` all of them, and `push` embeds one level deeper.
* `ContextTower.AccessPattern`: a depth, given relative to the tower, and a coordinate;
  `AccessPattern.origin` and `AccessPattern.innermost`.
* `AccessPattern.Stable`: pushing a shift leaves the pattern's value unchanged.

## Main results

* `push_innermost`, `push_contextAt_of_le`: a push acts on the innermost context alone.
* `AccessPattern.stable_origin`: a pattern reading the origin is stable under every shift.

## References

* [kaplan-1989]
* [schlenker-2003]
* [anand-nevins-2004]
-/

@[expose] public section

/-- A context tower is an origin with a stack of shifts, from outermost to innermost. -/
structure ContextTower (C : Type*) where
  /-- The root context, the speech-act context. -/
  origin : C
  /-- The shifts, the first being the outermost embedding. -/
  shifts : List (Function.End C)

namespace ContextTower

variable {C : Type*} (t : ContextTower C) (σ : Function.End C) (c : C) {k : ℕ}

/-- The embedding depth is the number of shifts. -/
def depth : ℕ := t.shifts.length

/-- The context at depth `k` is the first `k` shifts acting on the origin, saturating at the
innermost context. -/
def contextAt (k : ℕ) : C := (t.shifts.take k).reverse.prod • t.origin

/-- The innermost context is every shift acting on the origin. -/
def innermost : C := t.shifts.reverse.prod • t.origin

/-- The trivial tower over a context. -/
def root (c : C) : ContextTower C := ⟨c, []⟩

/-- Embed one level deeper. -/
def push : ContextTower C := ⟨t.origin, t.shifts ++ [σ]⟩

@[simp] theorem root_origin : (root c).origin = c := rfl
@[simp] theorem root_innermost : (root c).innermost = c := one_smul _ _
@[simp] theorem root_depth : (root c).depth = 0 := rfl
@[simp] theorem root_contextAt : (root c).contextAt k = c := by simp [root, contextAt]
@[simp] theorem contextAt_zero : t.contextAt 0 = t.origin := one_smul _ _
@[simp] theorem push_origin : (t.push σ).origin = t.origin := rfl
@[simp] theorem push_depth : (t.push σ).depth = t.depth + 1 := by simp [push, depth]

@[simp] theorem contextAt_depth : t.contextAt t.depth = t.innermost := by
  simp [contextAt, innermost, depth]

/-- Past the tower depth, `contextAt` saturates at the innermost context. -/
theorem contextAt_saturates (hk : t.depth ≤ k) : t.contextAt k = t.innermost := by
  simp [contextAt, innermost, List.take_of_length_le hk]

/-- Pushing a shift lets it act on the innermost context. -/
@[simp] theorem push_innermost : (t.push σ).innermost = σ • t.innermost := by
  simp [push, innermost, mul_smul]

/-- Below the tower depth, a push leaves the context at each depth unchanged. -/
theorem push_contextAt_of_le (hk : k ≤ t.depth) : (t.push σ).contextAt k = t.contextAt k := by
  simp only [contextAt, push]
  rw [List.take_append_of_le_length hk]

/-- Beyond the tower depth, a push saturates at the shifted innermost context. -/
theorem push_contextAt_of_lt (hk : t.depth < k) : (t.push σ).contextAt k = σ • t.innermost := by
  rw [← push_innermost, contextAt_saturates _ (by rw [push_depth]; exact hk)]

@[simp] theorem push_contextAt_succ_depth : (t.push σ).contextAt (t.depth + 1) = σ • t.innermost :=
  push_contextAt_of_lt _ _ (Nat.lt_succ_self _)

theorem prod_reverse_map_const_smul (l : List C) (c : C) :
    ((l.map (Function.const C) : List (Function.End C))).reverse.prod • c = l.getLastD c := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, mul_smul,
      ih, List.getLastD_cons]
    rfl

/-- A tower of reports, each shift taking every context to a reported one, has at depth `k` the
last of the first `k` reported contexts. -/
theorem contextAt_map_const (c : C) (js : List C) (k : ℕ) :
    (⟨c, js.map (Function.const C)⟩ : ContextTower C).contextAt k = (js.take k).getLastD c := by
  rw [contextAt, ← List.map_take, prod_reverse_map_const_smul]

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

universe u

variable {C R : Type*} (ap : AccessPattern C R) (t : ContextTower C) (f : C → R)
  (σ : Function.End C)

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

/-- An access pattern is stable under a shift when pushing the shift onto any tower leaves its
resolution unchanged. Kaplan-compliance is stability under every shift and monsterhood
instability of some pattern (`Reference/Kaplan.lean`). -/
def Stable : Prop := ∀ t, ap.resolve (t.push σ) = ap.resolve t

/-- Origin access is invariant under push, which is Kaplan's thesis for expressions reading the
speech-act context. -/
theorem origin_stable (ap : AccessPattern C R) (hd : ap.depth = .origin) (t : ContextTower C)
    (σ : Function.End C) : ap.resolve (t.push σ) = ap.resolve t := by
  simp only [resolve, hd, DepthSpec.origin_resolve, ContextTower.contextAt_zero,
    ContextTower.push_origin]

theorem stable_of_depth_origin (ap : AccessPattern C R) (hd : ap.depth = .origin)
    (σ : Function.End C) : ap.Stable σ :=
  fun t ↦ ap.origin_stable hd t σ

theorem stable_origin : (origin f).Stable σ := stable_of_depth_origin _ rfl σ

/-- Innermost access tracks the pushed shift. -/
theorem local_updates (ap : AccessPattern C R) (hd : ap.depth = .local) (t : ContextTower C)
    (σ : Function.End C) : ap.resolve (t.push σ) = ap.project (σ • t.innermost) := by
  simp only [resolve, hd, DepthSpec.local_resolve, ContextTower.push_depth,
    ContextTower.push_contextAt_succ_depth]

end AccessPattern

end ContextTower
