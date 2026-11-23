/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TierTree.Basic

/-!
# Maps of alphabets and of tiers

An autosegmental representation `X : AR τ` has a word over the alphabet `τ i` on each tier `i`,
and association lines between the tiers. This file defines two operations that change the
family of alphabets.

Given a map of alphabets `g i : τ i → τ' i` for each tier `i`, the relabelling `X.mapRange g`
applies `g i` to each letter of tier `i` and keeps the lines. Given a map of tiers `h : κ → ι`,
the restriction `X.comapDomain h` is the representation on the tiers `κ` whose tier `k` is tier
`h k` of `X`, with the lines of `X` between these tiers. Both are monoid homomorphisms, and both
preserve the No-Crossing Constraint.

## Implementation notes

The names follow `DFinsupp.mapRange` and `DFinsupp.comapDomain`, which map a dependent family
along its values and along its index. `AR.map` is a different operation: it moves the positions
of a representation within its tiers.

## TODO

* The melody of a restriction, when `h` is a map of trees of tiers.
* The contraction of a tier, which composes the lines through it.
* The merger of two tiers into one.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι κ κ' : Type*} {τ τ' τ'' : ι → Type*}

/-! ### Relabelling -/

section MapRange

variable (g : ∀ i, τ i → τ' i) (X Y : AR τ)

/-- The relabelling of `X` by `g`: the word of tier `i` is mapped by `g i`, and the lines are those
of `X`. -/
def mapRange : AR τ' where
  word i := (X.word i).map (g i)
  lines := X.lines
  lines_self := X.lines_self
  swap_mem_lines := X.swap_mem_lines
  fst_lt_of_mem_lines _ _ _ _ h := by simpa using X.fst_lt_of_mem_lines h

@[simp] theorem word_mapRange (i : ι) : (X.mapRange g).word i = (X.word i).map (g i) := rfl

@[simp] theorem lines_mapRange : (X.mapRange g).lines = X.lines := rfl

@[simp] theorem link_mapRange {i j : ι} {p q : ℕ} :
    (X.mapRange g).Link i j p q ↔ X.Link i j p q := .rfl

@[simp] theorem mapRange_id : X.mapRange (fun _ ↦ id) = X :=
  AR.ext (funext fun _ ↦ List.map_id _) fun _ _ _ _ ↦ .rfl

theorem mapRange_mapRange (g' : ∀ i, τ' i → τ'' i) :
    (X.mapRange g).mapRange g' = X.mapRange fun i ↦ g' i ∘ g i :=
  AR.ext (funext fun _ ↦ List.map_map) fun _ _ _ _ ↦ .rfl

@[simp] theorem mapRange_one : (1 : AR τ).mapRange g = 1 := rfl

@[simp] theorem mapRange_mul : (X * Y).mapRange g = X.mapRange g * Y.mapRange g :=
  AR.ext (funext fun _ ↦ List.map_append) fun i j p q ↦ by simp [link_mul]

/-- `AR.mapRange` as a monoid homomorphism. -/
def mapRangeHom : AR τ →* AR τ' where
  toFun X := X.mapRange g
  map_one' := mapRange_one g
  map_mul' := mapRange_mul g

@[simp] theorem mapRangeHom_apply : mapRangeHom g X = X.mapRange g := rfl

theorem mapRangeHom_id : mapRangeHom (τ := τ) (fun _ ↦ id) = MonoidHom.id _ :=
  MonoidHom.ext mapRange_id

theorem mapRangeHom_comp (g' : ∀ i, τ' i → τ'' i) :
    mapRangeHom (fun i ↦ g' i ∘ g i) = (mapRangeHom g').comp (mapRangeHom g) :=
  MonoidHom.ext fun X ↦ (mapRange_mapRange g X g').symm

/-- A relabelling satisfies the No-Crossing Constraint if and only if the representation does. -/
@[simp] theorem noCrossing_mapRange : (X.mapRange g).NoCrossing ↔ X.NoCrossing := .rfl

/-- The word of tier `i` of a relabelling is the word of tier `i` mapped by `g i`. -/
theorem wordHom_comp_mapRangeHom (i : ι) :
    (wordHom i).comp (mapRangeHom g) = (FreeMonoid.map (g i)).comp (wordHom i) :=
  MonoidHom.ext fun _ ↦ rfl

variable [Fintype ι] [DecidableEq ι] (T : ParentTree ι)

@[simp] theorem children_mapRange (v : ι × ℕ) :
    (X.mapRange g).children T v = X.children T v := rfl

@[simp] theorem descendants_mapRange :
    ∀ (d : ℕ) (v : ι × ℕ), (X.mapRange g).descendants T d v = X.descendants T d v
  | 0, _ => rfl
  | d + 1, v => by
    show insert v (((X.mapRange g).children T v).biUnion ((X.mapRange g).descendants T d)) =
      insert v ((X.children T v).biUnion (X.descendants T d))
    rw [children_mapRange, funext (descendants_mapRange d)]

@[simp] theorem dominates_mapRange {k q : ℕ} {j : ι} :
    (X.mapRange g).Dominates T k j q ↔ X.Dominates T k j q := by
  simp only [Dominates, descendants_mapRange]

/-- The melody of a slot of a relabelling is its melody mapped by `g`. -/
theorem melody_mapRange (k : ℕ) (j : ι) :
    (X.mapRange g).melody T k j = (X.melody T k j).map (g j) := by
  simp [melody, List.zipIdx_map, List.filter_map, Function.comp_def]

end MapRange

/-! ### Restriction -/

section ComapDomain

variable (h : κ → ι) (X Y : AR τ)

/-- The restriction of `X` along `h`: tier `k` is tier `h k` of `X`, and the lines between tiers `k`
and `k'` are those of `X` between `h k` and `h k'`. -/
def comapDomain : AR fun k ↦ τ (h k) where
  word k := X.word (h k)
  lines k k' := X.lines (h k) (h k')
  lines_self k := X.lines_self (h k)
  swap_mem_lines _ _ _ _ hl := X.swap_mem_lines hl
  fst_lt_of_mem_lines _ _ _ _ hl := X.fst_lt_of_mem_lines hl

@[simp] theorem word_comapDomain (k : κ) : (X.comapDomain h).word k = X.word (h k) := rfl

@[simp] theorem lines_comapDomain (k k' : κ) :
    (X.comapDomain h).lines k k' = X.lines (h k) (h k') := rfl

@[simp] theorem link_comapDomain {k k' : κ} {p q : ℕ} :
    (X.comapDomain h).Link k k' p q ↔ X.Link (h k) (h k') p q := .rfl

@[simp] theorem comapDomain_id : X.comapDomain id = X := rfl

theorem comapDomain_comapDomain (h' : κ' → κ) :
    (X.comapDomain h).comapDomain h' = X.comapDomain (h ∘ h') := rfl

@[simp] theorem comapDomain_one : (1 : AR τ).comapDomain h = 1 := rfl

@[simp] theorem comapDomain_mul : (X * Y).comapDomain h = X.comapDomain h * Y.comapDomain h :=
  rfl

/-- `AR.comapDomain` as a monoid homomorphism. -/
def comapDomainHom : AR τ →* AR fun k ↦ τ (h k) where
  toFun X := X.comapDomain h
  map_one' := comapDomain_one h
  map_mul' := comapDomain_mul h

@[simp] theorem comapDomainHom_apply : comapDomainHom h X = X.comapDomain h := rfl

/-- A restriction of a representation that satisfies the No-Crossing Constraint satisfies it. -/
theorem NoCrossing.comapDomain {X : AR τ} (hX : X.NoCrossing) : (X.comapDomain h).NoCrossing :=
  fun _ _ ↦ hX _ _

/-- The word of tier `k` of a restriction along `h` is the word of tier `h k`. -/
theorem wordHom_comp_comapDomainHom (k : κ) :
    (wordHom k).comp (comapDomainHom (τ := τ) h) = wordHom (h k) := rfl

/-- The restriction of a relabelling is the relabelling of the restriction. -/
theorem comapDomain_mapRange (g : ∀ i, τ i → τ' i) :
    (X.mapRange g).comapDomain h = (X.comapDomain h).mapRange fun k ↦ g (h k) := rfl

end ComapDomain

end Autosegmental.AR
