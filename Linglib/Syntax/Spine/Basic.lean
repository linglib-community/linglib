/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Basic

/-!
# Spines

A spine is the list of heads a phrase projects, from the lowest upward, each the head of the
complement of the next. A phrase whose head `c` takes as its complement a phrase headed by `b`,
which in turn takes one headed by `a`, has the spine `[a, b, c]`. Specifiers and adjuncts are not
on it.

This file holds what is said of a spine by position: the head at a position, the truncation of a
spine to its lowest `n` heads, a shell appended over a spine, and the image of a spine under a map
of heads. Nothing here compares two heads, so a head may recur on a spine, and what a recurrence
means is left to the type of heads. The operations that address a head by its value are in
`Linglib/Syntax/Spine/Label.lean`.

## Main definitions

* `Spine`: the list of heads a phrase projects, bottom-up.
* `Spine.Position`, `Spine.headAt`: the positions of a spine and the head at each.
* `Spine.take`: the lowest `n` heads.
* `Spine.append`: the spine with a shell over it.
* `Spine.map`: the spine of the images of the heads.

## Implementation notes

The type of heads is a parameter, which a framework supplies. A condition on spines, such as being
an extended projection, takes what it needs to know of the heads as further parameters.

A spine of categories may repeat a category without any head occupying two positions, and a spine
of head tokens repeats one only where the same head does. `Spine.map` takes a spine of tokens to
the spine of their categories.

## References

* [grimshaw-2000]
-/

@[expose] public section

/-- A spine is the list of heads a phrase projects, from the lowest upward. -/
structure Spine (H : Type*) where
  /-- The projected heads, bottom-up. -/
  heads : List H
  deriving Repr, DecidableEq

namespace Spine

variable {H : Type*} {s t : Spine H} {c d : H} {l : List H}

instance : Membership H (Spine H) := ⟨fun s c ↦ c ∈ s.heads⟩

@[simp] theorem mem_def : c ∈ s ↔ c ∈ s.heads := Iff.rfl

instance [DecidableEq H] (c : H) (s : Spine H) : Decidable (c ∈ s) :=
  inferInstanceAs (Decidable (c ∈ s.heads))

instance (priority := low) (P : H → Prop) [DecidablePred P] (s : Spine H) :
    Decidable (∀ c ∈ s, P c) :=
  inferInstanceAs (Decidable (∀ c ∈ s.heads, P c))

instance (priority := low) (P : H → Prop) [DecidablePred P] (s : Spine H) :
    Decidable (∃ c ∈ s, P c) :=
  inferInstanceAs (Decidable (∃ c ∈ s.heads, P c))

/-! ### Positions and truncations -/

/-- The positions of a spine, from the bottom up. -/
abbrev Position (s : Spine H) : Type := Fin s.heads.length

/-- The head at a position. -/
def headAt (s : Spine H) (p : s.Position) : H := s.heads.get p

/-- The lowest `n` heads of a spine. -/
def take (s : Spine H) (n : ℕ) : Spine H := ⟨s.heads.take n⟩

@[simp] theorem heads_take (s : Spine H) (n : ℕ) : (s.take n).heads = s.heads.take n := rfl

/-! ### Shells -/

/-- Appending heads to a spine projects a nominal or adpositional shell over the phrase. -/
def append (s : Spine H) (l : List H) : Spine H := ⟨s.heads ++ l⟩

@[simp] theorem heads_append (s : Spine H) (l : List H) :
    (s.append l).heads = s.heads ++ l :=
  rfl

@[simp] theorem mem_append : c ∈ s.append l ↔ c ∈ s ∨ c ∈ l := List.mem_append

/-! ### The image of a spine -/

section Map

variable {K : Type*} {f : H → K}

/-- The spine of the images of the heads, as when a head's features are forgotten for its
category. -/
def map (f : H → K) (s : Spine H) : Spine K := ⟨s.heads.map f⟩

@[simp] theorem heads_map (f : H → K) (s : Spine H) : (s.map f).heads = s.heads.map f := rfl

@[simp] theorem mem_map {k : K} : k ∈ s.map f ↔ ∃ c ∈ s, f c = k := List.mem_map

end Map

end Spine
