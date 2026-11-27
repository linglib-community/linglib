/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
public import Linglib.Syntax.Minimalist.Spine

/-!
# Complement sizes

This file defines the size of a clausal complement, the highest head that it projects, and orders
sizes by the order of the categories. Wurmbrand classifies infinitival complements by the structure
they project: a vP under a restructuring verb, a TP under a propositional attitude and a modal
projection for a future infinitive, beside the CP of a finite clause.

## Main definitions

* `Minimalist.ComplementSize`: a clausal complement measured by its highest head.
* `Spine.size`: the size of a spine.
* `Minimalist.ComplementSize.vP`, `Minimalist.ComplementSize.tP`,
  `Minimalist.ComplementSize.finP`, `Minimalist.ComplementSize.cP`: the standard sizes.

## Main results

* `Spine.size_le_size`: a nonempty spine whose heads all lie on an extended projection is no larger
  than that extended projection.

## Implementation notes

`Minimalist.ComplementSize` wraps a category and carries the order of the categories as an instance
of its own, lifted along `Minimalist.ComplementSize.highestHead`, so that a file that uses sizes
need not open the scoped order of the categories. Two sizes whose highest heads are each no higher
than the other, such as those of tense and negation, are each no larger than the other without
being equal, so sizes are preordered.

Spines are also ordered by inclusion of the sets of heads that they project. `Spine.size_le_size`
relates that order to the order of sizes.

## References

* [wurmbrand-2014]
* [grimshaw-2000]
-/

@[expose] public section

open scoped Minimalist.ExtendedProjection

namespace Minimalist

/-- A **complement size** is a clausal complement measured by the highest head that it
projects. -/
structure ComplementSize where
  /-- The highest head of the complement. -/
  highestHead : Cat
  deriving DecidableEq, Repr

namespace ComplementSize

variable {a b : ComplementSize}

/-- A complement size `a` is **no larger than** a complement size `b`, written `a ≤ b`, when the
highest head of `a` is no higher than the highest head of `b`. -/
instance : Preorder ComplementSize := Preorder.lift highestHead

instance : DecidableLE ComplementSize := fun a b ↦
  inferInstanceAs (Decidable (a.highestHead ≤ b.highestHead))

instance : DecidableLT ComplementSize := decidableLTOfDecidableLE

theorem le_def : a ≤ b ↔ a.highestHead ≤ b.highestHead := Iff.rfl

end ComplementSize

end Minimalist

namespace Spine

open Minimalist

variable {s t : Spine Cat} {c : Cat}

theorem cP_isExtendedProjection : cP.IsExtendedProjection Cat.family (· ≤ ·) := by
  decide +kernel

/-! ### The size of a spine -/

/-- The **size** of a spine is its highest head. The size of the empty spine is that of the bare
verb. -/
def size (s : Spine Cat) : ComplementSize := ⟨s.heads.getLastD .V⟩

private theorem le_getLastD {l : List Cat} (hp : l.Pairwise (· ≤ ·)) (hc : c ∈ l) :
    c ≤ l.getLastD .V := by
  have hne : l ≠ [] := List.ne_nil_of_mem hc
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  rw [← List.dropLast_append_getLast hne, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · rw [← List.dropLast_append_getLast hne, List.pairwise_append] at hp
    exact hp.2.2 c hc _ (List.mem_singleton_self _)
  · exact le_rfl

/-- In an extended projection, every head is no higher than the highest head. -/
theorem IsExtendedProjection.le_size (hs : s.IsExtendedProjection Cat.family (· ≤ ·))
    (hc : c ∈ s) : c ≤ s.size.highestHead :=
  le_getLastD hs.pairwise hc

/-- A nonempty spine whose heads all lie on an extended projection is no larger than that extended
projection. -/
theorem size_le_size (h : s ≤ t) (ht : t.IsExtendedProjection Cat.family (· ≤ ·))
    (hs : s.heads ≠ []) : s.size ≤ t.size := by
  obtain ⟨l, c, hlc⟩ := (List.eq_nil_or_concat s.heads).resolve_left hs
  show s.heads.getLastD .V ≤ t.size.highestHead
  rw [hlc, List.concat_eq_append, List.getLastD_concat]
  exact ht.le_size (le_iff_forall_mem.1 h c (by simp [hlc]))

end Spine

namespace Minimalist

/-! ### The standard sizes -/

namespace ComplementSize

/-- The **vP size** is the size of the vP, the complement of a restructuring verb. -/
def vP : ComplementSize := Spine.vP.size

/-- The **TP size** is the size of the TP, the complement of a propositional attitude. -/
def tP : ComplementSize := Spine.tP.size

/-- The **FinP size** is the size of a clause that projects the lowest head of the left
periphery. -/
def finP : ComplementSize := ⟨.Fin⟩

/-- The **CP size** is the size of the CP, the finite clause. -/
def cP : ComplementSize := Spine.cP.size

theorem vP_le_tP : vP ≤ tP :=
  Spine.size_le_size Spine.vP_le_tP (by decide +kernel) (List.cons_ne_nil _ _)

theorem tP_le_cP : tP ≤ cP :=
  Spine.size_le_size Spine.tP_le_cP Spine.cP_isExtendedProjection
    (List.cons_ne_nil _ _)

end ComplementSize

end Minimalist
