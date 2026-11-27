/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Complement sizes

How much of a clause does a complement contain? Wurmbrand sorts infinitival complements by the
structure they project: a bare vP under a restructuring verb, a TP under a propositional attitude
and a modal projection for a future infinitive, beside the full CP of a finite clause. A complement
is measured by its highest head, its **size**, and one size is at most another when its highest
head is at most the other's in the order of the categories. Two sizes whose heads are level, as
tense and negation are, are each at most the other without being equal, and two sizes that no
source relates, a nominalized clause and a CP, are incomparable.

The **size of a spine** is its highest head. A spine whose heads all occur on an extended projection
is no larger than it. The standard clauses are the vP, the TP and the CP, and their sizes ascend as
their spines grow.

## Implementation notes

`Minimalist.ComplementSize` wraps a category and carries the order of the categories, lifted
along `Minimalist.ComplementSize.highestHead`, as an instance of its own, so that a file that
speaks of sizes need not adopt the order on the categories. Spines have an order of their own,
inclusion of the sets of heads they project; `Spine.size_le_size` says that on extended projections
it refines the order of sizes.

## References

* [wurmbrand-2014]
* [grimshaw-2000]
-/

@[expose] public section

open scoped Minimalist.ExtendedProjection

namespace Minimalist

/-- A **complement size** is a clausal complement measured by the highest head it projects. -/
structure ComplementSize where
  /-- The highest functional head in the complement. -/
  highestHead : Cat
  deriving DecidableEq, Repr

namespace ComplementSize

variable {a b : ComplementSize}

/-- One complement size is at most another, written `a ≤ b`, when its highest head is at most the
other's. -/
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

/-!
### The standard clauses

The clauses of the verbal extended projection that the literature on complement size names.
-/

/-- The **vP** is the spine `[V, v]`, the small nonfinite clause. -/
def vP : Spine Cat := ⟨[.V, .v]⟩

/-- The **TP** is the spine `[V, v, T]`, the large nonfinite clause. -/
def tP : Spine Cat := ⟨[.V, .v, .T]⟩

/-- The **CP** is the spine `[V, v, T, C]`, the finite clause. -/
def cP : Spine Cat := ⟨[.V, .v, .T, .C]⟩

@[simp] theorem tP_below_T : tP.below .T = vP := by decide

@[simp] theorem cP_below_T : cP.below .T = vP := by decide

@[simp] theorem cP_below_C : cP.below .C = tP := by decide

theorem vP_le_tP : vP ≤ tP := by decide

theorem tP_le_cP : tP ≤ cP := by decide

theorem cP_isExtendedProjection : cP.IsExtendedProjection := by decide +kernel

/-!
### The size of a spine
-/

/-- The **size** of a spine is its highest head. The empty spine has the size of a bare lexical
head. -/
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

/-- In an extended projection every head is at most the highest one. -/
theorem IsExtendedProjection.le_size (hs : s.IsExtendedProjection) (hc : c ∈ s) :
    c ≤ s.size.highestHead :=
  le_getLastD hs.pairwise hc

/-- A nonempty spine whose heads an extended projection projects is no larger than it. -/
theorem size_le_size (h : s ≤ t) (ht : t.IsExtendedProjection) (hs : s.heads ≠ []) :
    s.size ≤ t.size := by
  obtain ⟨l, c, hlc⟩ := (List.eq_nil_or_concat s.heads).resolve_left hs
  show s.heads.getLastD .V ≤ t.size.highestHead
  rw [hlc, List.concat_eq_append, List.getLastD_concat]
  exact ht.le_size (le_iff_forall_mem.1 h c (by simp [hlc]))

end Spine

namespace Minimalist

/-!
### The standard sizes
-/

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
