/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.ExtendedProjection
public import Linglib.Syntax.Spine.Label

/-!
# Spines of extended projections

A spine of categories is an extended projection in Grimshaw's sense when each head extends the
one below it. Keine observes that category features project bilaterally within an extended
projection, so the label of a spine is the set of heads it projects.

## Main definitions

* `Spine.IsExtendedProjection`: a spine each of whose heads extends the one below it.
* `Spine.vP`, `Spine.tP`, `Spine.cP`: the clause sizes of the verbal extended projection.

## Main results

* `Spine.IsExtendedProjection.pairwise`: in an extended projection every head extends each head
  below it.

## References

* [grimshaw-2005]
* [keine-2020]
* [deal-2026]
-/

@[expose] public section

namespace Spine

open Minimalist

variable {s t : Spine Cat} {c d : Cat} {l : List Cat}

/-! ### Extended projections -/

/-- A spine is an extended projection when each head extends the one below it, so that its heads
are of one family. -/
def IsExtendedProjection (s : Spine Cat) : Prop := s.heads.IsChain Cat.ExtendsTo

instance (s : Spine Cat) : Decidable s.IsExtendedProjection :=
  inferInstanceAs (Decidable (List.IsChain _ _))

/-- In an extended projection every head extends each head below it. -/
theorem IsExtendedProjection.pairwise (h : s.IsExtendedProjection) :
    s.heads.Pairwise Cat.ExtendsTo :=
  List.isChain_iff_pairwise.1 h

/-- In an extended projection a head lies in the complement of another or extends it. -/
theorem IsExtendedProjection.mem_below_or_extendsTo (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hd : d ∈ s) : d ∈ s.below c ∨ c.ExtendsTo d :=
  mem_below_or_rel hs.pairwise hc hd

/-- In an extended projection a head extends every head in its complement. -/
theorem IsExtendedProjection.extendsTo_of_mem_below (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hd : d ∈ s.below c) : d.ExtendsTo c :=
  rel_of_mem_below hs.pairwise hc hd

/-! ### Clause sizes -/

/-- The vP-sized clause `[V, v]`, the small nonfinite clause. -/
def vP : Spine Cat := ⟨[.V, .v]⟩

/-- The TP-sized clause `[V, v, T]`, the large nonfinite clause. -/
def tP : Spine Cat := ⟨[.V, .v, .T]⟩

/-- The CP-sized clause `[V, v, T, C]`, the finite clause. -/
def cP : Spine Cat := ⟨[.V, .v, .T, .C]⟩

@[simp] theorem tP_below_T : tP.below .T = vP := by decide

@[simp] theorem cP_below_T : cP.below .T = vP := by decide

@[simp] theorem cP_below_C : cP.below .C = tP := by decide

theorem vP_le_tP : vP ≤ tP := by decide

theorem tP_le_cP : tP ≤ cP := by decide

theorem cP_isExtendedProjection : cP.IsExtendedProjection := by decide +kernel

end Spine
