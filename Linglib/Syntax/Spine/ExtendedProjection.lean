/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Label

/-!
# Extended projections

This file defines extended projections of a spine. Let `family` be a map from heads to their
categories and `r` a relation that ranks the heads. A spine is an extended projection with respect
to `family` and `r` if all its heads have the same family and each head is related by `r` to the
next head up.

In the system of Grimshaw, the heads `V`, `I` and `C` are verbal, with functional values `0`, `1`
and `2`, and the heads `N` and `D` are nominal, with functional values `0` and `1`. With `r` the
order of functional values, the spine `[V, I, C]` is an extended projection. The spine `[V, C, I]`
is not, since the functional value decreases, and `[V, I, C, D]` is not, since `D` is nominal.

## Main definitions

* `Spine.IsExtendedProjection`: a spine whose heads have the same family and are ranked by `r`
  from the bottom up.

## Main results

* `Spine.isExtendedProjection_iff_isChain`: if `r` only relates heads of the same family, a spine
  is an extended projection if and only if it is a chain for `r`.

## Implementation notes

The family and the ranking are parameters, since accounts differ on both. The ranking that a set of
spines determines is defined in `Linglib/Syntax/Spine/Hierarchy.lean`.

Grimshaw defines projections on trees. A phrase is a projection of a head that it dominates if the
two have the same categorial features, every node between them has those features, and no node
between them is lexical. An extended projection is a projection whose functional value differs
from that of its head. Here both conditions are stated for a spine, the heads on the path from the
lexical head up. Grimshaw leaves open whether the functional value must increase from each head to
the next or may stay the same, and whether only complements, and not specifiers, take part. Here
`r` is an arbitrary relation, and a spine contains complements only.

## TODO

Grimshaw's conditions on which heads take which complements, and the generalized theta criterion,
are not formalized. They concern how one extended projection is embedded in another, and require
the map from a tree with a head relation to the spine of a node, which is not yet defined.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Spine

variable {H K : Type*} {family : H → K} {r : H → H → Prop} {s : Spine H} {c d : H}

/-- A spine is an **extended projection** with respect to `family` and `r` if all its heads have
the same family and each head is related by `r` to the next head up. -/
structure IsExtendedProjection (family : H → K) (r : H → H → Prop) (s : Spine H) : Prop where
  /-- All heads have the same family. -/
  family_eq ⦃c : H⦄ (hc : c ∈ s) ⦃d : H⦄ (hd : d ∈ s) : family c = family d
  /-- Each head is related by `r` to the next head up. -/
  isChain : s.heads.IsChain r

theorem isExtendedProjection_iff : s.IsExtendedProjection family r ↔
    (∀ c ∈ s, ∀ d ∈ s, family c = family d) ∧ s.heads.IsChain r :=
  ⟨fun h ↦ ⟨fun _ hc _ hd ↦ h.family_eq hc hd, h.isChain⟩,
    fun h ↦ ⟨fun _ hc _ hd ↦ h.1 _ hc _ hd, h.2⟩⟩

instance [DecidableEq H] [DecidableEq K] [DecidableRel r] (s : Spine H) :
    Decidable (s.IsExtendedProjection family r) :=
  decidable_of_iff _ isExtendedProjection_iff.symm

theorem IsExtendedProjection.pairwise [IsTrans H r] (h : s.IsExtendedProjection family r) :
    s.heads.Pairwise r :=
  List.isChain_iff_pairwise.1 h.isChain

/-- If `r` only relates heads of the same family, a spine is an extended projection if and only if
it is a chain for `r`. -/
theorem isExtendedProjection_iff_isChain [IsTrans H r] (hr : ∀ x y, r x y → family x = family y) :
    s.IsExtendedProjection family r ↔ s.heads.IsChain r :=
  ⟨IsExtendedProjection.isChain, fun h ↦
    have hp := List.isChain_iff_pairwise.1 h
    ⟨fun _ hc _ hd ↦ List.Pairwise.forall_of_forall_of_flip
      (R := fun x y ↦ family x = family y) (fun _ _ ↦ rfl) (hp.imp (hr _ _))
      (hp.imp fun h ↦ (hr _ _ h).symm) hc hd, h⟩⟩

variable [DecidableEq H]

/-- In an extended projection, a head `d` is in the complement of a head `c` or `r c d` holds. -/
theorem IsExtendedProjection.mem_below_or_rel [Std.Refl r] [IsTrans H r]
    (hs : s.IsExtendedProjection family r) (hc : c ∈ s) (hd : d ∈ s) : d ∈ s.below c ∨ r c d :=
  Spine.mem_below_or_rel hs.pairwise hc hd

/-- In an extended projection, `r d c` holds for every head `d` in the complement of a head
`c`. -/
theorem IsExtendedProjection.rel_of_mem_below [IsTrans H r]
    (hs : s.IsExtendedProjection family r) (hc : c ∈ s) (hd : d ∈ s.below c) : r d c :=
  Spine.rel_of_mem_below hs.pairwise hc hd

end Spine
