/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic
public import Mathlib.Data.List.Chain

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

* `Spine.isExtendedProjection_pair_iff`: a spine of two heads is an extended projection if and only
  if the heads have the same family and are related by `r`.

## Implementation notes

The family and the ranking are parameters, since accounts differ on both.

Grimshaw defines projections on trees. A phrase is a projection of a head that it dominates if the
two have the same categorial features, every node between them has those features, and no node
between them is lexical. An extended projection is a projection whose functional value differs
from that of its head. Here both conditions are stated for a spine, the heads on the path from the
lexical head up. Grimshaw leaves open whether the functional value must increase from each head to
the next or may stay the same, and whether only complements, and not specifiers, take part. Here
`r` is an arbitrary relation, and a spine contains complements only. When `r` is the strict order
of functional values, no head above the lowest is lexical, as her definition requires. When `r`
lets the value stay the same, that is a further condition, which is not part of the definition
here.

## TODO

Grimshaw's conditions on which heads take which complements, and the generalized theta criterion,
are not formalized. They concern how one extended projection is embedded in another, and require
the map from a tree with a head relation to the spine of a node, which is not yet defined.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Spine

variable {H K : Type*} {family : H → K} {r : H → H → Prop} {s : Spine H}

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

/-- A spine of two heads is an extended projection if and only if the heads have the same family
and the lower is related by `r` to the higher. -/
theorem isExtendedProjection_pair_iff {x y : H} :
    IsExtendedProjection family r ⟨[x, y]⟩ ↔ family x = family y ∧ r x y := by
  refine ⟨fun h ↦ ⟨h.family_eq (by simp) (by simp), List.isChain_pair.1 h.isChain⟩,
    fun h ↦ ⟨fun c hc d hd ↦ ?_, List.isChain_pair.2 h.2⟩⟩
  simp only [mem_def, List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    first | rfl | exact h.1 | exact h.1.symm

end Spine
