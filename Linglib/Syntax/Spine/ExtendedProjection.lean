/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Label

/-!
# Extended projections

A clause is built on a verb, but much of its structure is not the verb's: inflection and the
complementizer each head a phrase of their own above it. In what sense is the clause still the
verb's phrase? Grimshaw's answer is that these phrases form one **extended projection**: a lexical
head together with the functional heads above it, all of the category of the lexical head and
ordered by their functional level, the lexical head lowest. A noun phrase is built the same way,
with the determiner above the noun.

Two things have to be known of the heads to say this. Each head belongs to a **family**, the
category it shares with its lexical head, so that inflection and the complementizer are of the
family of the verb and the determiner is of the family of the noun. And the heads are ranked, by a
relation that says when one head is no higher than another. A spine is then an extended projection
when its heads are of one family and each is ranked no higher than the next head up.

Take Grimshaw's categories: the family sends `V`, `I` and `C` to *verbal* and `N` and `D` to
*nominal*, and the ranking is `V`, `I`, `C`. The spine `[V, I, C]` is an extended projection. The
spine `[V, C, I]` is of one family but descends, and `[V, I, C, D]`, a clause under a determiner,
is of two families.

## Implementation notes

The family and the ranking are parameters, since accounts differ on both: on which heads are of
one category, and on whether heads are ranked by a fixed sequence, by the structures an account
draws, or not at all. `Linglib/Syntax/Spine/Hierarchy.lean` gives the ranking that a set of
spines determines.

Grimshaw defines a projection on a tree, by dominance: a phrase is a projection of a head it
dominates when the two share their categorial features, every node between them shares them too,
and none of those nodes is lexical. An extended projection is a projection whose functional value
differs from its head's. The two conditions are stated here of a spine, the heads on the path from
the lexical head up. She leaves open whether the functional value must rise from each head to the
next or may also stay the same; the ranking here is any relation, so either can be given. She adds
that it may be necessary to let only complements, and not specifiers, take part; a spine has only
complements.

## TODO

Grimshaw's conditions on which heads take which complements, and her generalized theta criterion,
are not formalized. They concern how one extended projection sits inside another, and so need the
map from a tree with its head relation to the spine of a node, which is not yet stated; under that
map her definition on trees and the one here on spines should correspond.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Spine

variable {H K : Type*} {family : H → K} {r : H → H → Prop} {s : Spine H} {c d : H}

/-- A spine is an **extended projection**, for a family of each head and a ranking of the heads,
when its heads are of one family and each is ranked no higher than the next head up. -/
structure IsExtendedProjection (family : H → K) (r : H → H → Prop) (s : Spine H) : Prop where
  /-- The heads are of one family. -/
  family_eq ⦃c : H⦄ (hc : c ∈ s) ⦃d : H⦄ (hd : d ∈ s) : family c = family d
  /-- Each head is ranked no higher than the next head up. -/
  isChain : s.heads.IsChain r

theorem isExtendedProjection_iff : s.IsExtendedProjection family r ↔
    (∀ c ∈ s, ∀ d ∈ s, family c = family d) ∧ s.heads.IsChain r :=
  ⟨fun h ↦ ⟨fun _ hc _ hd ↦ h.family_eq hc hd, h.isChain⟩,
    fun h ↦ ⟨fun _ hc _ hd ↦ h.1 _ hc _ hd, h.2⟩⟩

instance [DecidableEq H] [DecidableEq K] [DecidableRel r] (s : Spine H) :
    Decidable (s.IsExtendedProjection family r) :=
  decidable_of_iff _ isExtendedProjection_iff.symm

/-- In an extended projection, each head is ranked no higher than any head above it on the
spine. -/
theorem IsExtendedProjection.pairwise [IsTrans H r] (h : s.IsExtendedProjection family r) :
    s.heads.Pairwise r :=
  List.isChain_iff_pairwise.1 h.isChain

/-- When the ranking only relates heads of one family, a spine that ascends is an extended
projection: its heads are then of one family. -/
theorem isExtendedProjection_iff_isChain [IsTrans H r] (hr : ∀ x y, r x y → family x = family y) :
    s.IsExtendedProjection family r ↔ s.heads.IsChain r :=
  ⟨IsExtendedProjection.isChain, fun h ↦
    have hp := List.isChain_iff_pairwise.1 h
    ⟨fun _ hc _ hd ↦ List.Pairwise.forall_of_forall_of_flip
      (R := fun x y ↦ family x = family y) (fun _ _ ↦ rfl) (hp.imp (hr _ _))
      (hp.imp fun h ↦ (hr _ _ h).symm) hc hd, h⟩⟩

variable [DecidableEq H]

/-- In an extended projection, a head is either inside the complement of a given head or ranked
at least as high as that head. -/
theorem IsExtendedProjection.mem_below_or_rel [Std.Refl r] [IsTrans H r]
    (hs : s.IsExtendedProjection family r) (hc : c ∈ s) (hd : d ∈ s) : d ∈ s.below c ∨ r c d :=
  Spine.mem_below_or_rel hs.pairwise hc hd

/-- In an extended projection, every head inside the complement of a head is ranked no higher than
that head. -/
theorem IsExtendedProjection.rel_of_mem_below [IsTrans H r]
    (hs : s.IsExtendedProjection family r) (hc : c ∈ s) (hd : d ∈ s.below c) : r d c :=
  Spine.rel_of_mem_below hs.pairwise hc hd

end Spine
