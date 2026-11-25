/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.FreeSemigroup
public import Linglib.Generalizations.HeadMovementConstraint

/-!
# Morphosyntactic words

A morphosyntactic word, in the sense of Embick and Noyer, is a head at the input to Morphology
that is not contained in another head: a terminal, or a complex of terminals that head adjunction
has put together. This file records a morphosyntactic word by the head in whose position it is
pronounced and the grouping of its terminals, a bracketing of them. Accounts of how such words
are formed differ in which bracketings and positions they allow, so the type allows all of them.

## Main definitions

* `DistributedMorphology.MorphosyntacticWord`: a morphosyntactic word, its site and the
  bracketing of its terminals.
* `DistributedMorphology.MorphosyntacticWord.heads`: its terminals, lowest first.
* `DistributedMorphology.MorphosyntacticWord.sited`: the words with their sites.
* `DistributedMorphology.MorphosyntacticWord.hosts`: for the words on a spine, the head at which
  each position of the spine is pronounced.

## Main results

* `DistributedMorphology.MorphosyntacticWord.hmc_hosts`: words that divide a spine without
  repeated heads, each pronounced at one of its own heads, obey the Head Movement Constraint.

## Implementation notes

`DistributedMorphology.ComplexHead` is a root with the heads adjoined above it in order, the
bracketing in which each head is adjoined outside the ones below. A `MorphosyntacticWord` allows
any bracketing. The name is provisional. A `Morphology.Word` is a word token, the form a
morphosyntactic word is realized as.

## References

* [embick-noyer-2001]
* [harizanov-gribanova-2019]
* [arregi-pietraszko-2021]
-/

@[expose] public section

namespace DistributedMorphology

open FreeMagma

variable {H : Type*}

/-- A morphosyntactic word: the terminals pronounced together, at the position of one of
them. -/
structure MorphosyntacticWord (H : Type*) where
  /-- The head in whose position the word is pronounced. -/
  site : H
  /-- The grouping of the heads of the word, each product listing the lower constituent first. -/
  bracketing : FreeMagma H
  deriving DecidableEq, Repr

/-- The terminals of a morphosyntactic word, lowest first. -/
def MorphosyntacticWord.heads (w : MorphosyntacticWord H) : List H :=
  (toFreeSemigroup w.bracketing).toFreeMonoid.toList

namespace MorphosyntacticWord

/-- The words with their sites, forgetting how their heads are grouped. -/
def sited (ws : List (MorphosyntacticWord H)) : List (List H × H) :=
  ws.map fun w ↦ (w.heads, w.site)

/-- The hosts of the words on a spine, lowest first: each position of the spine with the head at
which its word is pronounced. -/
def hosts (ws : List (MorphosyntacticWord H)) : List H := HMC.hosting (sited ws)

theorem length_hosts (ws : List (MorphosyntacticWord H)) :
    (hosts ws).length = (ws.flatMap heads).length := by
  simp [hosts, sited, HMC.length_hosting, List.flatMap_map]

/-- Words that divide a spine without repeated heads, each pronounced at one of its own heads,
obey the Head Movement Constraint. -/
theorem hmc_hosts {ws : List (MorphosyntacticWord H)} (hsite : ∀ w ∈ ws, w.site ∈ w.heads)
    (hnd : (ws.flatMap heads).Nodup) : HMC.Holds (hosts ws) :=
  HMC.holds_hosting (by simpa [sited] using hsite) (by simpa [sited, List.flatMap_map] using hnd)

end MorphosyntacticWord

end DistributedMorphology
