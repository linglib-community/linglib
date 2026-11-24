/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Occurrence

/-!
# Head chains

In the Generalized Head Movement of Arregi and Pietraszko a head shares its morphological
features with the head of its complement, so a stretch of the spine forms a head chain around
one word, and the word is pronounced at the highest strong position of the chain, or at its
highest position when none is strong. This file is to hold head chains over the positions of a
`Spine`, with the choice of the heads that share features and of the strong heads as parameters,
so that a head chain account and amalgamation
(`Morphology/DistributedMorphology/Amalgamation.lean`) give hosts for the same positions.

## TODO

* Head chains on a spine and their pronunciation, now `ArregiPietraszko2021.HeadChain` over the
  categories of one study. Its word is a `DistributedMorphology.ComplexHead`, which admits one
  bracketing; the hosts need only the positions.
* The hosts of a head chain account, as `DistributedMorphology.MorphosyntacticWord.hosts` is for
  words, and their contiguity.
* The comparison with amalgamation on a spine without repeated heads, and across clause types.
* Chain splitting, where a word's terminal is pronounced away from its position.

## References

* [arregi-pietraszko-2021]
* [harizanov-gribanova-2019]
-/
