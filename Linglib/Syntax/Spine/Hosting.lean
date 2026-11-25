/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.OrdConnected
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Hostings of a spine

On accounts where the heads of a clause form a spine and a word realizes several of them, a word
is pronounced at the position of one head. A hosting of a spine lists, for each of its positions
from the bottom up, the head at which that position is pronounced. Words given by their heads and
their sites determine a hosting.

A hosting is contiguous, in the sense of `IsContiguous`, when the positions pronounced at one
head form an unbroken stretch of the spine. Words that divide a spine without repeated heads,
each pronounced at one of its own heads, give a contiguous hosting.

## Main definitions

* `Spine.hosting`: the hosting that words with their sites give a spine.

## Main results

* `Spine.isContiguous_hosting`: words dividing a spine without repeated heads, each pronounced at
  one of its own heads, give a contiguous hosting.

## Implementation notes

Contiguity of a hosting has no name of its own here: it is `IsContiguous` on the list, the
predicate that says of a paradigm that no form recurs across another.

The Head Movement Constraint of [travis-1984] is a condition on a step of upward movement, that
a head moves only into the head that governs it. Contiguity is a condition on the outcome.
[brody-2000] sets out the two assumptions usually made of head chains, that constraint and the
ban on excorporation, under which a head moves on only together with its host; the two together
give contiguity. [harizanov-gribanova-2019] state it of displacement in either direction. A
hosting in which a head leaves the word it has joined, pronounced as `[z, y, z]`, is not
contiguous, though each of its steps is local.

Contiguity reads the hosting and not the spine. It does not say that a word is pronounced at one
of its own heads, which `Spine.isContiguous_hosting` assumes: the hosting `[c, b, b]` of a spine
`[a, b, c]` is contiguous.

A site is a head and not a position: in [harizanov-gribanova-2019] word formation acts on the
syntactic object, whichever positions it occupies.

## References

* [travis-1984]
* [brody-2000]
* [svenonius-2012]
* [harizanov-gribanova-2019]
* [arregi-pietraszko-2021]
-/

@[expose] public section

namespace Spine

variable {H : Type*} {ws : List (List H × H)}

/-- The hosting that words give a spine. A word is its heads, lowest first, with the head at
which it is pronounced, and every position of a word is pronounced there. -/
def hosting (ws : List (List H × H)) : List H :=
  ws.flatMap fun w ↦ List.replicate w.1.length w.2

theorem length_hosting (ws : List (List H × H)) :
    (hosting ws).length = (ws.flatMap Prod.fst).length := by
  simp [hosting, List.length_flatMap]

/-- Words that divide a spine without repeated heads, each pronounced at one of its own heads,
give a contiguous hosting: the words are disjoint, so their sites are distinct. -/
theorem isContiguous_hosting (hsite : ∀ w ∈ ws, w.2 ∈ w.1) (hnd : (ws.flatMap Prod.fst).Nodup) :
    IsContiguous (hosting ws).get := by
  have hs : (ws.map Prod.snd).Nodup := by
    rw [List.nodup_flatMap] at hnd
    rw [List.Nodup, List.pairwise_map]
    exact hnd.2.imp_of_mem fun ha hb hd he ↦ hd (hsite _ ha) (he ▸ hsite _ hb)
  have e : (ws.map fun w ↦ (w.1.length, w.2)).flatMap (fun p ↦ List.replicate p.1 p.2) =
      hosting ws := by
    simp [hosting, List.flatMap_map]
  exact e ▸ List.isContiguous_get_flatMap_replicate (l := ws.map fun w ↦ (w.1.length, w.2))
    (by simpa [List.map_map, Function.comp_def] using hs)

-- a hosting that returns to a head after leaving it is not contiguous
example {a b : H} (hab : a ≠ b) : ¬ IsContiguous [a, b, a].get := fun h ↦
  hab (@h (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (Fin.zero_le _) (Fin.le_of_lt (by simp)) rfl)

end Spine
