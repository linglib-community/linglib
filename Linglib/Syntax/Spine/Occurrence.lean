/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Nodup

/-!
# Occurrences of a head on a spine

A head may occupy several positions of a spine, as a head that has moved does. The positions it
occupies are its occurrences, and a chain resolution says at which of them it is pronounced: the
highest, the lowest, or several. Where every head occupies one position there is nothing to
resolve.

With a hosting of the spine, a map `host` from positions to heads saying whose word the material
at each position belongs to, the material at a position `p` is pronounced at the positions
`pron (host p)`. A hosting is a `Morphology.Paradigm` over the positions: the positions with the
same host are pronounced together, the kernel of the map, and each word is a stretch of the spine
when the map is `IsContiguous`.

## Main definitions

* `Spine.occurrences`: the positions a head occupies.
* `Spine.highest`, `Spine.lowest`: the resolutions that pronounce a head at its highest or its
  lowest occurrence.

## Main results

* `Spine.card_occurrences_le_one`: on a spine without repeated heads a head has at most one
  occurrence.
* `Spine.highest_eq_occurrences`, `Spine.lowest_eq_occurrences`: there the two resolutions agree
  with each other and with every resolution that pronounces each head somewhere.

## Implementation notes

A word belongs to a head and not to one of its occurrences: in [harizanov-gribanova-2019] word
formation acts on the syntactic object and Chain Reduction on the positions it occupies. The
hosting is therefore valued in heads, and a word formed at one occurrence of a head is pronounced
wherever the resolution pronounces the head.

A value of the type of heads names one head here: two positions with the same value are
occurrences of that head. A spine on which a category recurs without any head occupying two
positions is the image under `Spine.map` of a spine of this kind.

## TODO

* The resolutions that pronounce a head at several of its occurrences, as in predicate doubling.

## References

* [harizanov-gribanova-2019]
* [nunes-2004]
-/

@[expose] public section

namespace Spine

variable {H : Type*} (s : Spine H)

variable [DecidableEq H] {s} {h : H} {p : s.Position}

variable (s) in
/-- The occurrences of a head are the positions it occupies. -/
def occurrences (h : H) : Finset s.Position := Finset.univ.filter (s.headAt · = h)

@[simp] theorem mem_occurrences : p ∈ s.occurrences h ↔ s.headAt p = h := by simp [occurrences]

theorem occurrences_nonempty_iff : (s.occurrences h).Nonempty ↔ h ∈ s := by
  simp only [Finset.Nonempty, mem_occurrences, headAt, mem_def, List.mem_iff_get]

/-- On a spine without repeated heads, a head has at most one occurrence. -/
theorem card_occurrences_le_one (hs : s.heads.Nodup) (h : H) : (s.occurrences h).card ≤ 1 :=
  Finset.card_le_one.2 fun _ ha _ hb ↦ List.nodup_iff_injective_get.1 hs <|
    (mem_occurrences.1 ha).trans (mem_occurrences.1 hb).symm

variable (s) in
/-- The resolution that pronounces a head at its highest occurrence. -/
def highest (h : H) : Finset s.Position :=
  (s.occurrences h).filter fun p ↦ ∀ q ∈ s.occurrences h, q ≤ p

variable (s) in
/-- The resolution that pronounces a head at its lowest occurrence. -/
def lowest (h : H) : Finset s.Position :=
  (s.occurrences h).filter fun p ↦ ∀ q ∈ s.occurrences h, p ≤ q

theorem highest_subset (h : H) : s.highest h ⊆ s.occurrences h := Finset.filter_subset _ _

theorem lowest_subset (h : H) : s.lowest h ⊆ s.occurrences h := Finset.filter_subset _ _

/-- On a spine without repeated heads the highest occurrence of a head is its only one. -/
theorem highest_eq_occurrences (hs : s.heads.Nodup) (h : H) : s.highest h = s.occurrences h := by
  refine Finset.filter_true_of_mem fun p hp q hq ↦ ?_
  exact (Finset.card_le_one.1 (card_occurrences_le_one hs h) q hq p hp).le

/-- On a spine without repeated heads the lowest occurrence of a head is its only one. -/
theorem lowest_eq_occurrences (hs : s.heads.Nodup) (h : H) : s.lowest h = s.occurrences h := by
  refine Finset.filter_true_of_mem fun p hp q hq ↦ ?_
  exact (Finset.card_le_one.1 (card_occurrences_le_one hs h) p hp q hq).le

end Spine
