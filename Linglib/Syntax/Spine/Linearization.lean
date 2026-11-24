/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Occurrence
public import Linglib.Syntax.WordOrder

/-!
# The order of the positions of a spine

A spine lists its heads from the bottom up, and a head direction turns that into an order of
pronunciation. With head-final order each head follows its complement, so the positions stand
from the bottom up; with head-initial order each head precedes its complement, so they stand from
the top down. We define this harmonic arrangement of the positions as a `WordOrder.Arrangement`.
It orders positions and says nothing about which occurrence of a head is pronounced, which is
the subject of `Syntax/Spine/Occurrence.lean`.

## Main definitions

* `Spine.arrangement`: the harmonic arrangement of the positions of a spine in a head direction.

## Main results

* `Spine.arrangement_headDirection`: a position stands in the chosen direction from every
  position below it.
* `Spine.arrangement_mirror`: the two head directions give mirror-image arrangements.

## TODO

* The order of the words with the phrases attached along the spine. On the rule of Brody and of
  Svenonius a phrase attached at or above the position where a word is pronounced precedes the
  word and a phrase attached below it follows, so that the finite verb precedes a phrase exactly
  when it is pronounced above the height at which the phrase attaches.
* The order of the verbs of a periphrastic form, which English and German reverse relative to
  each other on the same `Tense.Form`.

## References

* [brody-2000]
* [svenonius-2016]
-/

@[expose] public section

open WordOrder

namespace Spine

variable {H : Type*} (s : Spine H)

/-- The harmonic arrangement of the positions of a spine: with head-final order the positions
stand from the bottom up, each head after its complement, and with head-initial order from the
top down. -/
def arrangement : HeadDirection → Arrangement s.Position s.heads.length
  | .headFinal => Equiv.refl _
  | .headInitial => Fin.revPerm

variable {s} {p q : s.Position} {d : HeadDirection}

theorem arrangement_precedes_iff :
    (s.arrangement d).Precedes p q ↔ d.Orders q p := by
  cases d <;> simp [arrangement, Arrangement.Precedes, Fin.rev_lt_rev]

/-- A position stands in the chosen direction from every position below it. -/
theorem arrangement_headDirection (h : q < p) : (s.arrangement d).headDirection p q = d := by
  cases d <;> simp [arrangement_precedes_iff, h, h.not_gt]

theorem arrangement_mirror : (s.arrangement d).mirror = s.arrangement d.swap := by
  cases d <;> ext p <;> simp [arrangement, Arrangement.mirror]

end Spine
