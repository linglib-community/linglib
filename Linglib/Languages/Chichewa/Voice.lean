module

public import Linglib.Syntax.Voice.Basic

/-!
# Chichewa voice

Chichewa marks its valency-changing voices with verbal extensions, suffixes that follow the root:
the causative *-its-*, the applicative *-ir-*, the reciprocal *-an-* and the passive *-idw-*,
as on *mang-* 'tie', *mang-its-* 'cause to tie', *mang-ir-* 'tie for, with, at', *mang-an-* 'tie
each other' and *mang-idw-* 'be tied'. The applicative introduces a benefactive, an instrument,
a location or a circumstance.

## Main definitions

* `Chichewa.causative`, `applicative`, `reciprocal`, `passive`: the voices.

## References

* [hyman-mchombo-1992]
-/

@[expose] public section

namespace Chichewa

/-- The causative *-its-* makes a causer the A of a transitive construction. -/
def causative : Voice := Voice.causative.marked [.suff "its"]

/-- The applicative *-ir-* adds an applied participant as a second P beside the A and the P. -/
def applicative : Voice := Voice.applicative.marked [.suff "ir"]

/-- The reciprocal *-an-* makes the A and the P the single S of an intransitive construction. -/
def reciprocal : Voice := Voice.reciprocal.marked [.suff "an"]

/-- The passive *-idw-* makes the P the subject and demotes the agent. -/
def passive : Voice := Voice.passive.marked [.suff "idw"]

end Chichewa
