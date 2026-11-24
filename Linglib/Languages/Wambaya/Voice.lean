module

public import Linglib.Syntax.Voice.Basic

/-!
# Wambaya voice

Wambaya encodes reflexive and reciprocal constructions with the clitic *-ngg-*, in the object
position of the second-position auxiliary. It reduces the valency of the verb by one: a
transitive verb becomes intransitive, its subject nominative rather than ergative, while a
ditransitive keeps its theme as an accusative object (Nordlinger's grammar, §7.3.1).

## Main definitions

* `Wambaya.reflexive`: the reflexive voice.

## References

* [evans-et-al-2007]
* [nordlinger-1998]
-/

@[expose] public section

namespace Wambaya

/-- The reflexive *-ngg-* cumulates the A and the P in one S. -/
def reflexive : Voice := Voice.reflexive.marked [.suff "ngg"]

end Wambaya
