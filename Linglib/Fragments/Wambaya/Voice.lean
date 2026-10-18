module

public import Linglib.Syntax.Voice.Basic

/-!
# Wambaya voice

Wambaya encodes reflexive and reciprocal constructions with the clitic *-ngg-*, in the object
position of the second-position auxiliary, which reduces the clause to an intransitive one.

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
