module

public import Linglib.Syntax.Voice.Basic

/-!
# Finnish voice

Each Finnish verb has an active and an impersonal form, as *avat-a* 'open' has *avaa* 'opens'
and *avat-a-an* 'one opens, it is opened'. The impersonal form, traditionally the passive and
the fourth person of Karlsson's grammar, says that an unspecified human agent performs the
action, has no subject expressed as an independent phrase, and admits no correspondent to an
Indo-European *by*-agent; it is the impersonal passive of the typology. It is marked by the
suffix *-tA-* and its variants with the personal ending *-Vn* (§21.1).

## Main definitions

* `Finnish.impersonalPassive`: the impersonal passive with its marking.
* `Finnish.voices`: the active and the impersonal passive.

## Implementation notes

The inventory lists the voices projecting transitive clauses.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish

/-- The impersonal passive, the fourth person, is the passive marker *-ttA*, *-tA*, *-dA* or
*-A* with the personal ending *-Vn*. -/
def impersonalPassive : Voice := Voice.impersonalPassive.marked [.suff "tA", .suff "Vn"]

/-- The active and the impersonal passive. -/
def voices : Finset Voice := {.active, impersonalPassive}

end Finnish
