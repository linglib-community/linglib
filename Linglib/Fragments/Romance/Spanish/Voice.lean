module

public import Linglib.Syntax.Voice.Basic

/-!
# Spanish voices

The anticausative of most Spanish verbs of change of state takes the reflexive clitic *se*,
enclitic on the infinitive, as *romperse* 'break' beside transitive *romper*; a few verbs form it
bare, as *mejorar* 'improve'. The verbs record the form of each diathesis
(`Fragments/Romance/Spanish/Verbs.lean`), so a verb whose form marks the anticausative is one
of which `Verb.Marks` holds.

## References

* [koontz-garboden-2009]
* [munoz-perez-2026]
-/

@[expose] public section

namespace Spanish

/-- The anticausative, marked by the clitic *se*. -/
def anticausative : Voice := Voice.anticausative.marked [.encl "se"]

end Spanish
