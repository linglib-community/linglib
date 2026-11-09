module

public import Linglib.Semantics.Evidential.Defs

/-!
# Tuyuca evidentiality

Tuyuca (East Tucanoan, Vaupés) has five evidentials, the most frequently cited system of five:
visual *-wi*, non-visual sensory *-ti*, apparent (inferred) *-yi*, secondhand (reported) *-yigi*
and assumed *-hiyi*, obligatory verbal suffixes, classically described by Barnes.

## References

* [aikhenvald-2004], §2.4
* [barnes-1984]
-/

@[expose] public section

namespace Tuyuca.Evidentiality

open Evidential

/-- The visual *-wi*. -/
def visual : Evidential := { morphs := [.suff "wi"], covers := {.visual} }

/-- The non-visual sensory *-ti*. -/
def nonvisual : Evidential := { morphs := [.suff "ti"], covers := {.sensory} }

/-- The apparent *-yi*, for what is inferred. -/
def apparent : Evidential := { morphs := [.suff "yi"], covers := {.inference} }

/-- The secondhand *-yigi*, for what is reported. -/
def secondhand : Evidential := { morphs := [.suff "yigi"], covers := {.hearsay, .quotative} }

/-- The assumed *-hiyi*. -/
def assumed : Evidential := { morphs := [.suff "hiyi"], covers := {.assumption} }

/-- The evidentials, in the order visual, non-visual, apparent, secondhand and assumed. -/
def evidentials : List Evidential := [visual, nonvisual, apparent, secondhand, assumed]

end Tuyuca.Evidentiality
