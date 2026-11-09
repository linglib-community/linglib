module

public import Linglib.Semantics.Evidential.Defs

/-!
# Aymara evidentiality

Aymara (Jaqi) has three evidentials, an areal feature shared with Quechua: personal knowledge,
acquired visually, hearsay (knowledge through language) and non-personal knowledge (inferred).

## References

* [aikhenvald-2004], §2.2
-/

@[expose] public section

namespace Aymara.Evidentiality

open Evidential

/-- The personal knowledge *-wa*, acquired visually. -/
def personal : Evidential := { morphs := [.suff "wa"], covers := {.visual, .sensory} }

/-- The hearsay *-sa*, knowledge through language. -/
def hearsay : Evidential := { morphs := [.suff "sa"], covers := {.hearsay, .quotative} }

/-- The non-personal knowledge *-pacha*, inferred. -/
def nonpersonal : Evidential := { morphs := [.suff "pacha"], covers := {.inference, .assumption} }

/-- The evidentials: personal knowledge, hearsay and non-personal knowledge. -/
def evidentials : List Evidential := [personal, hearsay, nonpersonal]

end Aymara.Evidentiality
