module

public import Linglib.Semantics.Evidential.Defs

/-!
# Quechua (Cuzco) evidentiality

Cuzco Quechua has three evidentials, the canonical Andean system: direct *-mi*, reportative *-si*
and conjectural *-chá*, second-position enclitics on finite clauses.

## References

* [aikhenvald-2004], §2.2
-/

@[expose] public section

namespace Quechua.Evidentiality

open Evidential

/-- The direct *-mi*. -/
def direct : Evidential := { morphs := [.encl "mi"], covers := {.visual, .sensory} }

/-- The reportative *-si*. -/
def reportative : Evidential := { morphs := [.encl "si"], covers := {.hearsay, .quotative} }

/-- The conjectural *-chá*. -/
def conjectural : Evidential := { morphs := [.encl "chá"], covers := {.inference, .assumption} }

/-- The evidentials: direct, reportative and conjectural. -/
def evidentials : List Evidential := [direct, reportative, conjectural]

end Quechua.Evidentiality
