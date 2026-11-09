module

public import Linglib.Semantics.Evidential.Defs

/-!
# Tariana evidentiality

Tariana (Arawak, Vaupés) has five evidentials fused with tense: in the recent past, visual
*-ka*, non-visual sensory *-mahka*, inferred *-nihka*, assumed *-sika* and reported *-pidaka*.

## TODO

The forms are those of the recent past alone; the evidentials of the other tenses are not
recorded.

## References

* [aikhenvald-2004], §2.4
-/

@[expose] public section

namespace Tariana.Evidentiality

open Evidential

/-- The visual recent past *-ka*. -/
def visual : Evidential := { morphs := [.suff "ka"], covers := {.visual} }

/-- The non-visual recent past *-mahka*. -/
def nonvisual : Evidential := { morphs := [.suff "mahka"], covers := {.sensory} }

/-- The inferred recent past *-nihka*. -/
def inferred : Evidential := { morphs := [.suff "nihka"], covers := {.inference} }

/-- The assumed recent past *-sika*. -/
def assumed : Evidential := { morphs := [.suff "sika"], covers := {.assumption} }

/-- The reported recent past *-pidaka*. -/
def reported : Evidential := { morphs := [.suff "pidaka"], covers := {.hearsay, .quotative} }

/-- The recent-past evidentials: visual, non-visual, inferred, assumed and reported. -/
def evidentials : List Evidential := [visual, nonvisual, inferred, assumed, reported]

end Tariana.Evidentiality
