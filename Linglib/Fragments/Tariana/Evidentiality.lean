module

public import Linglib.Semantics.Evidential.Defs

/-!
# Tariana evidentiality

Tariana (Arawak, Vaupés) has a five-choice system of Aikhenvald's type D1, fused with tense:
in the recent past, visual *-ka*, non-visual sensory *-mahka*, inferred *-nihka*, assumed
*-sika* and reported *-pidaka*. WALS codes the language as having direct and indirect
evidentials.

## References

* [aikhenvald-2004], §2.4
* [de-haan-2013]
-/

@[expose] public section

namespace Tariana.Evidentiality

open Evidential

/-- The recent-past forms: visual, non-visual, inferred, assumed and reported. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "ka"], covers := {.visual} },
    { morphs := [.suff "mahka"], covers := {.sensory} },
    { morphs := [.suff "nihka"], covers := {.inference} },
    { morphs := [.suff "sika"], covers := {.assumption} },
    { morphs := [.suff "pidaka"], covers := {.hearsay, .quotative} } ]

end Tariana.Evidentiality
