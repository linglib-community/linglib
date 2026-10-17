module

public import Linglib.Semantics.Evidential.Defs

/-!
# West Greenlandic evidentiality

West Greenlandic codes information source in scattered fashion: evidential meanings are carried
by derivational suffixes that stand in opposition to suffixes unrelated to information source,
by an enclitic and by a particle, and they form no single paradigm. Aikhenvald, after Fortescue,
counts three synonymous reported evidentials, the sentential suffix *-nirar-*, the enclitic
*-guuq* and the particle *unnia*, which the inventory records. WALS codes the language as having
indirect evidentials only.

## TODO

The sentential suffixes *-gunar-* 'it seems that' and *-sima-* 'apparently', and the
non-sentential suffixes for what one can hear and what something looks or sounds like, await
Fortescue's description of which sources each covers.

## References

* [aikhenvald-2004]
* [fortescue-2003]
* [de-haan-2013]
-/

@[expose] public section

namespace WestGreenlandic.Evidentiality

open Evidential

/-- The sentential suffix *-nirar-* 'say that someone or something verbs', the one reported
evidential without an epistemic overtone. -/
def nirar : Evidential := { morphs := [.suff "nirar"], covers := {.hearsay, .quotative} }

/-- The enclitic *-guuq*, whose reports suggest displaced responsibility rather than doubt. -/
def guuq : Evidential := { morphs := [.encl "guuq"], covers := {.hearsay, .quotative} }

/-- The particle *unnia*, from the verb stem *unnir-* 'say (that)', with a gossipy and mirative
flavour. -/
def unnia : Evidential := { morphs := [.free "unnia"], covers := {.hearsay, .quotative} }

/-- The reported evidentials. -/
def evidentials : List Evidential := [nirar, guuq, unnia]

end WestGreenlandic.Evidentiality
