module

public import Linglib.Semantics.Evidential.Defs

/-!
# Lhasa Tibetan evidentiality

Lhasa (Standard Spoken) Tibetan marks evidentiality in its final auxiliaries, fused with tense
and aspect, and the same contrast runs through the copulas and the imperfective, so the forms
are given here in the perfective. Sensory *-song* marks an event the speaker perceived through
any of the senses, and *-bzhag* one inferred from direct knowledge of its result, the only
dedicated inferential in the paradigm. The so-called factual *-pa red* is read three ways:
Tournadre and LaPolla take it to mark factual access, with all report on the suffix *-za*;
DeLancey's later account glosses it indirect, covering hearsay, inference and general
knowledge; and Zeisler, with Garrett, shows it used for generic and shared knowledge, for inferences
and assumptions of high certainty and for unattributable hearsay, with *-za* (the depleted
verb *zer* 'say') reserved for attributable report. Under Aikhenvald's parameters that is
assumption and hearsay for *-pa red* and quotative for *-za*, which the inventory records.
Aikhenvald herself, following DeLancey's earlier description of *-song* against *-pa red*,
reads the perfective as a firsthand ~ non-firsthand system and confines evidentiality proper
to it. The egophoric *-pa yin*, *yin* and *yod*, and *-byung* with the speaker as goal of the
event, mark personal involvement rather than source: for Aikhenvald the copular opposition
*yin* ~ *red*, *yod* ~ *'dug* is an evidentiality strategy, and for Zeisler the egophoric ~
factual contrast is a dimension of speaker stance that the source parameters do not carve.
Neither is in the inventory.

## References

* [aikhenvald-2004], §2.1, §4.6
* [delancey-1986]
* [delancey-2001]
* [tournadre-2008]
* [tournadre-lapolla-2014]
* [zeisler-2024]
-/

@[expose] public section

namespace LhasaTibetan.Evidentiality

open Evidential

/-- The perfective evidentials sensory *-song*, inferential *-bzhag* and factual *-pa red*,
and the quotative *-za*. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "song"], covers := {.visual, .sensory} },
    { morphs := [.suff "bzhag"], covers := {.inference} },
    { morphs := [.suff "pa", .free "red"], covers := {.assumption, .hearsay} },
    { morphs := [.suff "za"], covers := {.quotative} } ]

end LhasaTibetan.Evidentiality
