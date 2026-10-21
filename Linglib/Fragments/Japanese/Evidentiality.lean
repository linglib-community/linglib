module

public import Linglib.Semantics.Evidential.Defs

/-!
# Japanese evidentiality

Japanese has grammaticalized markers of information source that are frequent but optional,
since there is no neutral evidential: the reportatives *sō* and *rashi-* and the inferentials
*-sō*, *rashi-*, *ppo-*, *yō* and *mitai*, *rashi-* serving both ways. The inferentials rest on
evidence, typically visual appearance, for a state of affairs the speaker has no direct access
to. The quotative particles *to* and *tte* embed whole utterances and are kept apart from the
evidentials, and whether *yō* and *mitai* also have direct evidential uses is open, so the
inventory records neither.

Aikhenvald, after Aoki, counts these as optional devices rather than a unitary grammatical
category of evidentiality, allowing at most that the reported form makes an A3 system of its
own. WALS codes the language as having indirect evidentials only.

## Implementation notes

Forms are in the Hepburn romanization, and a form that inflects is cited in its non-past.

## References

* [narrog-yang-2018]
* [aikhenvald-2004], §3.3
* [de-haan-2013]
-/

@[expose] public section

namespace Japanese.Evidentiality

open Evidential

/-! ### Reportatives -/

/-- The particle *sō*, followed by the copula *da*, the reportative closest to pure reporting. -/
def soo : Evidential := { morphs := [.encl "sō"], covers := {.hearsay, .quotative} }

/-- The particle adjective *rashi-*, an inferential that marks the speaker's distance from the
judgement and a reportative filtered through the speaker's own reasoning. -/
def rashii : Evidential :=
  { morphs := [.encl "rashii"], covers := {.inference, .hearsay, .quotative} }

/-! ### Inferentials -/

/-- The suffix *-sō*, followed by the copula *da*, apparent imminence: a state of affairs
that appearance shows is about to be realized. -/
def sooSuffix : Evidential := { morphs := [.suff "sō"], covers := {.inference} }

/-- *yō*, followed by the copula *da*, the general inferential, for the speaker's own judgement
or evidence immediately available. -/
def yoo : Evidential := { morphs := [.encl "yō"], covers := {.inference} }

/-- *mitai*, the colloquial counterpart of *yō*. -/
def mitai : Evidential := { morphs := [.encl "mitai"], covers := {.inference} }

/-- The particle adjective *ppo-*, a recent slang inferential with an evaluative connotation. -/
def ppoi : Evidential := { morphs := [.encl "ppoi"], covers := {.inference} }

/-- The evidentials. -/
def evidentials : List Evidential := [soo, rashii, sooSuffix, yoo, mitai, ppoi]

end Japanese.Evidentiality
