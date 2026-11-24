module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Uyghur clausal embedding

Uyghur (Turkic, ISO 639-3 `uig`) embeds a clause under a verb in two ways. A participial clause,
`V-PTPL-lik-POSS-CASE`, is a nominalization: its subject is genitive, and it bears possessive
agreement and case. A finite clause is followed by *dep*, the converb in *-(I)p* of *de-* 'say';
the same suffix links any clause to the clause it modifies. Main-verb *de-* takes a finite clause
with no linker, a noun phrase or a participial clause, and cannot go without a complement, where
*warqira-* 'scream' takes none. The light verbs *qil-* 'do, make' and *bol-* 'become' form a
transitive and an unaccusative predicate with the same noun or adjective.

The verbs are recorded with the complements they take as main verbs. *dep* has no entry: whether
it is a complementizer or the converb of the verb is the question of `Studies/Major2024.lean`.
Forms are in the standard Latin orthography, a verb's form is its stem, and `I` is the
harmonizing high vowel of the converb suffix.

## References

* [major-2024]
* [major-2021]
* [sugar-2019]
-/

@[expose] public section

namespace Uyghur

open Morphology (Morph)

/-! ### Clause-linking suffixes -/

/-- *-(I)p* is the converb suffix, borne by the verb of a clause that modifies another clause. -/
def ip : Complementizer where
  morphs := [.suff "(I)p"]
  verbForm := some .Conv

/-- *-lik* is the suffix of a participial clause, between the participle and the possessive
agreement. -/
def lik : Complementizer where
  morphs := [.suff "lik"]
  coding := some .nominalized

/-- A verb that takes a participial clause has this frame, the subject of the clause genitive. -/
def participialFrame : ArgumentFrame := .typedBy lik (some (.overt (some .gen)))

/-! ### Verbs -/

/-- *de-* 'say', which reports an act of speaking or only the source of some content; its
complement is obligatory. -/
def de : Verb where
  morphs := [.root "de"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.np, participialFrame]
  speechActVerb := true

/-- *oyla-* 'think'. -/
def oyla : Verb where
  morphs := [.root "oyla"]
  valency := .ofFrames [ArgumentFrame.np, participialFrame]
  attitude := some (.doxastic .doxastic)

/-- *bil-* 'know'. -/
def bil : Verb where
  morphs := [.root "bil"]
  valency := .ofFrames [ArgumentFrame.np, participialFrame]
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- *unut-* 'forget'. -/
def unut : Verb where
  morphs := [.root "unut"]
  valency := .ofFrames [ArgumentFrame.np, participialFrame]
  factivity := some .full

/-- *éyt-* 'tell'. -/
def eyt : Verb where
  morphs := [.root "éyt"]
  valency := .ofFrames [ArgumentFrame.np, participialFrame]
  voiceType := some .agentive
  speechActVerb := true

/-- *warqira-* 'scream', unergative. -/
def warqira : Verb where
  morphs := [.root "warqira"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .agentive

/-- *ket-* 'leave', unaccusative. -/
def ket : Verb where
  morphs := [.root "ket"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- *ye-* 'eat'. -/
def ye : Verb where
  morphs := [.root "ye"]
  valency := .ofFrame ArgumentFrame.np
  voiceType := some .agentive

/-- The light verb *qil-* 'do, make', transitive: *söz qil-* 'speak', *éniq qil-* 'make
clear'. -/
def qil : Verb where
  morphs := [.root "qil"]
  valency := .ofFrame ArgumentFrame.np
  voiceType := some .agentive

/-- The light verb *bol-* 'become', unaccusative: *söz bol-* 'there be speaking', *éniq bol-*
'become clear'. -/
def bol : Verb where
  morphs := [.root "bol"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- `verbs` lists the verbs recorded here. -/
def verbs : List Verb := [de, oyla, bil, unut, eyt, warqira, ket, ye, qil, bol]

/-- The converb of a verb is its stem under *-(I)p*, as *de-p* 'saying' and *oyla-p* 'thinking'. -/
def converb (v : Verb) : List Morph := v.morphs ++ ip.morphs

end Uyghur
