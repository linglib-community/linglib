module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Swahili verbs

This file defines the Swahili verbs of Palmieri's appendix on lexical reciprocity: ten verbs
in *-an-* with a lexicalized reciprocal entry and the nine binary bases they derive from.
Palmieri diagnoses the reciprocal entries as lexical by singular predication, under a modal
and in the habitual, and by the order of the reciprocal against the applicative and causative
suffixes. Some bases have drifted in meaning, *pambana* 'fight' from *pamba* 'decorate', and
*jibizana* 'discuss' has no binary base at all. The reciprocal marker is in `Reciprocals.lean`,
and Palmieri's pairing of each verb with its base is `Studies/Palmieri2024.lean`.

## Main definitions

* `Swahili.Verbs.achana`, `gawana`, `gombana`, `gongana`, `jibizana`, `pambana`, `patana`,
  `pigana`, `shindana`, `tengana`: the lexical reciprocals
* `Swahili.Verbs.acha`, `gawa`, `gomba`, `gonga`, `pamba`, `pata`, `piga`, `shinda`, `tenga`:
  their binary bases

## References

* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

@[expose] public section

namespace Swahili.Verbs

/-! ### Lexical reciprocal verbs -/

/-- *achana* 'break up, divorce'. -/
def achana : Verb where
  morphs := [.root "achana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *gawana* 'share'. -/
def gawana : Verb where
  morphs := [.root "gawana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *gombana* 'quarrel'. -/
def gombana : Verb where
  morphs := [.root "gombana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *gongana* 'collide'. -/
def gongana : Verb where
  morphs := [.root "gongana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *jibizana* 'discuss, talk, dialogue', which has no binary base. -/
def jibizana : Verb where
  morphs := [.root "jibizana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *pambana* 'fight, be in conflict'. -/
def pambana : Verb where
  morphs := [.root "pambana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *patana* 'agree'. -/
def patana : Verb where
  morphs := [.root "patana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *pigana* 'fight'. -/
def pigana : Verb where
  morphs := [.root "pigana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *shindana* 'compete'. -/
def shindana : Verb where
  morphs := [.root "shindana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *tengana* 'separate, break up'. -/
def tengana : Verb where
  morphs := [.root "tengana"]
  valency := .ofFrame ArgumentFrame.intransitive

/-! ### Binary bases -/

/-- *acha* 'leave, abandon'. -/
def acha : Verb where
  morphs := [.root "acha"]
  valency := .ofFrame ArgumentFrame.np

/-- *gawa* 'distribute'. -/
def gawa : Verb where
  morphs := [.root "gawa"]
  valency := .ofFrame ArgumentFrame.np

/-- *gomba* 'argue with'. -/
def gomba : Verb where
  morphs := [.root "gomba"]
  valency := .ofFrame ArgumentFrame.np

/-- *gonga* 'crash against'. -/
def gonga : Verb where
  morphs := [.root "gonga"]
  valency := .ofFrame ArgumentFrame.np

/-- *pamba* 'decorate'. -/
def pamba : Verb where
  morphs := [.root "pamba"]
  valency := .ofFrame ArgumentFrame.np

/-- *pata* 'find'. -/
def pata : Verb where
  morphs := [.root "pata"]
  valency := .ofFrame ArgumentFrame.np

/-- *piga* 'hit'. -/
def piga : Verb where
  morphs := [.root "piga"]
  valency := .ofFrame ArgumentFrame.np

/-- *shinda* 'defeat'. -/
def shinda : Verb where
  morphs := [.root "shinda"]
  valency := .ofFrame ArgumentFrame.np

/-- *tenga* 'separate, isolate'. -/
def tenga : Verb where
  morphs := [.root "tenga"]
  valency := .ofFrame ArgumentFrame.np

end Swahili.Verbs
