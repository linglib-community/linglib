module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Japanese verbs

The Japanese clause-embedding and departure predicates the studies of Qing and Uegaki and of
Ozaki consume: the preferential attitudes *tanoshimi* 'look forward to', *osore* 'fear', *kitai*
'expect', *nozomu* 'hope' and *shinpai* 'worry', whose distributivity over alternatives follows from
the kind of preference each records, and the departure verbs *hanareru* 'leave' and *deru* 'exit',
which take their source in the accusative or the ablative and are unaccusative, their Voice being
non-thematic. The causative suffix *-(s)ase* is a position of the verb template,
`Japanese.Verb.Exponent.sase`.

## Main definitions

* `Japanese.verbs`: the attitude and departure verbs.

## References

* [ozaki-2026]
* [qing-uegaki-2025]
-/

@[expose] public section

namespace Japanese

open ArgumentStructure

/-! ### Preferential attitudes -/

/-- 楽しみ *tanoshimi* 'look forward to', a positive preference relative to relevance. -/
def tanoshimi : Verb where
  morphs := [.root "tanoshimi"]
  script := some "楽しみ"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive false)

/-- 恐れ *osore* 'fear', a negative preference by comparison of degrees. -/
def osore : Verb where
  morphs := [.root "osore"]
  script := some "恐れ"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)

/-- 期待 *kitai* 'expect, hope', a positive preference by comparison of degrees. -/
def kitai : Verb where
  morphs := [.root "kitai"]
  script := some "期待"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- 望む *nozomu* 'hope', a positive preference by comparison of degrees. -/
def nozomu : Verb where
  morphs := [.root "nozomu"]
  script := some "望む"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- 心配 *shinpai* 'worry', a preference relative to uncertainty. -/
def shinpai : Verb where
  morphs := [.root "shinpai"]
  script := some "心配"
  valency := .ofFrame ArgumentFrame.finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative false)

/-! ### Departure verbs -/

/-- 離れる *hanareru* 'leave' takes the leaver as its theme and the source in the accusative or
ablative, with no thematic Voice. -/
def hanareru : Verb where
  morphs := [.root "hanareru"]
  script := some "離れる"
  valency := .ofFrame ArgumentFrame.np
  voiceType := some .nonThematic
  passivizable := false

/-- 出る *deru* 'exit' takes the leaver as its theme and the source in the accusative or ablative,
with no thematic Voice. -/
def deru : Verb where
  morphs := [.root "deru"]
  script := some "出る"
  valency := .ofFrame ArgumentFrame.np
  voiceType := some .nonThematic
  passivizable := false

/-- The inventory. -/
def verbs : List Verb :=
  [tanoshimi, osore, kitai, nozomu, shinpai, hanareru, deru]

end Japanese
