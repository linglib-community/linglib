module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Indonesian clause embedding

This file enters the complement-taking verbs and the subordinators of Arka's study of
finiteness. *Ingin* 'want', *belajar* 'learn', *menyuruh* 'order' and *mendorong* 'push' take a
bare complement whose subject is controlled, and *tahu* 'know' takes a *bahwa* clause. *Bahwa*
'that' and *agar* 'so that' introduce full clauses with subjects of their own, and *sambil*
'while' a clause whose subject is that of the main clause and is not expressed.

## Implementation notes

*Menyuruh*, *mendorong* and *belajar* are entered with their prefixes, *meN-* on *suruh* and
*dorong* and *ber-* on *ajar*, and `Indonesian.Phonology` gives the sound of each prefix.

## References

* [arka-2013]
* [sneddon-1996]
* [noonan-2007]
-/

@[expose] public section

namespace Indonesian.Complementation

open Morphology

/-- A bare complement whose subject is controlled by a matrix argument. -/
def controlled : ArgumentFrame.Position :=
  .clausal (coding := some .infinitive) (subject := some .null)

/-- The frame of a controlled complement alone. -/
def controlledFrame : ArgumentFrame := { complements := [controlled] }

/-- The frame of an object and a complement it controls. -/
def objectControlledFrame : ArgumentFrame := controlledFrame.withObject

/-- *ingin* 'want' takes a controlled complement, *Mereka ingin datang besok*. -/
def ingin : Verb :=
  { morphs := [.root "ingin"], valency := .ofFrame controlledFrame (controller := some 0) }

/-- *belajar* 'learn, study', *ber-* on *ajar*, takes a controlled complement, *Saya belajar
menembak*. -/
def belajar : Verb :=
  { morphs := [.pref "ber", .root "ajar"],
    valency := .ofFrame controlledFrame (controller := some 0) }

/-- *menyuruh* 'order, ask', *meN-* on *suruh*, takes an object and a complement it controls,
*Saya menyuruh dia makan*. -/
def menyuruh : Verb :=
  { morphs := [.pref "meN", .root "suruh"],
    valency := .ofFrame objectControlledFrame (controller := some 1) }

/-- *mendorong* 'push', *meN-* on *dorong*, takes an object and a resultative complement it
controls, *Orang itu mendorong saya jatuh*. -/
def mendorong : Verb :=
  { morphs := [.pref "meN", .root "dorong"],
    valency := .ofFrame objectControlledFrame (controller := some 1) }

/-- *tahu* 'know' takes a *bahwa* clause, *Saya tahu bahwa mereka akan datang*. -/
def tahu : Verb := { morphs := [.root "tahu"], valency := .ofFrame ArgumentFrame.finiteClause }

/-- *bahwa* 'that' is the declarative complementizer of a full clause. -/
def bahwa : Complementizer where
  morphs := [.free "bahwa"]
  coding := some .indicative
  types := .only .declarative

/-- *agar* 'so that' introduces a purpose clause, which may have a subject of its own. -/
def agar : Complementizer where
  morphs := [.free "agar"]

/-- *sambil* 'while' joins a clause for a second action of the same person: the two clauses
have the same subject, and that of the second is not expressed ([sneddon-1996] p. 338). -/
def sambil : Complementizer where
  morphs := [.free "sambil"]
  subject := some .null

end Indonesian.Complementation
