module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Indonesian clause embedding
[arka-2013] [sneddon-1996] [noonan-2007]

The complement-taking verbs and subordinators of [arka-2013]'s finiteness paradigm. *ingin*
'want', *belajar* 'learn', *menyuruh* 'order', and *mendorong* 'push' take bare complements
whose subject is controlled, coded as reduced in [noonan-2007]'s terms; *tahu* 'know' takes a
*bahwa* clause. *bahwa* 'that' and *agar* 'so that' type full clauses with their own subjects.
-/

@[expose] public section

namespace Indonesian.Complementation

open Morphology

/-- A bare complement whose subject is controlled by a matrix argument. -/
def controlled : ArgumentFrame.Position :=
  .clausal (coding := some .infinitive) (embeddedSubject := some .obligatorilyNull)

/-- The frame of a controlled complement alone. -/
def controlledFrame : ArgumentFrame := { complements := [controlled] }

/-- The frame of an object and a complement it controls. -/
def objectControlledFrame : ArgumentFrame := controlledFrame.withObject

/-- *ingin* 'want' takes a controlled complement, *Mereka ingin datang besok*. -/
def ingin : Verb :=
  { morphs := [.root "ingin"], valency := .ofFrame controlledFrame (controller := some 0) }

/-- *belajar* 'learn, study' takes a controlled complement, *Saya belajar menembak*. -/
def belajar : Verb :=
  { morphs := [.root "belajar"], valency := .ofFrame controlledFrame (controller := some 0) }

/-- *menyuruh* 'order, ask' takes an object and a complement it controls, *Saya menyuruh dia
makan*. -/
def menyuruh : Verb :=
  { morphs := [.root "menyuruh"],
    valency := .ofFrame objectControlledFrame (controller := some 1) }

/-- *mendorong* 'push' takes an object and a resultative complement it controls, *Orang itu
mendorong saya jatuh*. -/
def mendorong : Verb :=
  { morphs := [.root "mendorong"],
    valency := .ofFrame objectControlledFrame (controller := some 1) }

/-- *tahu* 'know' takes a finite *bahwa* clause, *Saya tahu bahwa mereka akan datang*. -/
def tahu : Verb := { morphs := [.root "tahu"], valency := .ofFrame ArgumentFrame.finiteClause }

/-- *bahwa* 'that' is the declarative complementizer of a full clause. -/
def bahwa : Complementizer where
  morphs := [.free "bahwa"]
  coding := some .indicative
  types := .only .declarative

/-- *agar* 'so that' is the purposive subordinator of a full, irrealis clause. -/
def agar : Complementizer where
  morphs := [.free "agar"]
  coding := some .subjunctive

end Indonesian.Complementation
