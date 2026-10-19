module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Portuguese verbs

This file defines two groups of Portuguese verbs. The first are the attitude and causative
verbs of Grano's survey of mood choice with the mood of the finite complement each selects:
*querer* 'want' and *pretender* 'intend' take a *que*-clause in the subjunctive and reject the
indicative, *esperar* 'hope' takes either mood, and the causative *fazer* 'make' takes an
infinitive and, as *fazer com que*, a finite clause in the subjunctive alone; *querer* and
*pretender* also take an infinitive under subject control and *fazer* one under object control.
The second are the transitive verbs of Brazilian Portuguese that Palmieri lists as lexical
reciprocals, *abraçar* 'hug', *beijar* 'kiss', *casar* 'marry', *consultar* 'consult',
*cumprimentar* 'greet', *encontrar* 'meet' and *namorar* 'date', whose reciprocal reading
survives without the clitic *se* in finite clauses and analytic causatives; they are ordinary
transitive entries here, and `Portuguese.Reciprocals` lists them.

## Main definitions

* `Portuguese.Verbs.querer`, `Portuguese.Verbs.esperar`, `Portuguese.Verbs.pretender`,
  `Portuguese.Verbs.fazer`: the mood-selecting verbs.
* `Portuguese.Verbs.abracar` and its siblings: the lexical reciprocals.

## References

* [grano-2024]
* [palmieri-2024]
-/

@[expose] public section

namespace Portuguese.Verbs

open ArgumentStructure

/-! ### Mood choice -/

/-- *querer* 'want' takes a *que*-clause in the subjunctive and an infinitive under subject
control. -/
def querer : Verb where
  morphs := [.root "querer"]
  valency := .of [(ArgumentFrame.subjunctiveClause, [0, 1]), (ArgumentFrame.infinitival, [0, 1])]
    (controllers := [none, some 0])

/-- *esperar* 'hope' takes a *que*-clause in the subjunctive or in the indicative. -/
def esperar : Verb where
  morphs := [.root "esperar"]
  valency := .of [(ArgumentFrame.subjunctiveClause, [0, 1]), (ArgumentFrame.finiteClause, [0, 1])]

/-- *pretender* 'intend' takes an infinitive under subject control and a *que*-clause in the
subjunctive. -/
def pretender : Verb where
  morphs := [.root "pretender"]
  valency := .of [(ArgumentFrame.infinitival, [0, 1]), (ArgumentFrame.subjunctiveClause, [0, 1])]
    (controllers := [some 0])

/-- The causative *fazer* 'make' takes an infinitive under object control and, as *fazer com
que*, a finite clause in the subjunctive. -/
def fazer : Verb where
  morphs := [.root "fazer"]
  valency := .of
    [(ArgumentFrame.infinitival.withObject, [0, 2, 1]), (ArgumentFrame.subjunctiveClause, [0, 1])]
    (controllers := [some 2])

/-! ### Lexical reciprocals -/

/-- *abraçar* 'hug'. -/
def abracar : Verb where
  morphs := [.root "abraçar"]
  valency := .ofFrame ArgumentFrame.np

/-- *beijar* 'kiss'. -/
def beijar : Verb where
  morphs := [.root "beijar"]
  valency := .ofFrame ArgumentFrame.np

/-- *casar* 'marry'. -/
def casar : Verb where
  morphs := [.root "casar"]
  valency := .ofFrame ArgumentFrame.np

/-- *consultar* 'consult, confer'. -/
def consultar : Verb where
  morphs := [.root "consultar"]
  valency := .ofFrame ArgumentFrame.np

/-- *cumprimentar* 'greet'. -/
def cumprimentar : Verb where
  morphs := [.root "cumprimentar"]
  valency := .ofFrame ArgumentFrame.np

/-- *encontrar* 'meet'. -/
def encontrar : Verb where
  morphs := [.root "encontrar"]
  valency := .ofFrame ArgumentFrame.np

/-- *namorar* 'date, be partners'. -/
def namorar : Verb where
  morphs := [.root "namorar"]
  valency := .ofFrame ArgumentFrame.np

end Portuguese.Verbs
