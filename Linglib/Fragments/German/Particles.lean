module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# German modal particles

This file defines the German modal particles *ja*, *denn*, *wohl*, *halt* and *doch* and the
combination *doch wohl* as `Particle` entries, each with the sentence types of a main clause in
which Durrell describes it. A modal particle stands in the middle of the clause and adds the
speaker's attitude to what is said. *Ja* appeals for agreement in statements, expresses surprise
in exclamations and intensifies a command, often as a warning and especially when stressed.
*Denn* is used in questions only, polar and constituent questions alike. *Wohl* signals
probability in statements and uncertainty in questions. *Halt* occurs in statements and
commands. *Doch* marks disagreement in statements, urgency in commands, a request for
confirmation in constituent questions and surprise in exclamations; unstressed, it can turn a
statement into a question expecting the answer yes, and with *wohl* it hopes that something is
the case. A sentence type the grammar says nothing about is left unrecorded.

The polarity particles *ja*, *nein* and *doch*, answering and responding, are
`German.PolarityParticles`; the response *doch* is also used as a separate utterance before a
Verum focus correction (`TurcoBraunDimroth2014`). The analyses of the modal particles are with
the studies of them: Gutzmann's typing of *ja*, *denn* and *wohl* with his own examples,
Theiler's *denn*, Seeliger and Repp's *doch wohl*.

## References

* [durrell-2011]
* [gutzmann-2015]
* [theiler-2021]
* [seeliger-repp-2018]
-/

@[expose] public section

namespace German.Particles

open Clause (EmbeddingContext)

/-- `inMatrix yes no` records a particle as optional in the main-clause sentence types `yes` and
excluded from those in `no`, and records nothing else. -/
def inMatrix (yes no : List Clause.SentenceType) : Clause.Distribution
  | c, .matrix => if c ∈ yes then some .optional else if c ∈ no then some .excluded else none
  | _, _ => none

/-- *Ja* appeals for agreement in statements, expresses surprise in exclamations and intensifies
a command. -/
def ja : Particle where
  form := "ja"
  position := some .clauseMedial
  distribution := inMatrix [.declarative, .exclamative, .imperative] []

/-- *Denn* is used in questions only, polar and constituent. -/
def denn : Particle where
  form := "denn"
  position := some .clauseMedial
  distribution := inMatrix [.polar, .constituent] [.declarative, .imperative, .exclamative]

/-- *Wohl* signals probability in statements and uncertainty in questions. -/
def wohl : Particle where
  form := "wohl"
  position := some .clauseMedial
  distribution := inMatrix [.declarative, .polar, .constituent] []

/-- *Halt* occurs in statements and commands. -/
def halt : Particle where
  form := "halt"
  position := some .clauseMedial
  distribution := inMatrix [.declarative, .imperative] []

/-- *Doch* occurs in statements, commands, constituent questions and exclamations. -/
def doch : Particle where
  form := "doch"
  position := some .clauseMedial
  distribution := inMatrix [.declarative, .imperative, .constituent, .exclamative] []

/-- *Doch wohl*, also *wohl doch*, occurs in statements and hopes that something is the case. -/
def dochWohl : Particle where
  form := "doch wohl"
  position := some .clauseMedial
  distribution := inMatrix [.declarative] []

/-- The modal particles. -/
def modalParticles : List Particle := [ja, denn, wohl, halt, doch]

end German.Particles

namespace German.PolarityParticles

/-- *ja* 'yes'. -/
def ja : Particle where
  form := "ja"

/-- *nein* 'no'. -/
def nein : Particle where
  form := "nein"

/-- *doch* 'yes', contradicting a negative: *Kommt er nicht?* — *Doch*, he is coming. -/
def doch : Particle where
  form := "doch"

/-- The polarity particles. -/
def all : List Particle := [ja, nein, doch]

end German.PolarityParticles
