module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Modern Greek complementizers

The four Modern Greek complementizers: indicative *oti*, factive *pu*, interrogative *an* and
subjunctive *na*. The matrix verbs that select them are in `Verbs.lean`. Angelopoulos's
light-noun selection, content and situation sorts, selection classes and stativity
generalizations are projections over these entries in `Studies/Angelopoulos2026.lean`.

## References

* [christidis-1982]
* [roussou-2010]
* [roussou-2019]
* [angelopoulos-2026]
* [grano-2024]
-/

@[expose] public section

namespace Greek.StandardModern.Complementizers

/-- *oti*, the indicative declarative complementizer ([christidis-1982], [roussou-2010]), is
selected by verbs of saying, belief and knowledge. The factivity of an *oti*-clause tracks the
matrix verb (*kséro* against *léo*), so the entry is not lexically factive. -/
def oti : Complementizer where
  morphs := [.free "oti"]
  coding := some .indicative
  types := .only .declarative

/-- *pu*, the factive complementizer ([christidis-1982], [roussou-2019]), is selected by
emotive factives and, on direct-perception readings, by perception and memory verbs
([angelopoulos-2026] fn. 16). It is also adverbial, relative and interrogative *where*, uses
[angelopoulos-2026] unifies through a PLACE noun; the entry records the complement use. -/
def pu : Complementizer where
  morphs := [.free "pu"]
  coding := some .indicative
  types := .only .declarative
  factive := true

/-- *an* 'if', the interrogative complementizer ([roussou-2010]), types embedded polar
questions over indicative clauses, selected (*anarotjéme* 'wonder') or, under matrix negation
or a question, unselected (*dhen kséro an* 'I don't know if'). -/
def an : Complementizer where
  morphs := [.free "an"]
  coding := some .indicative
  types := .only .polar

/-- *na*, the subjunctive marker ([grano-2024]), is selected by volitional, intention and
causative verbs. Whether it heads C or a Mood projection is debated; the entry is
head-agnostic, and [angelopoulos-2026] sets *na* aside. -/
def na : Complementizer where
  morphs := [.free "na"]
  coding := some .subjunctive

/-- The complementizer inventory. -/
def complementizers : List Complementizer := [oti, pu, an, na]

end Greek.StandardModern.Complementizers
