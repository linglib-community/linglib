module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Swedish particles

The modal particle *väl* and the polarity particles *ja*, *nej* and *jo*.

*Väl* is a clause-medial modal particle of declaratives: the speaker suspects but is not
certain that the proposition is true and expects the addressee to take a stance on it, so that
a declarative with *väl* is a question rather than an assertion ([seeliger-repp-2018]). Unlike
German *wohl* it lacks a reportative meaning. Its role in rejecting questions, with low negation
and with *men* 'but', is analysed in `SeeligerRepp2018`. Swedish also has clause-initial *visst*
and *nog*, which can mark positive rejecting questions and are not formalized here.

The polarity particles are `Swedish.PolarityParticles`: *ja* 'yes', *nej* 'no', and *jo*,
glossed yes.REV, the polarity-reversing affirmative that confirms the positive alternative of a
negative question ([holmberg-2016]).

## References

* [seeliger-repp-2018]
* [holmberg-2016]
-/

@[expose] public section

namespace Swedish.Particles

/-! ### Modal particles -/

/-- *väl* — clause-medial modal particle (after the finite verb) of matrix declaratives. That a
declarative with *väl* is a question and not an assertion is a matter of speech act, not of
clause type, analysed in `SeeligerRepp2018`. -/
def val : Particle where
  form := "väl"
  position := some .clauseMedial
  distribution := fun c e ↦ match c, e with
    | .declarative, .matrix => some .optional
    | _, _ => none

end Swedish.Particles

namespace Swedish.PolarityParticles

/-- *ja* 'yes': *Vill han ha kaffe?* 'Does he want coffee?' — *Ja*. -/
def ja : Particle where
  form := "ja"

/-- *nej* 'no': *Har Johan inte kommit?* 'Has Johan not arrived?' — *Nej*, he has not. -/
def nej : Particle where
  form := "nej"

/-- *jo* 'yes.REV', contradicting a negative: *Har Johan inte kommit?* — *Jo*, he has. -/
def jo : Particle where
  form := "jo"

/-- The polarity particles. -/
def all : List Particle := [ja, nej, jo]

end Swedish.PolarityParticles
