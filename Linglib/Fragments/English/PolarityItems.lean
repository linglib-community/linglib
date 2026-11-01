module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# English polarity items

This file defines the English polarity-sensitive items as `PolarityItem` entries. The weak
negative polarity items *any*, *ever*, *yet*, *anymore*, *at all*, *in the least*, *a single*
and *whatsoever* are licensed by any downward-entailing operator; the strong ones, *lift a
finger*, *budge an inch*, *in years*, *until* and additive *either*, need an anti-additive
licenser, and Gajewski shows that *either* is out under *only* although *only* is Strawson
anti-additive. *Any* and the free relatives *whatever*, *whoever* and *whichever* have free choice
readings. The positive polarity items are blocked by clausal negation: *someone* also by the other
anti-additive operators but not by *at most five* (Szabolcsi), and *already*, *too* (the
positive counterpart of *either*), *somewhat*, *rather*, *tons of* and *awfully* at least by
clausal negation. The idioms *wild horses*, *all the tea in China*, *a ten-foot pole* and *in a
million years* are Israel's maximizer negative polarity items and *at the drop of a hat*, *in a
jiffy*, *for a pittance* and *for a song* his minimizer positive ones; his classification of the
items by force, quantity and propositional role is the matter of `Studies/Israel2001.lean`. The
entries are tested against cited judgments in the studies of the papers that report them: *any*
and *ever* in `Studies/Chierchia2013.lean` and `Studies/KadmonLandman1993.lean`, and *someone* in
`Studies/Szabolcsi2004.lean`.

## Main definitions

* `English.PolarityItems.weakNPIs`, `English.PolarityItems.strongNPIs`,
  `English.PolarityItems.invertedNPIs`, `English.PolarityItems.allFCIs`,
  `English.PolarityItems.canonicalPPIs`, `English.PolarityItems.invertedPPIs`: the classes.
* `English.PolarityItems.allPolarityItems`: the lexicon.

## Implementation notes

A positive polarity item whose class van der Wouden does not settle carries the weakest
anti-licensor, anti-morphic strength, which every positive polarity item has by his (169).

## References

* [israel-2011]
* [gajewski-2011]
* [chierchia-2006]
* [rullmann-2003]
* [ladd-1981]
* [szabolcsi-2004]
* [vanderwouden-1997]
-/

@[expose] public section

namespace English.PolarityItems

open PolarityItem

/-! ### Weak NPIs -/

/-- *any*, the prototypical negative polarity and free choice item ([chierchia-2006]). -/
def any : PolarityItem :=
  { form := "any"
  , licensor := some .weak
  , freeChoice := true }

/-- *ever*, a temporal negative polarity item. -/
def ever : PolarityItem :=
  { form := "ever"
  , licensor := some .weak }

/-- *yet*, a temporal negative polarity item. -/
def yet : PolarityItem :=
  { form := "yet"
  , licensor := some .weak }

/-- *anymore*, a temporal negative polarity item. -/
def anymore : PolarityItem :=
  { form := "anymore"
  , licensor := some .weak }

/-- *at all*, a degree negative polarity item. -/
def atAll : PolarityItem :=
  { form := "at all"
  , licensor := some .weak }

/-- *in the least*, a degree negative polarity item. -/
def inTheLeast : PolarityItem :=
  { form := "in the least"
  , licensor := some .weak }

/-- *a single*, an emphatic existential negative polarity item. -/
def aSingle : PolarityItem :=
  { form := "a single"
  , licensor := some .weak }

/-- *whatsoever*, an emphatic post-nominal negative polarity item. -/
def whatsoever : PolarityItem :=
  { form := "whatsoever"
  , licensor := some .weak }

/-! ### Strong NPIs -/

/-- *lift a finger*, an idiomatic minimizer needing an anti-additive licenser. -/
def liftAFinger : PolarityItem :=
  { form := "lift a finger"
  , licensor := some .antiAdditive }

/-- *budge an inch*, an idiomatic minimizer needing an anti-additive licenser. -/
def budgeAnInch : PolarityItem :=
  { form := "budge an inch"
  , licensor := some .antiAdditive }

/-- *in years*, a temporal strong negative polarity item. -/
def inYears : PolarityItem :=
  { form := "in years"
  , licensor := some .antiAdditive }

/-- *until*, a temporal strong negative polarity item in its punctual use. -/
def until_ : PolarityItem :=
  { form := "until"
  , licensor := some .antiAdditive }

/-- Additive *either* ([rullmann-2003], [gajewski-2011]), out under the Strawson anti-additive
*only*: *\*Only John likes pancakes, either* ([gajewski-2011] p. 120). -/
def either : PolarityItem :=
  { form := "either"
  , licensor := some .antiAdditive }

/-! ### Free choice items -/

/-- *whatever*, a free-relative free choice item. -/
def whatever : PolarityItem :=
  { form := "whatever"
  , freeChoice := true }

/-- *whoever*, a free-relative free choice item. -/
def whoever : PolarityItem :=
  { form := "whoever"
  , freeChoice := true }

/-- *whichever*, a free-relative free choice item. -/
def whichever : PolarityItem :=
  { form := "whichever"
  , freeChoice := true }

/-! ### Positive polarity items -/

/-- *someone*, a positive polarity item out in the immediate scope of a clausemate anti-additive
operator, *\*John didn't call someone*, *\*No one called someone*, *\*John came to the party
without someone*, and fine below *at most five*, *At most five boys called someone*
([szabolcsi-2004] (10)–(13); [vanderwouden-1997]). -/
def someone : PolarityItem :=
  { form := "someone"
  , antiLicensor := some .antiAdditive }

/-- *already*, a temporal positive polarity item. -/
def already : PolarityItem :=
  { form := "already"
  , antiLicensor := some .antiMorphic }

/-- *too*, an additive positive polarity item, the positive counterpart of *either*
([ladd-1981]). -/
def too : PolarityItem :=
  { form := "too"
  , antiLicensor := some .antiMorphic }

/-- *somewhat*, a degree positive polarity item. -/
def somewhat : PolarityItem :=
  { form := "somewhat"
  , antiLicensor := some .antiMorphic }

/-- *rather*, a degree positive polarity item. -/
def rather : PolarityItem :=
  { form := "rather"
  , antiLicensor := some .antiMorphic }

/-- *tons of*, an emphatic positive polarity item, as in *She has tons of friends.* -/
def tonsOf : PolarityItem :=
  { form := "tons of"
  , antiLicensor := some .antiMorphic }

/-- *awfully*, an emphatic positive polarity item, as in *I was awfully depressed.* -/
def awfully : PolarityItem :=
  { form := "awfully"
  , antiLicensor := some .antiMorphic }

/-! ### Maximizer NPIs -/

/-- *wild horses*, an idiomatic maximizer negative polarity item, as in *Wild horses couldn't
keep me away.* -/
def wildHorses : PolarityItem :=
  { form := "wild horses"
  , licensor := some .weak }

/-- *all the tea in China*, an idiomatic maximizer negative polarity item, as in *I wouldn't do
it for all the tea in China.* -/
def allTheTeaInChina : PolarityItem :=
  { form := "all the tea in China"
  , licensor := some .weak }

/-- *a ten-foot pole*, an idiomatic maximizer negative polarity item, as in *I wouldn't touch it
with a ten-foot pole.* -/
def aTenFootPole : PolarityItem :=
  { form := "a ten-foot pole"
  , licensor := some .weak }

/-- *in a million years*, an idiomatic maximizer negative polarity item, as in *I wouldn't marry
that woman in a million years.* -/
def inAMillionYears : PolarityItem :=
  { form := "in a million years"
  , licensor := some .weak }

/-! ### Minimizer PPIs -/

/-- *at the drop of a hat*, an idiomatic minimizer positive polarity item, as in *He'd quit at the
drop of a hat.* -/
def atTheDropOfAHat : PolarityItem :=
  { form := "at the drop of a hat"
  , antiLicensor := some .antiMorphic }

/-- *in a jiffy*, an idiomatic minimizer positive polarity item, as in *We'll be back in a
jiffy.* -/
def inAJiffy : PolarityItem :=
  { form := "in a jiffy"
  , antiLicensor := some .antiMorphic }

/-- *for a pittance*, an idiomatic minimizer positive polarity item, as in *He got Madonna to
play for peanuts.* -/
def forAPittance : PolarityItem :=
  { form := "for a pittance"
  , antiLicensor := some .antiMorphic }

/-- *for a song*, an idiomatic minimizer positive polarity item, as in *He bought that painting
for a song.* -/
def forASong : PolarityItem :=
  { form := "for a song"
  , antiLicensor := some .antiMorphic }

/-! ### Lexicon access -/

/-- The weak NPIs. -/
def weakNPIs : List PolarityItem :=
  [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever]

/-- The strong NPIs. -/
def strongNPIs : List PolarityItem :=
  [liftAFinger, budgeAnInch, inYears, until_, either]

/-- The maximizer NPIs. -/
def invertedNPIs : List PolarityItem :=
  [wildHorses, allTheTeaInChina, aTenFootPole, inAMillionYears]

/-- All NPIs (weak + strong + maximizer). -/
def allNPIs : List PolarityItem := weakNPIs ++ strongNPIs ++ invertedNPIs

/-- The FCIs. -/
def allFCIs : List PolarityItem :=
  [any, whatever, whoever, whichever]

/-- The plain PPIs. -/
def canonicalPPIs : List PolarityItem :=
  [someone, already, too, somewhat, rather, tonsOf, awfully]

/-- The minimizer PPIs. -/
def invertedPPIs : List PolarityItem :=
  [atTheDropOfAHat, inAJiffy, forAPittance, forASong]

/-- All PPIs. -/
def allPPIs : List PolarityItem :=
  canonicalPPIs ++ invertedPPIs

/-- The full lexicon. -/
def allPolarityItems : List PolarityItem :=
  weakNPIs ++ strongNPIs ++ invertedNPIs ++
  [whatever, whoever, whichever] ++ allPPIs

end English.PolarityItems
