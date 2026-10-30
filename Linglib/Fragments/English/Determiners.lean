module

public import Linglib.Semantics.Quantification.Determiner
public import Linglib.Fragments.English.Phonology

/-!
# English determiners

The quantificational determiners of English are `QuantificationalDeterminer` records, each with
the readings available for it and what its readings leave open, the number the word selects and
whether it selects mass nouns: a word with one consensus reading has one, so `⟦all⟧` is
`{every}`, and *many*, whose standard Barwise and Cooper leave to context, has none. Everything
a reading fixes, its force, monotonicity, strength and conservativity, is a theorem about it, as
in `Studies/BarwiseCooper1981.lean`. The articles, demonstratives and possessives are the other
determiner kinds. The indefinite article has the liaison form *an* before a word that begins with
a vowel sound, and the weak form of *the* varies in the same environment.

## Main declarations

* `allQuantifiers`: the quantificational determiners, with the six-word scale `scale` of van
  Tiel, Franke and Sauerland inside it.
* `indefinite`, `theWeakForm`: the forms of the articles before each beginning of a word.
* `inventory`: the English determiner inventory, whose *the* marks both strengths
  (`isSyncretic_inventory`).

## References

* [barwise-cooper-1981]
* [horn-1972]
* [van-tiel-franke-sauerland-2021]
* [von-fintel-1993]
* [harbour-2014]
* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
* [schwarz-2009]
* [moroney-2021]
-/

@[expose] public section

namespace English.Determiners

/-! ## Quantificational determiners

A word records the readings the literature makes available for it, as determiner symbols: a word
with one consensus reading records one, so *all* reads as `every`, and *many*, whose standard
Barwise and Cooper leave to context, records none. The number a word selects and whether it
selects mass nouns are left open by its readings, so *every* and *all* share a reading and differ
there. *Both* and *neither* select the dual, the core concept `[−atomic, +minimal]` of
[harbour-2014], whose cardinality clause their readings reflect
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]). -/

/-- *None*, read as `no`. -/
def none_ : QuantificationalDeterminer :=
  { form := "none", readings := {.no}, selectsMass := true }

/-- *Few*, read as `few`, with a plural noun. -/
def few : QuantificationalDeterminer :=
  { form := "few", readings := {.few}, numberRestriction := some .plural }

/-- *Some*, read as `Quantifier.Det.some`. -/
def some_ : QuantificationalDeterminer :=
  { form := "some", readings := {.some}, selectsMass := true }

/-- *Half*, read as `half`. -/
def half : QuantificationalDeterminer :=
  { form := "half", readings := {.half}, selectsMass := true }

/-- *Most*, read as `most`, with a plural or a mass noun. -/
def most : QuantificationalDeterminer :=
  { form := "most", readings := {.most}, numberRestriction := some .plural, selectsMass := true }

/-- *All*, read as `every`, with a plural or a mass noun. -/
def all : QuantificationalDeterminer :=
  { form := "all", readings := {.every}, numberRestriction := some .plural, selectsMass := true }

/-- *Every*, read as `every`, with a singular noun. -/
def every : QuantificationalDeterminer :=
  { form := "every", readings := {.every}, numberRestriction := some .singular }

/-- *Each*, read as `every`, with a singular noun. -/
def each : QuantificationalDeterminer :=
  { form := "each", readings := {.every}, numberRestriction := some .singular }

/-- *Many*, with a plural noun and no reading, its standard left to context. -/
def many : QuantificationalDeterminer :=
  { form := "many", numberRestriction := some .plural }

/-- *Both*, read as `both`, with the dual. -/
def both : QuantificationalDeterminer :=
  { form := "both", readings := {.both}, numberRestriction := some .dual }

/-- *Neither*, read as `neither`, with the dual. -/
def neither : QuantificationalDeterminer :=
  { form := "neither", readings := {.neither}, numberRestriction := some .dual }

/-- The six-word quantity scale of [van-tiel-franke-sauerland-2021] runs from *none* to *all*;
quantifier theories such as those of [barwise-cooper-1981] and [von-fintel-1993] are compared on
it. -/
def scale : List QuantificationalDeterminer := [none_, few, some_, half, most, all]

/-! ## Articles, demonstratives and possessives

The articles and demonstratives are not quantifiers, since what they denote is definiteness and
not a generalized quantifier. -/

/-- *The* is the definite article, syncretic over both strengths of [schwarz-2009]. -/
def the : Article :=
  { form := "the", definiteness := .definite, exponent := .dedicatedMorpheme
  , uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- The weak form of *the*, /ðə/ before a consonant and /ði/ before a vowel, though some speakers
use /ðə/ throughout ([huddleston-pullum-2002] ch. 18 §6.1, p. 1613). -/
def theWeakForm : Phonology.Onset → List Phonology.Segment
  | .vowel => [Phonology.ð, Phonology.i]
  | .consonant => [Phonology.ð, Phonology.schwa]

/-- The singular indefinite article, *an* before a word beginning with a vowel and *a* elsewhere,
*an* being its liaison form ([huddleston-pullum-2002] ch. 18 §6.4, p. 1618). -/
def indefinite : Phonology.Onset → String
  | .vowel => "an"
  | .consonant => "a"

/-- *A* is the singular indefinite article, under its form before a consonant. -/
def a : Article :=
  { form := indefinite .consonant, definiteness := .indefinite, exponent := .dedicatedMorpheme,
    numberRestriction := some .singular }

open English.Phonology in
example : [[smallCapitalI, d, i, schwa, t], [wedge, ŋ, k, l], [j, u, n, smallCapitalI, t],
    [w, wedge, n, s], [scriptA, n, smallCapitalI, s, t], [h, æ, b, smallCapitalI, t, æ, t]].map
      (indefinite ∘ Onset.of) = ["an", "an", "a", "a", "an", "a"] := by
  decide

/-- *This* is the singular proximal demonstrative. -/
def this : DemonstrativeDeterminer := { form := "this", deixis := Person.first.participantSets }

/-- *That* is the singular distal demonstrative. -/
def that : DemonstrativeDeterminer := { form := "that", deixis := Person.first.participantSetsᶜ }

/-- *These* is the plural proximal demonstrative. -/
def these : DemonstrativeDeterminer := { form := "these", deixis := Person.first.participantSets }

/-- *Those* is the plural distal demonstrative. -/
def those : DemonstrativeDeterminer := { form := "those", deixis := Person.first.participantSetsᶜ }

/-- *My* is the first-person possessive determiner. -/
def my : PossessiveDeterminer := { form := "my" }

/-- *Your* is the second-person possessive determiner. -/
def your : PossessiveDeterminer := { form := "your" }

/-! ## The inventory -/

/-- The quantificational determiners. -/
def allQuantifiers : List QuantificationalDeterminer :=
  [none_, few, some_, half, most, all, every, each, many, both, neither]

/-- The articles. -/
def allArticles : List Article := [the, a]

/-- The demonstratives. -/
def allDemonstratives : List DemonstrativeDeterminer := [this, that, these, those]

/-- The possessive determiners. -/
def allPossessives : List PossessiveDeterminer := [my, your]

/-- The determiner inventory collects every kind of determiner. -/
def inventory : Determiner.Inventory :=
  allArticles.map .article ++ allDemonstratives.map .demonstrative ++
    allQuantifiers.map .quantifier ++ allPossessives.map .possessive

/-- A single article marks both strengths. -/
theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end English.Determiners
