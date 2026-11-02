module

public import Linglib.Semantics.Degree.Adjective
public import Linglib.Fragments.English.Inflection

/-!
# English adjectives

This file lists the English adjective lexemes. An entry records the surface
form, the scalar dimension, the polarity, the antonym and, where it is given, the comparison
paradigm. An adjective compares with the suffixes *-er* and *-est*, with the degree words
*more* and *most*, or on another root, as *good*, *better*, *best* does. An antonym pair is
entered once, as an `AntonymPair` on its shared scale, and its two polar adjectives are the
pair's `pos` and `neg`.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [bobaljik-2012]
* [tham-2025]
* [beltrama-2025]
* [nouwen-2024]
* [cariani-santorio-wellwood-2024]
* [goodman-2024]
* [lassiter-2017]
* [rappaport-hovav-2014]
* [rotstein-winter-2004]
* [morzycki-2012]
* [alexandropoulou-gotzner-2024a]
-/

@[expose] public section

namespace English.Adjectives

open Degree Morphology

/-! ### Grade -/

/-- The degree word of the analytic comparative. -/
def more : Morph := .free "more"

/-- The degree word of the analytic superlative. -/
def most : Morph := .free "most"

/-- The inflectional comparison of `form`, with the suffixes *-er* and *-est*. -/
def inflectional (form : String) : Adjective.Comparison :=
  { comparative := [.root form, Inflection.er], superlative := [.root form, Inflection.est] }

/-- The analytic comparison of `form`, with the degree words *more* and *most*. -/
def analytic (form : String) : Adjective.Comparison :=
  { comparative := [more, .root form], superlative := [most, .root form] }

/-- The comparison of an adjective whose comparative and superlative are on another root. -/
def suppletive (comparative superlative : String) : Adjective.Comparison :=
  { comparative := [.root comparative], superlative := [.root superlative] }

/-! ### The lexemes -/

def height : AntonymPair :=
  { dimension := .height, posForm := "tall", negForm := "short"
  , posComparison := inflectional "tall"
  , negComparison := inflectional "short" }

abbrev tall := height.pos

abbrev short := height.neg

def elevation : AntonymPair :=
  { dimension := .height, posForm := "high", negForm := "low" }

abbrev high := elevation.pos

abbrev low := elevation.neg

/-- *happy* here is the one-place predicate "x is happy"; the two-place veridical-preferential
attitude predicate "x is happy that p" is in `Studies/UegakiSudo2019.lean`. -/
def happiness : AntonymPair :=
  { dimension := .happiness, posForm := "happy", negForm := "unhappy"
  , posComparison := inflectional "happy"
  , negComparison := inflectional "unhappy", evaluativeValence := some .positive }

abbrev happy := happiness.pos

abbrev unhappy := happiness.neg

def sad : GradableAdjective :=
  { form := "sad", polarity := .negative, dimension := some .happiness
  , comparison := inflectional "sad"
  , antonymForm := some "happy"
  , evaluativeValence := some .negative }

/-- *full* and *empty* measure on a closed scale, as *100% full* and *100% empty* show
([kennedy-mcnally-2005] (28a)), and both poles take the maximum standard ([kennedy-2007], p. 38),
so a half-full glass is neither full nor empty. -/
def fullness : AntonymPair :=
  { dimension := .fullness, posForm := "full", negForm := "empty"
  , posComparison := inflectional "full"
  , negComparison := inflectional "empty" }

abbrev full := fullness.pos

abbrev empty := fullness.neg

def heat : AntonymPair :=
  { dimension := .temperature, posForm := "hot", negForm := "cold"
  , posComparison := inflectional "hot", negComparison := inflectional "cold" }

abbrev hot := heat.pos

abbrev cold := heat.neg

def cost : AntonymPair :=
  { dimension := .cost, posForm := "expensive", negForm := "cheap"
  , posComparison := analytic "expensive"
  , negComparison := inflectional "cheap" }

abbrev expensive := cost.pos

abbrev cheap := cost.neg

def wetness : AntonymPair :=
  { dimension := .wetness, posForm := "wet", negForm := "dry"
  , posComparison := inflectional "wet", negComparison := inflectional "dry" }

abbrev wet := wetness.pos

abbrev dry := wetness.neg

def cleanliness : AntonymPair :=
  { dimension := .cleanliness, posForm := "clean", negForm := "dirty" }

abbrev clean := cleanliness.pos

abbrev dirty := cleanliness.neg

def straightness : AntonymPair :=
  { dimension := .straightness, posForm := "straight"
  , negForm := "bent" }

abbrev straight := straightness.pos

abbrev bent := straightness.neg

def flat : GradableAdjective :=
  { form := "flat", dimension := some .flatness, antonymForm := some "bumpy"
  , spatialConfigType := some .surfaceOrient }

/-- *open* takes the minimum standard, any amount of opening ([kennedy-2007] (68)); *closed* the
maximum. -/
def openness : AntonymPair :=
  { dimension := .openness, posForm := "open", negForm := "closed"
  , posLexicalStandard := some .minEndpoint, spatialConfigType := some .barrierConfig }

abbrev open_ := openness.pos

abbrev closed_ := openness.neg

def shut : GradableAdjective :=
  { form := "shut", polarity := .negative, dimension := some .openness, antonymForm := some "open"
  , spatialConfigType := some .barrierConfig }

def free_ : GradableAdjective :=
  { form := "free", dimension := some .freedom, antonymForm := some "stuck"
  , spatialConfigType := some .unattachment }

def loose : GradableAdjective :=
  { form := "loose", polarity := .negative, dimension := some .tightness
  , antonymForm := some "tight"
  , spatialConfigType := some .unattachment }

def tight : GradableAdjective :=
  { form := "tight", dimension := some .tightness, antonymForm := some "loose" }

def smoothness : AntonymPair :=
  { dimension := .smoothness, posForm := "smooth", negForm := "rough" }

abbrev smooth := smoothness.pos

abbrev rough := smoothness.neg

def hardness : AntonymPair :=
  { dimension := .hardness, posForm := "hard", negForm := "soft" }

abbrev hard := hardness.pos

abbrev soft := hardness.neg

def pure_ : GradableAdjective :=
  { form := "pure", dimension := some .purity, antonymForm := some "impure" }

/-- *dead* takes the maximum standard and is rarely used imprecisely ([kennedy-mcnally-2005]);
*alive* the minimum. -/
def life : AntonymPair :=
  { dimension := .alive, posForm := "alive", negForm := "dead"
  , posLexicalStandard := some .minEndpoint }

abbrev alive := life.pos

abbrev dead := life.neg

def pregnant : GradableAdjective :=
  { form := "pregnant" }

def size : AntonymPair :=
  { dimension := .generalSize, posForm := "large", negForm := "small" }

abbrev large := size.pos

abbrev small := size.neg

/-- *gigantic* and *tiny* are extreme adjectives on the scale of *large* and *small*, with standards
beyond theirs ([morzycki-2012]). -/
def extremeSize : AntonymPair :=
  { dimension := .generalSize, posForm := "gigantic", negForm := "tiny"
  , posLexicalStandard := some .extreme, negLexicalStandard := some .extreme }

abbrev gigantic := extremeSize.pos

abbrev tiny := extremeSize.neg

/-- *pristine* and *filthy* are extreme adjectives on the scale of *clean* and *dirty*, with
standards beyond theirs, so the pair leaves a gap although the weak pair does not
([alexandropoulou-gotzner-2024a]). -/
def pristineness : AntonymPair :=
  { dimension := .cleanliness, posForm := "pristine", negForm := "filthy"
  , posLexicalStandard := some .extreme, negLexicalStandard := some .extreme
  , evaluativeValence := some .positive }

abbrev pristine := pristineness.pos

abbrev filthy := pristineness.neg

def long : GradableAdjective :=
  { form := "long", dimension := some .length, antonymForm := some "short" }

def wide : GradableAdjective :=
  { form := "wide", dimension := some .width, antonymForm := some "narrow" }

def warmth : AntonymPair :=
  { dimension := .temperature, posForm := "warm", negForm := "cool" }

abbrev warm := warmth.pos

abbrev cool := warmth.neg

/-! ## Physical dimension adjectives -/

def weight : AntonymPair :=
  { dimension := .weight, posForm := "heavy", negForm := "light" }

abbrev heavy := weight.pos

abbrev light := weight.neg

def thickness : AntonymPair :=
  { dimension := .thickness, posForm := "thick", negForm := "thin" }

abbrev thick := thickness.pos

abbrev thin := thickness.neg

def depth : AntonymPair :=
  { dimension := .depth, posForm := "deep", negForm := "shallow" }

abbrev deep := depth.pos

abbrev shallow := depth.neg

def strength : AntonymPair :=
  { dimension := .strength, posForm := "strong", negForm := "weak" }

abbrev strong := strength.pos

abbrev weak := strength.neg

def speed : AntonymPair :=
  { dimension := .speed, posForm := "fast", negForm := "slow" }

abbrev fast := speed.pos

abbrev slow := speed.neg

def age : AntonymPair :=
  { dimension := .age, posForm := "old", negForm := "young" }

abbrev old := age.pos

abbrev young := age.neg

/-! ## Sensory adjectives -/

def brightness : AntonymPair :=
  { dimension := .brightness, posForm := "bright", negForm := "dark" }

abbrev bright := brightness.pos

abbrev dark := brightness.neg

def volume : AntonymPair :=
  { dimension := .volume, posForm := "loud", negForm := "quiet" }

abbrev loud := volume.pos

abbrev quiet := volume.neg

/-! ## Intelligence and confidence

The confidence adjectives are the gradable attitude adjectives of
[cariani-santorio-wellwood-2024]. They measure on an upper-bounded confidence
scale, with *certain* at its maximum and *doubtful*, *unsure* and *uncertain*
on its negative pole. -/

def smart : GradableAdjective :=
  { form := "smart", dimension := some .intelligence, comparison := inflectional "smart"
  , antonymForm := some "dumb" }

/-- *Tragic* measures tragedy, which no other entry does. -/
def tragic : GradableAdjective :=
  { form := "tragic", dimension := some .tragedy, comparison := analytic "tragic" }

/-- *Clever* measures intelligence, as *smart* does. -/
def clever : GradableAdjective :=
  { form := "clever", dimension := some .intelligence, comparison := inflectional "clever" }

/-- *Wise* measures wisdom, which *clever* does not: *clever but not wise* is consistent. -/
def wise : GradableAdjective :=
  { form := "wise", dimension := some .wisdom, comparison := inflectional "wise"
  , antonymForm := some "foolish" }

/-- *Confident* is relative on the upper-closed confidence scale. [cariani-santorio-wellwood-2024]
give it the ordering of *certain* with a contextual contrast state below *certain*'s maximal
states ((40), Figure 3), so that *confident but not certain* (65a) is consistent while
*completely confident* (69a) reaches the maximum. [goodman-2024]'s non-extremity makes its
threshold non-maximal in many ordinary contexts, on the evidence of *confident that p, and even
more confident that p or q* (3). Interpretive Economy ([kennedy-2007] (66)) would give it the
maximum of the scale, so the standard is lexical. -/
def confident : GradableAdjective :=
  { form := "confident", dimension := some .confidence, lexicalStandard := some .contextual
  , comparison := analytic "confident" }

/-- *certain* and *uncertain* measure on an upper-closed scale, *certain* with the maximum standard
and *uncertain* with the minimum, as *perfectly certain* and *slightly uncertain* show
([kennedy-2007] (64)), so the pair is contradictory. -/
def confidence : AntonymPair :=
  { dimension := .confidence, posForm := "certain", negForm := "uncertain"
  , posComparison := analytic "certain"
  , negComparison := analytic "uncertain" }

abbrev certain := confidence.pos

abbrev uncertain := confidence.neg

/-- *sure* and *unsure* are entered on the scale of *certain* and *uncertain*. -/
def sureness : AntonymPair :=
  { dimension := .confidence, posForm := "sure", negForm := "unsure"
  , posComparison := inflectional "sure"
  , negComparison := analytic "unsure" }

abbrev sure := sureness.pos

abbrev unsure := sureness.neg

def doubtful : GradableAdjective :=
  { form := "doubtful", polarity := .negative, dimension := some .confidence
  , comparison := analytic "doubtful" }

/-! ## Evaluative adjectives -/

/-- "good" — open value scale, contrary to "bad". "good" takes a contextual
    standard and patterns with relative adjectives ([beltrama-2025] §3); on the
    open `.value` scale this class is *derived* (open ⇒ contextual) rather than
    stipulated, so no `lexicalStandard` is needed. -/
def value : AntonymPair :=
  { dimension := .value, posForm := "good", negForm := "bad"
  , posComparison := suppletive "better" "best", negComparison := suppletive "worse" "worst"
  , evaluativeValence := some .positive }

abbrev good := value.pos

abbrev bad := value.neg

def beauty : AntonymPair :=
  { dimension := .beauty, posForm := "beautiful", negForm := "ugly"
  , evaluativeValence := some .positive }

abbrev beautiful := beauty.pos

abbrev ugly := beauty.neg

def important : GradableAdjective :=
  { form := "important", dimension := some .importance }

/-- *safe* and *dangerous* measure on an upper-closed scale, so *completely safe* is fine but
*??completely dangerous* is not ([kennedy-mcnally-2005] (27c)), and the pair is weak and
contradictory, as Gotzner and Mazzarella's entailment pretest assumes ([gotzner-mazzarella-2024],
Appendix 1). Alexandropoulou and Gotzner instead use it as a strong pair in their materials
([alexandropoulou-gotzner-2024a], Table A.2), which would make it contrary. -/
def safety : AntonymPair :=
  { dimension := .safety, posForm := "safe", negForm := "dangerous"
  , evaluativeValence := some .positive }

abbrev safe := safety.pos

abbrev dangerous := safety.neg

/-! ## Physical disturbance deverbal adjectives

[tham-2025]: physical disturbance predicates are associated with a totally
closed, multi-point scale. Lower bound = physical instantiation of disturbance;
upper bound = spatial extent of host entity. Gradable (*more cracked*, *badly
dented*), compatible with *completely* and *partially*. Contra
[rappaport-hovav-2014] (two-point) and [rotstein-winter-2004]
(lower-bounded only). -/

/-- "cracked" — closed scale, contradictory to "uncracked".
    Deverbal adjective from *crack* (Levin 45.1 Break verbs).
    NOT a two-point scale: accepts *more cracked*, *completely cracked*,
    *partially cracked*, *badly cracked* ([tham-2025] §2.3–2.4). -/
def cracked : GradableAdjective :=
  { form := "cracked", dimension := some .cracking, lexicalStandard := some .minEndpoint }

/-- "dented" — closed scale.
    Deverbal adjective from *dent*. Accepts *more dented*, *completely dented*,
    *badly dented* ([tham-2025] (11a), (20b)). -/
def dented : GradableAdjective :=
  { form := "dented", dimension := some .denting, lexicalStandard := some .minEndpoint }

/-- "scratched" — closed scale.
    Deverbal adjective from *scratch*. Accepts *more scratched*, *completely
    scratched*, *badly scratched* ([tham-2025] (11b), (20c)). -/
def scratched : GradableAdjective :=
  { form := "scratched", dimension := some .scratching, lexicalStandard := some .minEndpoint }

/-- "shattered" — closed scale, NON-GRADABLE.
    Deverbal adjective from *shatter* (Levin 45.1 Break verbs).
    Contrast: ??*more shattered*, punctual verb, no durative reading.
    Not a physical disturbance predicate ([tham-2025] (12c)). -/
def shattered : GradableAdjective :=
  { form := "shattered" }

/-! ## Mildly positive adjectives (MPAs)

[beltrama-2025]: MPAs encode a necessity standard — the minimum value
required for pursuit. They share properties with both relative (context-sensitive,
gradable) and absolute (no zone of indifference, crisp judgments, *barely*
compatible) predicates. -/

/-- "nice" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *nicely*. -/
def nice : GradableAdjective :=
  { form := "nice", dimension := some .value, evaluativeValence := some .positive }

/-- "pleasant" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *pleasantly*. -/
def pleasantness : AntonymPair :=
  { dimension := .value, posForm := "pleasant", negForm := "unpleasant"
  , evaluativeValence := some .positive }

abbrev pleasant := pleasantness.pos

abbrev unpleasant := pleasantness.neg

/-- *decent* is a mildly positive adjective, on the open value scale with a functional
    (necessity) standard ([beltrama-2025]) recorded as its `lexicalStandard`. -/
def decent : GradableAdjective :=
  { form := "decent", dimension := some .value, evaluativeValence := some .positive
  , lexicalStandard := some .necessity }

/-- "acceptable" — mildly-positive adjective; open `.value` scale, functional
    standard ([beltrama-2025]). Deverbal *-able* form: the modal suffix
    contributes the functional standard. -/
def acceptable : GradableAdjective :=
  { form := "acceptable", dimension := some .value, evaluativeValence := some .positive
  , lexicalStandard := some .necessity }

/-- "adequate" — mildly-positive adjective; open `.value` scale, functional
    (necessity) standard ([beltrama-2025]). -/
def adequate : GradableAdjective :=
  { form := "adequate", dimension := some .value, evaluativeValence := some .positive
  , lexicalStandard := some .necessity }

/-! ## Deadjectival intensifier bases ([nouwen-2024])

Adjectival bases for deadjectival intensifiers. Evaluative adjectives
(horrible, wonderful) derive H-degree or M-degree intensifiers via the
Goldilocks effect. Mirative (unusual, surprising) and modal (possible,
impossible) bases follow Zwicky's generalization. -/

/-! ### Negative-evaluative bases: H-degree intensifiers -/

/-- "horrible" — open scale, negative evaluative. Base for H-degree *horribly*. -/
def horrible : GradableAdjective :=
  { form := "horrible", dimension := some .quality, evaluativeValence := some .negative }

/-- "terrible" — open scale, negative evaluative. Base for H-degree *terribly*. -/
def terrible : GradableAdjective :=
  { form := "terrible", dimension := some .quality, evaluativeValence := some .negative }

/-- "awful" — open scale, negative evaluative. Base for H-degree *awfully*. -/
def awful : GradableAdjective :=
  { form := "awful", dimension := some .quality, evaluativeValence := some .negative }

/-- "dreadful" — open scale, negative evaluative. Base for H-degree *dreadfully*. -/
def dreadful : GradableAdjective :=
  { form := "dreadful", dimension := some .quality, evaluativeValence := some .negative }

/-- "frightening" — open scale, negative evaluative. Base for H-degree *frighteningly*. -/
def frightening : GradableAdjective :=
  { form := "frightening", dimension := some .danger, evaluativeValence := some .negative }

/-- "disgusting" — open scale, negative evaluative. Base for H-degree *disgustingly*. -/
def disgusting : GradableAdjective :=
  { form := "disgusting", dimension := some .quality, evaluativeValence := some .negative }

/-- "annoying" — open scale, negative evaluative. Base for H-degree *annoyingly*. -/
def annoying : GradableAdjective :=
  { form := "annoying", dimension := some .quality, evaluativeValence := some .negative }

/-- "scary" — open scale, negative evaluative. Base for H-degree *scarily*. -/
def scary : GradableAdjective :=
  { form := "scary", dimension := some .danger, evaluativeValence := some .negative }

/-! ### Positive-evaluative bases: M-degree intensifiers -/

/-- "wonderful" — open scale, positive evaluative. Base for M-degree *wonderfully*. -/
def wonderful : GradableAdjective :=
  { form := "wonderful", dimension := some .quality, evaluativeValence := some .positive }

/-- "delightful" — open scale, positive evaluative. Base for M-degree *delightfully*. -/
def delightful : GradableAdjective :=
  { form := "delightful", dimension := some .quality, evaluativeValence := some .positive }

/-- "gorgeous" — open scale, positive evaluative. Base for M-degree *gorgeously*. -/
def gorgeous : GradableAdjective :=
  { form := "gorgeous", dimension := some .beauty, evaluativeValence := some .positive }

/-! ### Mirative bases: H-degree intensifiers, not evaluative -/

def expectation : AntonymPair :=
  { dimension := .expectation, posForm := "usual", negForm := "unusual"
  , evaluativeValence := some .neutral }

abbrev usual := expectation.pos

abbrev unusual := expectation.neg

/-- "surprising" — open scale, neutral (mirative). Base for H-degree *surprisingly*. -/
def surprising : GradableAdjective :=
  { form := "surprising", dimension := some .expectation, evaluativeValence := some .neutral }

/-- "remarkable" — open scale, positive evaluative (§2.4.1). Extreme positive
    evaluation: H-degree *remarkably* despite positive valence (Goldilocks exception). -/
def remarkable : GradableAdjective :=
  { form := "remarkable", dimension := some .quality, evaluativeValence := some .positive }

/-- "stunning" — open scale, positive evaluative (Figure 2, upper-right quadrant).
    Extreme positive evaluation: H-degree *stunningly* (Goldilocks exception). -/
def stunning : GradableAdjective :=
  { form := "stunning", dimension := some .quality, evaluativeValence := some .positive }

/-! ### Modal bases: Zwicky's generalization -/

/-- "expected" — open scale, neutral (modal). Unattested as intensifier (*expectedly). -/
def expected : GradableAdjective :=
  { form := "expected", dimension := some .expectation, evaluativeValence := some .neutral }

/-- *possible* and *impossible* are contradictories, since *possible* takes the minimum standard of
the lower-closed possibility scale and *impossible* the maximum of its dual, as *wet* and *dry* do.
Whether *possible* is gradable at all is disputed ([lassiter-2017] §5.2.2); the entry records its
gradable use, which *impossibly long* needs ([nouwen-2024] (27b)). -/
def possibility : AntonymPair :=
  { dimension := .possibility, posForm := "possible"
  , negForm := "impossible", evaluativeValence := some .neutral }

abbrev possible := possibility.pos

abbrev impossible := possibility.neg

/-! ### Inventory -/

/-- The antonym pairs of the fragment. -/
def pairs : List AntonymPair := [
  height, elevation, happiness, fullness, heat, cost, wetness, cleanliness, straightness, openness,
  smoothness, hardness, life, size, extremeSize, pristineness, warmth, weight, thickness, depth,
  strength, speed, age, brightness, volume, confidence, sureness, value, beauty, pleasantness,
  expectation, possibility, safety]

/-- The entries outside an antonym pair. -/
def singletons : List GradableAdjective := [
  sad, flat, shut, free_, loose, tight, pure_, pregnant, long, wide, smart, tragic, clever,
  wise, confident,
  doubtful, important, cracked, dented, scratched, shattered, nice, decent,
  acceptable, adequate, horrible, terrible, awful, dreadful, frightening, disgusting, annoying,
  scary, wonderful, delightful, gorgeous, surprising, remarkable, stunning, expected]

/-- Every entry of the fragment. -/
def allEntries : List GradableAdjective :=
  pairs.flatMap (fun p ↦ [p.pos, p.neg]) ++ singletons

/-- The entry with a given surface form. -/
def lookup (form : String) : Option GradableAdjective :=
  allEntries.find? (·.form == form)

/-- The antonym pair with a given surface form as one of its poles. -/
def pairOf (form : String) : Option AntonymPair :=
  pairs.find? fun p ↦ p.posForm == form || p.negForm == form

/-- The grades are spelled by the rules of `English.Inflection`, with the consonant doubled in
*sadder*, the *y* replaced in *happiest* and *drier* and the *e* dropped in *surer*. -/
example :
    Inflection.spell sad.comparison.comparative = "sadder" ∧
      Inflection.spell happy.comparison.superlative = "happiest" ∧
      Inflection.spell dry.comparison.comparative = "drier" ∧
      Inflection.spell sure.comparison.comparative = "surer" ∧
      Inflection.spell confident.comparison.comparative = "more confident" ∧
      Inflection.spell good.comparison.superlative = "best" := by
  decide

end English.Adjectives
