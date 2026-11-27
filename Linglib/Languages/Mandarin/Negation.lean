module

public import Linglib.Syntax.Negation
public import Linglib.Languages.Mandarin.Aspect

/-!
# Mandarin negation

Mandarin negates a declarative verbal clause with one of two preverbal negators, chosen by aspect.
*Bù* negates non-perfective predicates, present and future, is the natural choice with states, and
adds nothing else to the clause: *Nézha bù tǎoyàn Yángjiǎn* 'Nezha does not hate Yangjian'. *Méi*
negates perfective and experiential predicates and is the dedicated negator of the existential and
possessive verb *yǒu* 'have', which may follow it in the long form *méi-yǒu*. The perfective
particle *le* does not occur under it, while the experiential *guò* does: *Nézha chuī le chángdí*
'Nezha played the flute' is negated as *Nézha méi-yǒu chuī chángdí*. Prohibitions use neither
negator but the negative imperatives *bié* and *búyào*, literally 'not want'. The description
follows Miestamo, Zhao, and Jin and Koenig; Miestamo's classification of the constructions as
symmetric and asymmetric lives in `Studies/Miestamo2005.lean`, and the negators that appear
expletively under *fear* and *regret* are the rows of `Data.Examples.JinKoenig2021`.

## References

* [miestamo-2005]
* [zhao-2025]
* [jin-koenig-2021]
-/

@[expose] public section

open Negation

namespace Mandarin.Negation

/-- A Mandarin standard negator is given by its exponent, the aspectual domain it negates, the
verb that may follow it as part of the negator, and the aspect particles of the affirmative that
do not occur with it. -/
structure Negator where
  /-- The exponent. -/
  marker : Marker
  /-- The aspectual domain the negator negates. -/
  perfectivity : _root_.Aspect.Perfectivity
  /-- The verb that may follow the negator in its long form. -/
  verb : Option Morphology.Morph := none
  /-- The aspect particles of the affirmative that do not occur under the negator. -/
  excludes : List Aspect.Marker := []

/-- *bù* 不, the negator of non-perfective predicates. -/
def bu : Negator := { marker := { pieces := [[.free "bù"]] }, perfectivity := .imperfective }

/-- *méi* 没, long form *méi-yǒu* 没有, the negator of perfective and experiential predicates
and of *yǒu* 'have'. The perfective *le* does not occur with it. -/
def mei : Negator where
  marker := { pieces := [[.free "méi"]] }
  perfectivity := .perfective
  verb := some (.free "yǒu")
  excludes := [Aspect.le]

/-- The standard negators. -/
def negators : List Negator := [bu, mei]

/-- *bié* 别, the negative imperative. -/
def bie : Marker := { pieces := [[.free "bié"]] }

/-- *búyào* 不要, literally 'not want', the periphrastic negative imperative. -/
def buyao : Marker := { pieces := [[.free "bú", .free "yào"]] }

/-- *bùgāi* 不该, literally 'not should', the deontic negative 'should not'. -/
def bugai : Marker := { pieces := [[.free "bù", .free "gāi"]] }

end Mandarin.Negation
