module

public import Linglib.Semantics.Tense.Connective

/-!
# Greek temporal connectives

Lexical entries for the Modern Greek temporal connectives: *prin* 'before', whose complement is a
*na*-subjunctive, *afou* 'after' and *otan* 'when' with indicative complements, and *mexri*
'until'. Giannakidou takes *mexri* for Karttunen's durative *until* and the polarity item *para
monon*, literally 'but only', for the punctual one, so that Greek lexicalizes the two *until*s
apart; Iatridou and Zeijlstra read *para monon* as an exceptive and note that *mexri* also takes
perfectives. Each classification lives in its paper's study.

## References

* [giannakidou-2002]
* [karttunen-1974]
* [iatridou-zeijlstra-2021]
-/

@[expose] public section

namespace Greek.StandardModern.TemporalConnectives

open Tense

/-- *prin* (πριν) 'before' takes a *na*-subjunctive complement, as in *efije prin na erthi o
Janis* 'she left before Janis came'. -/
def prin : Connective := { form := "prin", relation := .before }

/-- *afou* (αφού) 'after' takes an indicative complement, as in *efije afou irthe o Janis* 'she
left after Janis came'. -/
def afou : Connective := { form := "afou", relation := .after }

/-- *otan* (όταν) 'when' takes an indicative complement, as in *efije otan irthe o Janis* 'she
left when Janis came'. -/
def otan : Connective := { form := "otan", relation := .when_ }

/-- *mexri* (μέχρι) means 'until', as in *i prigipisa kimotane mexri ta mesanixta* 'the princess
was sleeping until midnight'. -/
def mexri : Connective := { form := "mexri", relation := .until_ }

end Greek.StandardModern.TemporalConnectives
