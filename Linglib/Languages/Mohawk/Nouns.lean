module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Mohawk noun stems

This file defines the Mohawk noun stems of the incorporation examples of [pullum-gazdar-1982],
who take them from the descriptions they cite. A noun is cited by its stem, the part that a verb
incorporates: the paper segments *ka-nuhs-aʔ* 'house' with the stem *-nuhs-* between a prefix and
a suffix, and the same stem is inside the verb of *k-nuhs-nuhweʔs* 'I like the house'. The forms
are in the transcription of that paper.

## References

* [pullum-gazdar-1982]
-/

@[expose] public section

namespace Mohawk.Nouns

/-- *-nuhs-* 'house', as in *ka-nuhs-aʔ*. -/
def nuhs : Noun := { form := "nuhs", gloss := "house" }

/-- *-hnek-* 'liquid', a stem that a verb incorporates when its object is a drinkable liquid. -/
def hnek : Noun := { form := "hnek", gloss := "liquid" }

/-- *-tsiʔts-* 'flower' and 'wine', as in *otsìʔtsaʔ*. -/
def tsits : Noun := { form := "tsiʔts", gloss := "flower, wine" }

/-- *-seleht-* 'vehicle'. -/
def seleht : Noun := { form := "seleht", gloss := "vehicle" }

/-- *-liʔw-* 'idea'. -/
def liw : Noun := { form := "liʔw", gloss := "idea" }

/-- *bike*, the English noun as the external noun of a Mohawk verb. -/
def bike : Noun := { form := "bike", gloss := "bike" }

/-- *sawatis* 'John'. -/
def sawatis : ProperName := { form := "sawatis", gloss := "John" }

end Mohawk.Nouns
