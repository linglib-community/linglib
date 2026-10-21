module

public import Linglib.Fragments.Slavic.Polish.Case

/-!
# Polish interrogative pronouns

This file defines the case paradigms of the interrogative pronouns *kto* 'who' and *co* 'what',
which have no vocative. In the accusative *kto* takes its genitive *kogo* and *co* its
nominative, as the animate and the inanimate masculine nouns do, and each has one form for the
instrumental and the locative.

## References

* [rothstein-1993]
-/

@[expose] public section

namespace Polish.Pronouns

/-- *kto* 'who' by case ([rothstein-1993] p. 704). -/
def kto : Case → Option String
  | .nom => some "kto"
  | .gen => some "kogo"
  | .dat => some "komu"
  | .acc => some "kogo"
  | .inst => some "kim"
  | .loc => some "kim"
  | .voc => none

/-- *co* 'what' by case ([rothstein-1993] p. 704). -/
def co : Case → Option String
  | .nom => some "co"
  | .gen => some "czego"
  | .dat => some "czemu"
  | .acc => some "co"
  | .inst => some "czym"
  | .loc => some "czym"
  | .voc => none

/-- The accusative of *kto* is its genitive: "for animate nouns it is identical to the genitive"
([rothstein-1993] p. 698). -/
theorem kto_acc_eq_gen : kto .acc = kto .gen := rfl

/-- The accusative of *co* is its nominative: "The accusative singular of inanimate nouns is
identical to the nominative" ([rothstein-1993] p. 698). -/
theorem co_acc_eq_nom : co .acc = co .nom := rfl

end Polish.Pronouns
