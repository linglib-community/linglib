module

public import Linglib.Syntax.Feature.Case.Function

/-!
# Georgian case

Hewitt's grammar gives Georgian seven cases, the nominative, vocative, dative, ergative,
genitive, instrumental and adverbial, in essentially one declension for all nouns. Besides the
functions of its name, the dative marks location with a few nouns, where the language otherwise
uses the postpositions *-ši* 'in' and *-ze* 'on', and the adverbial marks both the state and the
change of state of a predication, as in *gvel-i kva-d (gada-)i-kc-a* 'the snake turned into
stone'. The paradigms that distinguish the seven cases are in `Georgian.Declension`.

## Main definitions

* `Georgian.Case`: the seven cases, in Hewitt's order.
* `Georgian.Case.label`, `Georgian.Case.functions`: the comparative value each case is named for,
  and the functions it marks.

## Implementation notes

The case of the subject and the objects changes with the series of the verb, so `functions`
gives a case the core roles it marks in some series, the nominative S, A and P and the dative P
and A beside the recipient; which it marks in which series is `Georgian.marking`. `functions`
leaves out time, which Hewitt gives to the nominative, the dative and the instrumental. Hewitt
also lists among the case functions an ablative, the instrumental followed by *-gan* 'from',
which is not one of the seven cases, so `functions` has no source.

## References

* [hewitt-1995]
-/

@[expose] public section

namespace Georgian

/-- The seven cases, in Hewitt's order. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The vocative. -/
  | voc
  /-- The dative. -/
  | dat
  /-- The ergative. -/
  | erg
  /-- The genitive. -/
  | gen
  /-- The instrumental. -/
  | inst
  /-- The adverbial, as in *briq'v-ada* 'as an idiot'. -/
  | adv
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for, the essive for the adverbial. -/
def label : Case → _root_.Case
  | nom => .nom
  | voc => .voc
  | dat => .dat
  | erg => .erg
  | gen => .gen
  | inst => .inst
  | adv => .ess

/-- The functions a case marks: the nominative marks S, the subject of a transitive verb in the
first series and its direct object in the second and third, the dative its direct object in the
first series and its subject in the third, and location with a few nouns ([hewitt-1995]
pp. 531–532), and the adverbial the change of state (p. 534). -/
def functions : Case → Finset _root_.Case.Function
  | nom => {.argument .S, .argument .A, .argument .P}
  | dat => {.argument .R, .argument .P, .argument .A, .spatial none .place}
  | adv => {.essive, .translative}
  | c => c.label.functions

theorem label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

end Case

end Georgian
