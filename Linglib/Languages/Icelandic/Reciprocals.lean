module

public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Syntax.Reciprocal

/-!
# Icelandic reciprocals

Icelandic marks reciprocity with the two-part noun phrase *hvort annað* 'each other', cited in
its neuter forms as in Nordlinger's (17a). The noun phrase fills the object position, so the
clause stays transitive, and its two parts inflect for case independently, as Hurst and Nordlinger
describe: the quantifier *hvor* agrees in case with the antecedent, and *annað* takes the case of
its argument position. The reciprocal is distinct in form from the reflexive *sig*, which is also
bound from outside its clause, out of a subjunctive complement, as in the examples of Sells.

## Main definitions

* `Icelandic.Reciprocals.hvorAnnad`, `Icelandic.Reciprocals.markers`: the reciprocal noun
  phrase, and the reciprocal markers.
* `Icelandic.Reciprocals.sig`: the reflexive pronoun.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [P. Hurst and R. Nordlinger, *An LFG Approach to Icelandic Reciprocal Constructions*
  (2021)][hurst-nordlinger-2021]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

@[expose] public section

namespace Icelandic.Reciprocals

open Reciprocal

/-- *hvort annað* 'each other', the two-part reciprocal noun phrase in its neuter forms; both
parts inflect for case and gender independently. -/
def hvorAnnad : Marker := { morphs := [.free "hvort", .free "annað"], strategy := .bipartiteNP }

/-- The reflexive pronoun *sig*, which is also bound from outside its clause. -/
def sig : ReflexivePronoun := { form := "sig", person := some .third }

/-- The reciprocal markers. -/
def markers : Finset Marker := {hvorAnnad}

end Icelandic.Reciprocals
