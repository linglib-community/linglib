module

public import Linglib.Syntax.Clause.Relative

/-!
# Hebrew relative clauses

Modern Hebrew forms its postnominal relative clauses with the complementizer *she-*, in two
ways. With the relativized position left empty, *she-* relativizes subjects and direct objects.
With a personal pronoun in the relativized position, the strategy Keenan and Comrie take as the
characteristic Semitic one, it relativizes everything from direct objects down to objects of
comparison: *ha-isha she-David natan la et ha-sefer* 'the woman that David gave the book to',
with the pronoun in *la* 'to her'. The direct object is shared between the two, subjects do not
retain a pronoun, and relative clauses on objects of comparison are only marginally
acceptable. The data are Keenan and Comrie's; Sichel's distinction between the optional
resumptive of direct objects, a bound pronoun, and the obligatory resumptive of prepositional
objects, a movement copy, is the matter of the studies of resumption.

## Main definitions

* `Hebrew.relShe`, `Hebrew.relativizers`: the relativizer *she-*.

## References

* [keenan-comrie-1977]
* [sichel-2014]
-/

@[expose] public section

namespace Hebrew

/-- The complementizer *she-*: the relativized position is left empty at the subject, left
empty or filled by a personal pronoun at the direct object, and filled by a personal pronoun
from the indirect object down to the object of comparison. -/
def relShe : Relativizer where
  placement := .postNominal
  realize
    | .subject => {.gap}
    | .directObject => {.gap, .resumptive}
    | _ => {.resumptive}

/-- The relativizers. -/
def relativizers : List Relativizer := [relShe]

end Hebrew
