module

public import Linglib.Syntax.Reflex
public import Linglib.Languages.Mayan.Extraction

/-!
# Tseltal extraction marking

Tseltal (Tseltalan Mayan) has no Agent Focus form, so a transitive subject extracts without a
reflex on the verb, as the intransitive subject and the patient do; Polian notes an Agent Focus
inverse voice in the Villa Las Rosas variety alone, which this language file does not describe. A
recipient or benefactive
is the primary object of the applicative *-bey* or *-be*, cross-referenced by Set B as the object
of a transitive verb is. When an instrument is questioned, focused or relativized, the
preposition *ta* gives way to the enclitic *=ˀa*, on the last word before a definite noun phrase.

## Main declarations

* `Tseltal.Extraction.realize`: no reflex for the extraction of the intransitive subject, the
  transitive subject, the patient or the recipient.

## Implementation notes

The instrument cell is `none`: the host of *=ˀa*, the last word before a definite noun phrase,
is not among the `Mayan.Host`s. The theme beside an applied recipient is unrecorded.

## References

* [polian-2017b]
-/

@[expose] public section

namespace Tseltal.Extraction

/-- The extraction of an argument leaves no reflex, a recipient being the primary object of the
applicative ([polian-2017b] pp. 626–627); the theme and the adjuncts are unrecorded. -/
def realize : Mayan.ExtractionSite → Option (Finset (Reflex Mayan.Host))
  | .argument .S | .argument .A | .argument .P | .argument .R => some ∅
  | _ => none

end Tseltal.Extraction
