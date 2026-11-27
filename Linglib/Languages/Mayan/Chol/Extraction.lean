module

public import Linglib.Syntax.Reflex
public import Linglib.Languages.Mayan.Extraction

/-!
# Chol extraction marking

Chol (Cholan Mayan) has no Agent Focus form, so the extraction of no argument leaves a reflex on
the verb, and a question with two third-person arguments is ambiguous between subject and object
extraction. A recipient or benefactive is the primary object of the applicative *-be*,
cross-referenced by Set B, and Coon, Mateo Pedro and Preminger observe that either object of an
applicative verb extracts. These sources do not describe the extraction of adjuncts.

## Main declarations

* `Chol.Extraction.realize`: no reflex for the extraction of any argument, adjuncts unrecorded.

## References

* [coon-mateo-pedro-preminger-2014]
* [vazquez-alvarez-2011]
-/

@[expose] public section

namespace Chol.Extraction

/-- The extraction of an argument leaves no reflex, the recipient and theme of the applicative
*-be* included ([coon-mateo-pedro-preminger-2014] §5.3); adjunct extraction is unrecorded. -/
def realize : Mayan.ExtractionSite → Option (Finset (Reflex Mayan.Host))
  | .argument _ => some ∅
  | .adjunct _ => none

end Chol.Extraction
