module

public import Linglib.Semantics.Modality.Typology

/-!
# Washo modals

Washo (Hokan/isolate, ISO 639-3 `was`) expresses modality with the verb *-eʔ*, the copula of
individual-level predication used without an overt subject and with a clause as its complement
([bochnak-2015a] §2). It keeps the individual-level agreement (third person *k'-*, first person
*L-*), most often third person whatever the subject of the prejacent, and the prejacent is a
non-finite clause or a finite clause closed by the relativizer *-gi*: *súku baŋáya ʔéʔišgi k'éʔi*
'The dog has to stay outside.'

*-eʔ* leaves both force and flavor to context. [bochnak-2015a] §3 elicits it in necessity, weak
necessity and possibility contexts, with deontic, metaphysical, epistemic, bouletic, generic and
circumstantial flavors, though speakers tend to use an evidential in epistemic contexts. Negation
is marked inside the prejacent and never on *-eʔ* itself ([bochnak-2015a] §5), and the subjunctive
*-hel* on the prejacent rules out the necessity reading ([bochnak-2015b] §4).

## References

* [bochnak-2015a]
* [bochnak-2015b]
-/

@[expose] public section

namespace Washo

open Modality

/-- The modal verb *-eʔ*, which [bochnak-2015a] finds lexically specified for neither force nor
flavor, so that it expresses every force-flavor pair. -/
def modalEq : ModalItem where
  form := "-eʔ"
  meaning := Finset.univ

end Washo
