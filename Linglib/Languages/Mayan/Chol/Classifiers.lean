module

public import Linglib.Syntax.Category.Classifier.Basic
public import Mathlib.Data.Finset.Insert

/-!
# Ch'ol numeral classifiers

A Ch'ol numeral of the native vigesimal series takes a classifier suffix: *ux-p'ej juñ* 'three
books', *ux-kojty mis* 'three cats'. The suffix is obligatory with the native numerals, and the
Spanish loan numerals from *siete* 'seven' up reject it. The classifier is chosen by the noun and
its configuration: many classifiers derive from positional and transitive verb roots, *-kojty*
from *koty* 'standing on four legs' and *-bujch* from *buch* 'seated', so one noun is counted
with different classifiers in different positions. *-p'ej* is the general classifier of
inanimates and also the base of the classifiers of the vigesimal powers. [arcos-lopez-2009]
identifies at least 180 classifiers; those below are the common ones of
[little-moroney-royer-2022]'s table of Ch'ol classifiers.

## Main definitions

* `Chol.Classifiers.classifiers` — the classifiers entered here.

## References

* [little-moroney-royer-2022]
* [bale-coon-2014]
* [bale-et-al-2019]
* [arcos-lopez-2009]
-/

@[expose] public section

namespace Chol.Classifiers

/-- *-p'ej*, the general classifier of inanimates: *ux-p'ej juñ* 'three books'. -/
def pej : Classifier := { toMorph := .suff "p'ej" }

/-- *-kojty*, animals, from the positional root *koty* 'standing on four legs': *ux-kojty mis*
'three cats'. -/
def kojty : Classifier := { toMorph := .suff "kojty" }

/-- *-tyikil*, people: *ux-tyikil x'ixik* 'three women'. -/
def tyikil : Classifier := { toMorph := .suff "tyikil" }

/-- *-k'ej*, flat round objects: *ux-k'ej waj* 'three tortillas'. -/
def kej : Classifier := { toMorph := .suff "k'ej" }

/-- *-ts'ijty*, long things: *ux-ts'ijty tye'* 'three trees'. -/
def tsijty : Classifier := { toMorph := .suff "ts'ijty" }

/-- *-bujch*, things seated or propped up, from the positional root *buch* 'seated': *ux-bujch
bux* 'three propped-up bottles'. -/
def bujch : Classifier := { toMorph := .suff "bujch" }

/-- The classifiers. -/
def classifiers : Finset Classifier := {pej, kojty, tyikil, kej, tsijty, bujch}

end Chol.Classifiers
