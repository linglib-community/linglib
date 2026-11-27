module

public import Linglib.Syntax.Category.Classifier.Basic
public import Mathlib.Data.Finset.Insert

/-!
# Shan numeral classifiers

A Shan noun is counted through a classifier, a free morpheme after the numeral in the order
noun–numeral–classifier: *mǎa sǎam tǒ* 'three dogs'. The classifier is chosen by the noun, and
the classifiers are nominal in origin: *tǒ* for animals is also the noun 'body', and *ton* for
plants is the head of the compound *ton-mâj* 'tree', which it counts. The classifier also
appears with the interrogative numeral *lǎaj* 'how many', the quantifier *ku* 'every',
demonstratives and relative clauses, though not with every expression of quantity: *nǎm* 'many,
much' takes none. *ʔǎn* is the general classifier of inanimates. The basic classifiers below are
those of Little, Moroney and Royer's table of Shan classifiers, after Moroney's.

## Main definitions

* `Shan.Classifiers.classifiers`: the classifiers entered here.

## References

* [little-moroney-royer-2022]
* [moroney-2021]
-/

@[expose] public section

namespace Shan.Classifiers

/-- *ʔǎn*, the general classifier of inanimates, as in *tsɔ̂ sǎam ʔǎn* 'three spoons'. -/
def an : Classifier := { toMorph := .free "ʔǎn" }

/-- *tǒ*, for animals and also the noun 'body', as in *mɛ́w sǎam tǒ* 'three cats'. -/
def «to» : Classifier := { toMorph := .free "tǒ" }

/-- *kɔ̂*, for people, as in *kón sǎam kɔ̂* 'three people'. -/
def ko : Classifier := { toMorph := .free "kɔ̂" }

/-- *hòj*, for round objects, as in *màak-khɔ̌ sǎam hòj* 'three jujubes'. -/
def hoj : Classifier := { toMorph := .free "hòj" }

/-- *ton*, for plants and trees and the head of *ton-mâj* 'tree', as in *ton-mâj sǎam ton*
'three trees'. -/
def ton : Classifier := { toMorph := .free "ton" }

/-- *lǎŋ*, for buildings, as in *hɤ́n sǎam lǎŋ* 'three houses'. -/
def lang : Classifier := { toMorph := .free "lǎŋ" }

/-- The classifiers. -/
def classifiers : Finset Classifier := {an, «to», ko, hoj, ton, lang}

end Shan.Classifiers
