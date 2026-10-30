module

public import Linglib.Semantics.Degree.Antonymy

/-!
# Attitude predicates: the classification

This file is the root of the attitude API: the semantic classification a clause-embedding
predicate's lexical entry records, from which its combinatorial properties are derived. A
doxastic predicate is veridical or not, the classical cut between *know* and *believe*
(`Doxastic.Veridicality`); Karttunen's finer split of the factives into full and semi-factives is
`Factivity`, on the presupposition facet. A preferential predicate has the evaluative valence of
a gradable predicate, positive for *hope* and negative for *fear*, and is clausally distributive
or not. Villalta's degree comparison relates its subject to a question exactly when it relates
her to some answer, while *worry*, Mandarin *qidai* and *care* relate her to the question itself
and can hold of no particular answer. `Attitude` composes the two dimensions: verb entries
record one, and the veridicality label records `Doxastic.DoxasticPredicate.IsVeridical`.

## Implementation notes

The binary cut between veridical and non-veridical is the classical default; Giannakidou's
three-way veridical, nonveridical, and antiveridical taxonomy and finer attitude typologies such
as Anand and Hacquard's cut the space differently. Clausal distributivity is recorded, as in Qing
and Uegaki's classification, rather than derived, since the non-distributive predicates share no
denotation. Speech-act predicates are outside the classification.

## References

* [karttunen-1971b]
* [villalta-2008]
* [anand-hacquard-2013]
* [elliott-etal-2017]
* [giannakidou-1998]
* [qing-uegaki-2025]
* [hintikka-1962]
-/

@[expose] public section

/-- A doxastic predicate is veridical when it entails its complement, as *know* and *discover* do
and *believe* and *think* do not. -/
inductive Doxastic.Veridicality
  | veridical
  | nonVeridical
  deriving DecidableEq, Repr

/-- An attitude predicate is doxastic, with an accessibility semantics ([hintikka-1962]) and a
veridicality, or preferential, with an evaluative valence and a record of whether it is clausally
distributive in the sense of `Distributivity.IsDistributive`, as the degree comparisons are
(`Preferential.isDistributive_degreeComparison`) and *worry* is not. -/
inductive Attitude
  | doxastic (veridicality : Doxastic.Veridicality)
  | preferential (valence : Degree.EvaluativeValence) (distributive : Bool)
  deriving DecidableEq, Repr

namespace Attitude

/-- The veridicality of a predicate; preferential predicates are non-veridical. -/
def veridicality : Attitude → Doxastic.Veridicality
  | .doxastic v => v
  | .preferential _ _ => .nonVeridical

/-- The attitude is preferential. -/
def IsPreferential : Attitude → Prop
  | .doxastic _ => False
  | .preferential _ _ => True

instance : DecidablePred IsPreferential
  | .doxastic _ => isFalse id
  | .preferential _ _ => isTrue trivial

/-- The valence of a preferential predicate. -/
def valence : Attitude → Option Degree.EvaluativeValence
  | .doxastic _ => none
  | .preferential v _ => some v

end Attitude
