module

public import Linglib.Semantics.EvaluativeValence
public import Linglib.Semantics.Presupposition.Trigger

/-!
# Attitude predicates: the classification

This file is the root of the attitude API: the semantic classification a clause-embedding
predicate's lexical entry records, from which its combinatorial properties are derived. A
doxastic predicate quantifies over epistemic or doxastic alternatives, Hintikka's knowledge and
belief (`Doxastic.Alternatives`); Karttunen's split of the factives into full and semi-factives is
`Factivity`, on the presupposition facet. The classical cut between *know* and *believe* is
derived from the two: a doxastic predicate is veridical when it is factive or its alternatives are
epistemic (`Attitude.IsVeridical`), exactly when every denotation of that kind is
(`Doxastic.isVeridical_forall_iff`). A preferential predicate has the evaluative valence of
a gradable predicate, positive for *hope* and negative for *fear*. `Attitude` composes the two
dimensions, and verb entries record one.

## Implementation notes

For a factive the factivity alone decides `IsVeridical`, so the alternatives of a factive entry do
not bear on its veridicality. Entries classify them by Hintikka's knowledge: a factive whose
meaning entails that the holder knows its complement, as *know*, *realize*, *discover*, *notice*,
*remember*, *forget* and *see* do, quantifies over epistemic alternatives.

The binary cut between veridical and non-veridical is the classical default; Giannakidou's
three-way veridical, nonveridical, and antiveridical taxonomy and finer attitude typologies such
as Anand and Hacquard's cut the space differently. Speech-act predicates are outside the
classification.

## References

* [karttunen-1971b]
* [anand-hacquard-2013]
* [giannakidou-1998]
* [hintikka-1962]
-/

@[expose] public section

/-- The alternatives a doxastic predicate quantifies over ([hintikka-1962]): the epistemic
alternatives of a holder, compatible with what she knows, among which the actual world always is,
or her doxastic alternatives, compatible with what she believes, among which it need not be. -/
inductive Doxastic.Alternatives
  | epistemic
  | doxastic
  deriving DecidableEq, Repr

/-- An attitude predicate is doxastic, with an accessibility semantics over its alternatives
([hintikka-1962]), or preferential, with an evaluative valence. -/
inductive Attitude
  | doxastic (alternatives : Doxastic.Alternatives)
  | preferential (valence : EvaluativeValence)
  deriving DecidableEq, Repr

namespace Attitude

/-- The attitude is doxastic and veridical, entailing its complement: a predicate of factivity
class `fac` is, when it is factive or quantifies over epistemic alternatives, as *know* and
*discover* do and *believe* and *think* do not. -/
def IsVeridical (fac : Option Presupposition.Factivity) : Attitude → Prop
  | .doxastic b => fac ≠ none ∨ b = .epistemic
  | .preferential _ => False

instance (fac : Option Presupposition.Factivity) : DecidablePred (IsVeridical fac)
  | .doxastic _ => inferInstanceAs (Decidable (_ ∨ _))
  | .preferential _ => isFalse id

/-- The attitude is preferential. -/
def IsPreferential : Attitude → Prop
  | .doxastic _ => False
  | .preferential _ => True

instance : DecidablePred IsPreferential
  | .doxastic _ => isFalse id
  | .preferential _ => isTrue trivial

/-- The valence of a preferential predicate. -/
def valence : Attitude → Option EvaluativeValence
  | .doxastic _ => none
  | .preferential v => some v

end Attitude
