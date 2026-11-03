module

public import Linglib.Logic.Natural.ImplicationSignature
public import Linglib.Logic.Natural.ProjectivitySignature
public import Linglib.Semantics.Attitudes.Basic
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# Clause-embedding predicates

A predicate that embeds a clause has properties that concern its complement and do not depend on
its word class, as *know*, *be aware* and the rest of Noonan's complement-taking predicates show:
its factivity, the implication signature saying what it implies about the complement in positive
and negative contexts, the attitude it expresses, whether it makes the complement opaque, and its
monotonicity in the complement. A frame can override them for one complement
(`Clause.Embedding.Reading`). A verb or an adjective carries them by extending `Clause.Embedding`,
and a predicate that embeds no clause has the default values.

## Implementation notes

Whether such a predicate triggers a presupposition is derived, not recorded. A factive presupposes
its complement, and an implicative presupposes that what it asserts is a condition for its
complement (`Implicative.sentence`); veridicality is an entailment and does not make a predicate
factive.

## References

* [noonan-2007]
* [karttunen-1971]
* [karttunen-1971b]
* [nairn-condoravdi-karttunen-2006]
* [bondarenko-2022]
* [wurmbrand-lohninger-2023]
* [hintikka-1962]
* [heim-1992]
-/

@[expose] public section

open NaturalLogic (ImplicationSignature ProjectivitySignature)

namespace Clause.Embedding

/-- A frame-conditioned reading of a predicate ([bondarenko-2022] §4.4.3 *hanaxa*; Greek
*thimame*) overrides the lexeme-level attitude, factivity and opacity for its frame (`none`
inherits the lexeme's) and records the sort of the frame's complement. -/
structure Reading where
  /-- The reading applies to every frame of the predicate refining this one, in the refinement
  order on `ArgumentFrame`. -/
  frame : ArgumentFrame
  /-- Frame-conditioned attitude override. -/
  attitude : Option Attitude := none
  /-- Frame-conditioned opacity override. -/
  opaqueContext : Option Bool := none
  /-- Frame-conditioned factivity override. -/
  factivity : Option Presupposition.Factivity := none
  /-- The semantic sort of the complement on this frame ([wurmbrand-lohninger-2023]). -/
  size : Option Size := none
  deriving DecidableEq, Repr

end Clause.Embedding

namespace Clause

/-- What a predicate does with a clausal complement. -/
structure Embedding where
  /-- The [karttunen-1971b] factivity class of a factive predicate; `none` for a non-factive. -/
  factivity : Option Presupposition.Factivity := none
  /-- The [nairn-condoravdi-karttunen-2006] implication signature of the predicate, the polarity
  of the complement it implies in a positive and in a negative context; `⊥` for a predicate that
  implies nothing. -/
  implicative : ImplicationSignature := ⊥
  /-- Does the predicate create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- The attitude the predicate expresses, doxastic or preferential, if it is an attitude
  predicate. -/
  attitude : Option Attitude := none
  /-- The frame-conditioned readings ([bondarenko-2022] §4.4.3), per-frame attitude and opacity
  overrides keyed to the predicate's frames. -/
  readings : List Embedding.Reading := []
  /-- Entailment signature of the complement position, the predicate's monotonicity with respect
  to its clausal complement. `.mono` is upward monotone, the report closed under entailment of the
  complement, as in Hintikka-style doxastic semantics ([hintikka-1962]). Set only where the
  classification is textbook consensus (believe, think, know); preferential attitudes (want, hope)
  are contested ([heim-1992]) and stay `none`. -/
  complementSig : Option ProjectivitySignature := none
  deriving Repr, BEq

namespace Embedding

/-- The predicate is factive when it carries a [karttunen-1971b] factivity class. -/
def IsFactive (e : Embedding) : Prop := e.factivity ≠ none

instance : DecidablePred IsFactive := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The predicate triggers a presupposition about its complement when it is factive or
implicative. -/
def IsTrigger (e : Embedding) : Prop := e.IsFactive ∨ e.implicative ≠ ⊥

instance : DecidablePred IsTrigger := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The reading keyed to frame `fr` is the first whose frame `fr` refines. -/
def reading? (e : Embedding) (fr : ArgumentFrame) : Option Reading :=
  e.readings.find? fun r ↦ decide (r.frame ≤ fr)

/-- The effective attitude on frame `fr` is the reading's override, else the lexeme's default. -/
def attitudeOn (e : Embedding) (fr : ArgumentFrame) : Option Attitude :=
  ((e.reading? fr).bind (·.attitude)).orElse fun _ ↦ e.attitude

/-- The effective factivity on frame `fr` is the reading's override, else the lexeme's default. -/
def factivityOn (e : Embedding) (fr : ArgumentFrame) : Option Presupposition.Factivity :=
  ((e.reading? fr).bind (·.factivity)).orElse fun _ ↦ e.factivity

end Embedding

end Clause
