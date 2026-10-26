module

public import Mathlib.Data.Finset.Basic

/-!
# Dialogue gameboards

This file defines the dialogue gameboard of Ginzburg's theory of dialogue, KoS, and the records
it holds. A dialogue gameboard is one participant's view of the public state of a conversation:
who holds the turn and whom they address, the facts accepted so far, the moves made, the
utterances not yet grounded, and the questions under discussion. An utterance is recorded as a
locutionary proposition, which keeps its phonological form, category, contextual parameters and
sub-utterances beside its content, so that a clarification request can target any part of its
form, as Ginzburg and Cooper argue. A question under discussion carries the sub-utterances that
established it, which a fragment resolving the question must match.

The types a gameboard is built from form a domain: the grammatical domain of forms, categories,
parameter labels and sub-utterance denotations, extended by participants, facts, questions and
utterance contents. A question may mention sub-utterances, as the question of what a speaker
meant by one does, so the grammatical domain comes first.

## Main definitions

* `Discourse.GrammaticalDomain`, `Discourse.Gameboard.Domain`: the types gameboards are built
  from.
* `Discourse.IllocutionaryAct`: an illocutionary relation applied to its content.
* `Discourse.SubUtterance`, `Discourse.LocutionaryProposition`: sub-utterances and utterances.
* `Discourse.InformationStructure`: a question with its focus-establishing constituents.
* `Discourse.Gameboard`: the dialogue gameboard.

## Implementation notes

* A domain bundles decidable equality of its types, as `CategoryTheory.Bundled` bundles a
  structure with its carrier, so that the records derive decidable equality and gameboards can
  be computed with.
* A locutionary proposition records the utterance's values as fields, Ginzburg's single type
  notation, rather than as an Austinian proposition pairing the utterance with its type.
* A contextual parameter is its label; the restriction on its value is not represented, and
  sub-utterances do not record their own parameters.
* The gameboard omits the utterance time and the addressing condition, and `non-resolve-cond` is
  the predicate `Discourse.Gameboard.NonResolveCond` of `Gameboard/Basic.lean`.

## References

* [ginzburg-2012]
* [ginzburg-cooper-2004]
* [ginzburg-sag-2000]
-/

@[expose] public section

universe u

namespace Discourse

/-- The grammatical domain of a gameboard ([ginzburg-2012] Appendix C) supplies the phonological
forms, syntactic categories and contextual-parameter labels of signs, and the denotations of
sub-utterances, each with decidable equality. -/
structure GrammaticalDomain : Type (u + 1) where
  /-- Phonological forms. -/
  Form : Type u
  /-- Syntactic categories. -/
  Category : Type u
  /-- Labels of contextual parameters. -/
  Label : Type u
  /-- Denotations of sub-utterances. -/
  Denotation : Type u
  [decEqForm : DecidableEq Form]
  [decEqCategory : DecidableEq Category]
  [decEqLabel : DecidableEq Label]
  [decEqDenotation : DecidableEq Denotation]

attribute [instance] GrammaticalDomain.decEqForm GrammaticalDomain.decEqCategory
  GrammaticalDomain.decEqLabel GrammaticalDomain.decEqDenotation

/-- The domain of a gameboard extends a grammatical domain with the participants, facts,
questions and utterance contents of [ginzburg-2012] Appendix A, each with decidable equality. -/
structure Gameboard.Domain extends GrammaticalDomain.{u} where
  /-- Participants. -/
  Participant : Type u
  /-- Facts. -/
  Fact : Type u
  /-- Questions. -/
  Question : Type u
  /-- Contents of utterances. -/
  Content : Type u
  [decEqParticipant : DecidableEq Participant]
  [decEqFact : DecidableEq Fact]
  [decEqQuestion : DecidableEq Question]
  [decEqContent : DecidableEq Content]

attribute [instance] Gameboard.Domain.decEqParticipant Gameboard.Domain.decEqFact
  Gameboard.Domain.decEqQuestion Gameboard.Domain.decEqContent

/-- An illocutionary act is the illocutionary relation of an illocutionary proposition applied
to its content ([ginzburg-2012] (8c) p. 361), without the speaker and addressee that the
proposition also records. The inventory is that of the rules of Ch. 4 less parting and
counter-parting. -/
inductive IllocutionaryAct (Fact Question : Type*) where
  /-- Asserting a fact. -/
  | assert : Fact → IllocutionaryAct Fact Question
  /-- Asking a question. -/
  | ask : Question → IllocutionaryAct Fact Question
  /-- Accepting an assertion. -/
  | accept : Fact → IllocutionaryAct Fact Question
  /-- Asking for confirmation of an assertion. -/
  | check : Fact → IllocutionaryAct Fact Question
  /-- Confirming in response to a check. -/
  | confirm : Fact → IllocutionaryAct Fact Question
  /-- Greeting. -/
  | greet : IllocutionaryAct Fact Question
  /-- Counter-greeting. -/
  | counterGreet : IllocutionaryAct Fact Question
  deriving Repr, DecidableEq

variable (G : GrammaticalDomain.{u})

/-- A sub-utterance carries a phonological form, a category and a denotation, which make any
constituent of an utterance clarifiable, the fractal heterogeneity of
[ginzburg-cooper-2004]. -/
structure SubUtterance where
  /-- The phonological form. -/
  form : G.Form
  /-- The syntactic category. -/
  category : G.Category
  /-- The denotation, which for a sub-utterance contributing a contextual parameter is its label. -/
  denotation : G.Denotation
  deriving DecidableEq

/-- A locutionary proposition records an utterance with its phonological form, category,
content, contextual parameters and constituents ([ginzburg-2012] pp. 172–174), so that a
clarification request can target the form of the utterance and any of its constituents, not
only its content. The fields are the single-type notation of (42) p. 174; the Austinian
proposition `[sit = u, sit-type = Tᵤ]` of (41) p. 173 and Appendix A (8d) p. 362 is not
represented. -/
structure LocutionaryProposition (Content : Type u) where
  /-- The phonological form. -/
  form : G.Form
  /-- The syntactic category. -/
  category : G.Category
  /-- The content. -/
  content : Content
  /-- The labels of the contextual parameters, which grounding must witness; like SLASH they are
  pooled from the words of the utterance ([ginzburg-cooper-2004] (29)). The restrictions on
  their values, the RESTR of (28), are not represented. -/
  parameters : Finset G.Label := ∅
  /-- The sub-utterances, the utterance itself among them as in (42) p. 174, listed rather than
  computed from the daughters by the CONSTITS Amalgamation Constraint of
  [ginzburg-cooper-2004] (30). -/
  constituents : Finset (SubUtterance G) := ∅
  deriving DecidableEq

/-- An information structure pairs a question under discussion with its focus-establishing
constituents, the sub-utterances a fragment resolving the question must match in category
([ginzburg-2012] p. 239 and (9) p. 362). The focus-establishing constituent of a wh-question is
its wh-phrase, and that of a clarification request the sub-utterance it clarifies; it replaces
the `sal-utt` of [ginzburg-sag-2000]. (9) types these constituents as locutionary propositions;
they are sub-utterances here because the rules that set them pick a constituent of an utterance
(p. 241, and Appendix B (26e) p. 374). -/
structure InformationStructure (Question : Type u) where
  /-- The question. -/
  question : Question
  /-- The focus-establishing constituents. -/
  focusEstablishing : Finset (SubUtterance G) := ∅
  deriving DecidableEq

/-- The dialogue gameboard of a participant is their public share of the conversational state
([ginzburg-2012] (43) p. 175); each participant has their own. Its moves and pending utterances
are locutionary propositions whose contents are the domain's, and its questions under discussion
are information structures (p. 239). With `IllocutionaryAct` contents it is the gameboard of
Ch. 4 ((100) p. 111), whose moves are illocutionary propositions. QUD is a partial order in
(43), here a list. -/
structure Gameboard (D : Gameboard.Domain.{u}) where
  /-- The speaker. -/
  speaker : D.Participant
  /-- The addressee. -/
  addressee : D.Participant
  /-- The commonly accepted facts. -/
  facts : Finset D.Fact := ∅
  /-- The moves made, LatestMove first. -/
  moves : List (LocutionaryProposition D.toGrammaticalDomain D.Content) := []
  /-- The utterances not yet grounded, MaxPending first. -/
  pending : List (LocutionaryProposition D.toGrammaticalDomain D.Content) := []
  /-- The questions under discussion, MaxQUD first. -/
  qud : List (InformationStructure D.toGrammaticalDomain D.Question) := []
  deriving DecidableEq

end Discourse
