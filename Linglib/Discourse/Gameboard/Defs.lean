module

public import Mathlib.Data.Finset.Basic

/-!
# Dialogue gameboards

A dialogue gameboard is one participant's view of the public state of a conversation in
Ginzburg's theory of dialogue, KoS: who holds the turn and whom they address, the facts accepted
so far, the moves made, the utterances not yet grounded, and the questions under discussion. An
utterance is recorded as a `LocutionaryProposition`, which keeps its form, category, contextual
parameters and sub-utterances beside its content, so that a clarification request can target any
part of its form, as Ginzburg and Cooper argue. A question under discussion is recorded as an
`InformationStructure`, with the constituents that a fragment resolving the question must match.

## Implementation notes

* `Gameboard` takes the types of its utterances and of its questions under discussion as
  parameters, as `DFA` takes its alphabet and its states, rather than a bundle of the types its
  records are built from: turn taking and the updates of MOVES, PENDING and QUD read neither, and
  each operation of `Gameboard/Basic.lean` is stated for the gameboards whose entries it reads.
* A locutionary proposition records the utterance's values as fields, Ginzburg's single type
  notation, rather than as an Austinian proposition pairing the utterance with its type; its
  gaps and its question domain are not represented.
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

namespace Discourse

/-- A sub-utterance carries a phonological form, a category and a denotation, which make any
constituent of an utterance clarifiable, the fractal heterogeneity of
[ginzburg-cooper-2004]. -/
structure SubUtterance (Form Category Denotation : Type*) where
  /-- The phonological form. -/
  form : Form
  /-- The syntactic category. -/
  category : Category
  /-- The denotation, which for a sub-utterance contributing a contextual parameter is its label. -/
  denotation : Denotation
  deriving DecidableEq

/-- A locutionary proposition records an utterance with its phonological form, category,
content, contextual parameters and constituents ([ginzburg-2012] pp. 172–174), so that a
clarification request can target the form of the utterance and any of its constituents, not
only its content. The fields are the single-type notation of (42) p. 174; the Austinian
proposition `[sit = u, sit-type = Tᵤ]` of (41) p. 173 and Appendix A (8d) p. 362 is not
represented. -/
structure LocutionaryProposition (Form Category Label Denotation Content : Type*) where
  /-- The phonological form. -/
  form : Form
  /-- The syntactic category. -/
  category : Category
  /-- The content. -/
  content : Content
  /-- The labels of the contextual parameters, which grounding must witness; like SLASH they are
  pooled from the words of the utterance ([ginzburg-cooper-2004] (29)). The restrictions on
  their values, the RESTR of (28), are not represented. -/
  parameters : Finset Label := ∅
  /-- The sub-utterances, the utterance itself among them as in (42) p. 174, listed rather than
  computed from the daughters by the CONSTITS Amalgamation Constraint of
  [ginzburg-cooper-2004] (30). -/
  constituents : Finset (SubUtterance Form Category Denotation) := ∅
  deriving DecidableEq

/-- An information structure pairs a question under discussion with its focus-establishing
constituents, which a fragment resolving the question must match in category ([ginzburg-2012]
p. 239 and (9) p. 362). The focus-establishing constituent of a wh-question is its wh-phrase,
and that of a clarification request the sub-utterance it clarifies; it replaces the `sal-utt` of
[ginzburg-sag-2000]. (9) types these constituents as locutionary propositions; the rules that
set them pick a constituent of an utterance (p. 241, and Appendix B (26e) p. 374), so the
studies take them to be sub-utterances. -/
structure InformationStructure (Question Constituent : Type*) where
  /-- The question. -/
  question : Question
  /-- The focus-establishing constituents. -/
  focusEstablishing : Finset Constituent := ∅
  deriving DecidableEq

/-- The dialogue gameboard of a participant is their public share of the conversational state
([ginzburg-2012] (43) p. 175); each participant has their own. Its moves and pending utterances
are locutionary propositions in (43), and its questions under discussion are questions there and
information structures from p. 239 on. QUD is a partial order in (43), here a list. -/
structure Gameboard (Participant Fact Utterance Question : Type*) where
  /-- The speaker. -/
  speaker : Participant
  /-- The addressee. -/
  addressee : Participant
  /-- The commonly accepted facts. -/
  facts : Finset Fact := ∅
  /-- The moves made, LatestMove first. -/
  moves : List Utterance := []
  /-- The utterances not yet grounded, MaxPending first. -/
  pending : List Utterance := []
  /-- The questions under discussion, MaxQUD first. -/
  qud : List Question := []
  deriving DecidableEq

end Discourse
