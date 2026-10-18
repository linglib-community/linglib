module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Realization
public import Linglib.Semantics.Root.Kinds
public import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Allosemy

Allosemy is contextual meaning variation of a single functional head —
the LF analogue of allomorphy. The heads v, n, and Voice each carry
several allosemes, selected by the syntactic context rather than tracked
by morphosyntactic features, and the ambiguity of deverbal
nominalizations between event, result, state, entity, and content
readings is the visible trace of that selection. The reading typology
`readingFromAllosemes` is grounded in typed denotations in
`Studies/Benz2025.lean`, where it is shown to track definedness.

## Main definitions

* `Alloseme` — the inventory carrier: contentful allosemes with the
  zero alloseme adjoined (`Option`, in the `WithZero` pattern)
* `Verbalizer.Alloseme`, `Nominalizer.Alloseme`, `Voice.Alloseme` —
  each head's inventory under its own API, from its `Contentful` type;
  Voice's expletive is the shared zero
* `Verbalizer.vocabulary`, `Nominalizer.vocabulary`,
  `Voice.vocabulary` — each head's List-3 vocabulary over the shared
  selection engine
* `NominalizationReading`, `readingFromAllosemes` — the reading typology
  of deverbal nominalizations and its alloseme table

## Main statements

* `Voice.theta_consistent` — a Voice alloseme assigns a θ-role iff its
  syntactic flavor does
* `Verbalizer.isAllosemous` — v's contextual meaning variation on the
  shared `Realization.Interpreted` carrier

## Implementation notes

An alloseme is a `VocabularyItem` whose exponent is a denotation, so DM's
List 2 (form) and List 3 (meaning) run on one selection engine
(`subsetPrinciple`, `winner?_isElsewhereWinner`); its specification
conditions on the neighboring terminals, not on features of its own head.
`Voice.Alloseme.fromComplement` is a worked List-3 competition on that
engine; `readingFromAllosemes` is a different object — the composition of
two already-selected allosemes.
Existing infrastructure this module retroactively classifies as
allosemy: `Minimalist.Voice.Flavor` (Voice) and root change-type
conditioning of v.

## References

* [I. Benz, *Structure and interpretation across categories*][benz-2025]
* [J. Wood, *Icelandic nominalizations and allosemy*][wood-2023]
* [A. Kratzer, *Severing the external argument from its verb*][kratzer-1996]
* [N. Myler, *Building and interpreting possession sentences*][myler-2016]
* [L. J. Adamson, *Gender assignment is local*][adamson-2024]
* [J. Beavers et al., *States and changes of state*][beavers-etal-2021]
-/

@[expose] public section

namespace DistributedMorphology.Allosemy

open Minimalist.Voice (Head)
open Morphology.Exponence

/-! ### The alloseme carrier

Every head's inventory contains the zero alloseme trivially, so an
inventory is the head's contentful allosemes with a zero adjoined:
`Option`, in the `WithZero` pattern, with `none` the zero alloseme. Each
head contributes only its `Contentful` type. -/

/-- The allosemes of a head whose contentful allosemes are `C`, with the zero alloseme (Benz's Ø)
as `0`. -/
def Alloseme (C : Type*) : Type _ := WithZero C

namespace Alloseme

variable {C : Type*}

/-- The zero alloseme, semantically Ø. -/
@[match_pattern] def zero : Alloseme C := none

/-- A contentful alloseme. -/
@[match_pattern] def of (c : C) : Alloseme C := some c

instance [DecidableEq C] : DecidableEq (Alloseme C) :=
  inferInstanceAs (DecidableEq (Option C))

instance [Repr C] : Repr (Alloseme C) := inferInstanceAs (Repr (Option C))

instance [Fintype C] : Fintype (Alloseme C) :=
  inferInstanceAs (Fintype (Option C))

instance : Zero (Alloseme C) := inferInstanceAs (Zero (WithZero C))

end Alloseme

/-! ### v allosemy -/

/-- The contentful alloseme of v, which introduces the event variable and the Theme
requirement. -/
inductive Verbalizer.Contentful where
  | eventive
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of v. A nominalization is eventive when v is interpreted and n vacuous, and
referential when n is interpreted and v vacuous, as with *observation*. -/
abbrev Verbalizer.Alloseme := Allosemy.Alloseme Verbalizer.Contentful

namespace Verbalizer.Alloseme

/-- v interpreted as in the verbal domain (CEN contexts). -/
@[match_pattern] def eventive : Verbalizer.Alloseme :=
  Allosemy.Alloseme.of .eventive

/-- Semantically Ø (SEN/RN contexts). -/
@[match_pattern] def zero : Verbalizer.Alloseme := Allosemy.Alloseme.zero

end Verbalizer.Alloseme

/-- Does this v alloseme introduce an event variable? -/
def Verbalizer.Alloseme.introducesEvent : Verbalizer.Alloseme → Bool
  | .eventive => true
  | .zero     => false

/-! ### Allosemic entries

An alloseme is a Vocabulary Item whose exponent is a denotation. Its
specification mentions no feature of its own head — the vocabulary is the
head's — and conditions on the neighbors: the complement below, toward the
root, and the embedding head above — allosemy is conditioned by the
interpreted domain below and the features of the next head above. The
locality of the conditioning — the first category head's
spell-out domain, across semantically null heads only — is `ComplexHead.Sees`
(`Locality.lean`). -/

/-- A condition an alloseme places on a neighbouring terminal, on its category or on whether it
denotes an event or a state. -/
inductive Feature where
  | cat (c : Categorizer)
  | eventive
  | stative
  deriving DecidableEq, Repr

/-- A specification on the complement, the terminal below the head. -/
def complement (fs : List Feature) : Neighborhood (List Feature) := ⟨[], [fs], []⟩

/-- A specification on the embedding head, the terminal above. -/
def embedding (fs : List Feature) : Neighborhood (List Feature) := ⟨[], [], [fs]⟩

/-- The denotations a vocabulary licenses in a context — the exponents of
its applicable entries. Ambiguity in a context is non-singleton licensing;
the canonical default among the licensed entries is the Elsewhere winner
(`winner?_isElsewhereWinner`). -/
def licensed {Sem : Type*} (v : RuleSet (VocabularyItem Feature Sem))
    (n : Neighborhood (List Feature)) : List Sem :=
  (v.applicable n).map (·.exponent)

/-- The alloseme vocabulary of v. The eventive alloseme requires an eventive complement and the
zero alloseme is the elsewhere case. -/
def Verbalizer.vocabulary : RuleSet (VocabularyItem Feature Verbalizer.Alloseme) :=
  [⟨(complement [.eventive]).toFinset, .eventive⟩, ∅ ⟷ .zero]

/-- Root change-type conditions v alloseme selection: result roots,
    which entail a prior change, demand the event variable; property
    concept roots do not — the root typology feeding v allosemy. -/
def Verbalizer.Alloseme.fromRootType : Semantics.Root.ChangeType → Verbalizer.Alloseme
  | .result          => .eventive
  | .propertyConcept => .zero

/-- v is eventive iff the root entails change. -/
theorem Verbalizer.fromRootType_eventive_iff (rt : Semantics.Root.ChangeType) :
    (Verbalizer.Alloseme.fromRootType rt).introducesEvent = true ↔ rt = .result := by
  cases rt <;> decide

/-! ### n allosemy -/

/-- The contentful allosemes of n. The relational, sortal and alienator allosemes attach to
roots; the deverbal ones have their denotations in `Studies/Benz2025.lean`. -/
inductive Nominalizer.Contentful where
  | relational    -- introduces a relation (body-part-of)
  | sortal        -- bare categorization
  | alienator     -- existentially closes a possessor
  | content       -- propositional content (CCN reading)
  | simpleEvent   -- picks out entities equal to an event (SEN)
  | result        -- picks out the entity an event produced
  | state         -- picks out states
  | entity        -- picks out entities, no event connection
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of n. -/
abbrev Nominalizer.Alloseme := Allosemy.Alloseme Nominalizer.Contentful

namespace Nominalizer.Alloseme

@[match_pattern] def relational : Nominalizer.Alloseme := Allosemy.Alloseme.of .relational
@[match_pattern] def sortal : Nominalizer.Alloseme := Allosemy.Alloseme.of .sortal
@[match_pattern] def alienator : Nominalizer.Alloseme := Allosemy.Alloseme.of .alienator
@[match_pattern] def content : Nominalizer.Alloseme := Allosemy.Alloseme.of .content
@[match_pattern] def simpleEvent : Nominalizer.Alloseme := Allosemy.Alloseme.of .simpleEvent
@[match_pattern] def result : Nominalizer.Alloseme := Allosemy.Alloseme.of .result
@[match_pattern] def state : Nominalizer.Alloseme := Allosemy.Alloseme.of .state
@[match_pattern] def entity : Nominalizer.Alloseme := Allosemy.Alloseme.of .entity

/-- The zero alloseme of n, under which the noun inherits the verb meaning (CEN). -/
@[match_pattern] def zero : Nominalizer.Alloseme := Allosemy.Alloseme.zero

end Nominalizer.Alloseme

/-- The alloseme vocabulary of n. The deverbal allosemes require a verbal complement, the CEN and
result allosemes an eventive one, and the others are unconditioned. -/
def Nominalizer.vocabulary : RuleSet (VocabularyItem Feature Nominalizer.Alloseme) :=
  [∅ ⟷ .relational, ∅ ⟷ .sortal, ∅ ⟷ .alienator,
    ⟨(complement [.cat .v]).toFinset, .content⟩,
    ⟨(complement [.cat .v, .eventive]).toFinset, .zero⟩,
    ⟨(complement [.cat .v]).toFinset, .simpleEvent⟩,
    ⟨(complement [.cat .v, .eventive]).toFinset, .result⟩,
    ⟨(complement [.cat .v]).toFinset, .state⟩,
    ⟨(complement [.cat .v]).toFinset, .entity⟩]

/-! ### Voice allosemy -/

/-- The θ-assigning allosemes of Voice. The complement fixes the role, since the holder cannot
combine with an action predicate nor the agent with a stative one. -/
inductive Voice.Contentful where
  | agent     -- combines with dynamic action complements
  | holder    -- combines with stative complements
  | engineer  -- ECM *have*: saturated eventive VoiceP complement
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of Voice. The zero alloseme is the expletive of relational and light-verb
*have*. -/
abbrev Voice.Alloseme := Allosemy.Alloseme Voice.Contentful

namespace Voice.Alloseme

@[match_pattern] def agent : Voice.Alloseme := Allosemy.Alloseme.of .agent
@[match_pattern] def holder : Voice.Alloseme := Allosemy.Alloseme.of .holder
@[match_pattern] def engineer : Voice.Alloseme := Allosemy.Alloseme.of .engineer

/-- The zero alloseme of Voice, which assigns no θ-role. -/
@[match_pattern] def expletive : Voice.Alloseme := Allosemy.Alloseme.zero

end Voice.Alloseme

/-- The alloseme assigns a thematic role to the external argument;
only the expletive identity does not. -/
def Voice.Alloseme.AssignsTheta (a : Voice.Alloseme) : Prop :=
  a ≠ .expletive

instance : DecidablePred Voice.Alloseme.AssignsTheta :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The alloseme vocabulary of Voice. The engineer takes a saturated eventive complement, the
holder a stative one, and the expletive is the elsewhere case. -/
def Voice.vocabulary : RuleSet (VocabularyItem Feature Voice.Alloseme) :=
  [⟨(complement [.cat .v, .eventive]).toFinset, .engineer⟩,
    ⟨(complement [.stative]).toFinset, .holder⟩, ∅ ⟷ .expletive]

/-- The Voice alloseme selected from `Voice.vocabulary` by the complement's features. -/
def Voice.Alloseme.fromComplement (fs : List Feature) : Voice.Alloseme :=
  (subsetPrinciple Voice.vocabulary (complement fs)).getD .expletive

/-- Eventive-VoiceP complement selects engineer. -/
example : Voice.Alloseme.fromComplement [.cat .v, .eventive] = .engineer := by decide

/-- Stative complement selects holder. -/
example : Voice.Alloseme.fromComplement [.stative] = .holder := by decide

/-- Neither condition met selects the elsewhere expletive. -/
example : Voice.Alloseme.fromComplement [] = .expletive := by decide

/-- Bridge to the syntactic Voice heads. Syntactically all four allosemes realize an
    active Voice with a DP specifier; the θ-role distinction is resolved at LF. The
    map picks the head matching each alloseme's syntactic behavior. -/
def Voice.Alloseme.toHead : Voice.Alloseme → Head
  | .agent    => Minimalist.Voice.agentive
  | .holder   => Minimalist.Voice.experiencer
  | .engineer => Minimalist.Voice.agentive
  | .expletive => Minimalist.Voice.anticausative

/-- The bridge respects θ-assignment: an alloseme assigns a thematic
    role iff its syntactic head does. -/
theorem Voice.theta_consistent (a : Voice.Alloseme) :
    a.AssignsTheta ↔ a.toHead.AssignsTheta := by
  revert a; decide

/-! ### Nominalization readings -/

/-- The readings of a deverbal nominalization. -/
inductive NominalizationReading where
  | complexEvent   -- CEN: full verbal event reading with argument structure
  | simpleEvent    -- SEN: event reading without argument structure
  | result         -- entity whose existence results from an event
  | simpleState    -- state reading
  | simpleEntity   -- entity reading, no event connection
  | content        -- CCN: propositional content, takes a CP complement
  deriving DecidableEq, Repr, Fintype

/-- The reading of a nominalization from the allosemes of v and n. The CEN
pairs eventive v with zero n, the noun inheriting the verb meaning; the
simple readings pair zero v with the event, state, and entity allosemes of
n. The result and content readings admit both derivations — v vacuous, or
the eventive component from v — and the choice is immaterial for what the
nominal describes (`Benz2025.result_options_pred_agree`,
`Benz2025.content_options_agree`); content needs no verbal source at all.
The non-deverbal allosemes yield no nominalization reading: their
semantics is the relationalizer and the closure of its possessor slot. -/
def readingFromAllosemes : Verbalizer.Alloseme → Nominalizer.Alloseme → Option NominalizationReading
  | .eventive, .zero        => some .complexEvent
  | .eventive, .result      => some .result   -- both-heads-interpreted option
  | .eventive, .content     => some .content  -- both-heads-interpreted option
  | .zero,     .simpleEvent => some .simpleEvent
  | .zero,     .state       => some .simpleState
  | .zero,     .entity      => some .simpleEntity
  | .zero,     .result      => some .result   -- v-vacuous option
  | .zero,     .content     => some .content  -- v-vacuous option
  | _,         .sortal      => none
  | _,         .relational  => none
  | _,         .alienator   => none
  | .zero,     .zero        => none
  | .eventive, .simpleEvent => none
  | .eventive, .state       => none
  | .eventive, .entity      => none

/-! ### The `Realization.Interpreted` view

An allosemic head is a List-3 object: a single morpheme whose
interpretation is resolved in context by the shared exponence engine.
`Realization.Interpreted` is exactly that carrier — an opaque index with
a contextual `interp` map — with an empty List-2 form side, since
allosemy is meaning-only. Contextual meaning variation, Benz's core
claim that allosemy is allomorphy's LF analogue, is then literally
`Realization.Interpreted.IsAllosemous`. -/

/-- The allosemy engine as a `Realization.Interpreted` view, whose one head is interpreted as the
alloseme the Subset Principle picks. -/
def toInterpreted {Sem : Type} (v : RuleSet (VocabularyItem Feature Sem)) :
    Morphology.Realization.Interpreted Unit (Neighborhood (List Feature)) Unit Sem where
  realize _ _ := ∅
  interp _ n := (subsetPrinciple v n).elim ∅ ({·})

/-- The verbal categorizer is allosemous, eventive under an eventive complement and zero
elsewhere. -/
theorem Verbalizer.isAllosemous :
    (toInterpreted Verbalizer.vocabulary).IsAllosemous () :=
  ⟨complement [.eventive], ∅, .eventive, by decide, .zero, by decide, by decide⟩

end DistributedMorphology.Allosemy
