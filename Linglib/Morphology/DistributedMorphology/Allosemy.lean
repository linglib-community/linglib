module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Realization
public import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Allosemy

Allosemy is contextual variation in the meaning of one functional head, the counterpart at LF of
allomorphy. Each of v, n and Voice has an inventory of allosemes, its contentful ones with a zero
adjoined (`Alloseme`), and a vocabulary that selects among them by the neighbouring terminals
rather than by features of the head itself. An alloseme is thus a `VocabularyItem` whose
exponent is a denotation, so that form and meaning run on one selection engine. The readings of
a deverbal nominalization are the compositions of an alloseme of v with one of n
(`readingFromAllosemes`), and the Voice allosemes map to the cells of `Minimalist.Voice.Head`
[preserving θ-assignment](##Voice.theta_consistent).

## References

* [benz-2025]
* [wood-2023]
* [kratzer-1996]
* [myler-2016]
* [adamson-2024]
-/

@[expose] public section

namespace DistributedMorphology.Allosemy

open Minimalist.Voice (Head)
open Morphology

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

/-- The alloseme introduces an event variable; only the zero alloseme does not. -/
def Verbalizer.Alloseme.IntroducesEvent (a : Verbalizer.Alloseme) : Prop :=
  a ≠ .zero

instance : DecidablePred Verbalizer.Alloseme.IntroducesEvent :=
  fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

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
  | cat (c : Minimalist.Cat)
  | eventive
  | stative
  deriving DecidableEq, Repr

/-- A specification on the complement, the terminal below the head. -/
def complement (fs : Finset Feature) : Neighborhood (Finset Feature) := ⟨∅, [fs], []⟩

/-- A specification on the embedding head, the terminal above. -/
def embedding (fs : Finset Feature) : Neighborhood (Finset Feature) := ⟨∅, [], [fs]⟩

/-- The denotations a vocabulary licenses in a context — the exponents of
its applicable entries. Ambiguity in a context is non-singleton licensing;
the canonical default among the licensed entries is the Elsewhere winner
(`winner?_isElsewhereWinner`). -/
def licensed {Sem : Type*} (v : RuleSet (VocabularyItem Feature Sem))
    (n : Neighborhood (Finset Feature)) : List Sem :=
  (v.applicable n).map (·.exponent)

/-- The alloseme vocabulary of v. The eventive alloseme requires an eventive complement and the
zero alloseme is the elsewhere case. -/
def Verbalizer.vocabulary : RuleSet (VocabularyItem Feature Verbalizer.Alloseme) :=
  [⟨(complement {.eventive}).toFinset, .eventive⟩, ∅ ⟷ .zero]

/-! ### n allosemy -/

/-- The contentful allosemes of n. The relational, sortal and alienator allosemes attach to
roots; the others are deverbal. -/
inductive Nominalizer.Contentful where
  /-- Introduces a relation, as with a body part. -/
  | relational
  /-- Bare categorization. -/
  | sortal
  /-- Existentially closes a possessor. -/
  | alienator
  /-- Propositional content, the reading of a content nominal. -/
  | content
  /-- Picks out the entities that are events, the reading of a simple event nominal. -/
  | simpleEvent
  /-- Picks out the entity an event produced. -/
  | result
  /-- Picks out states. -/
  | state
  /-- Picks out entities with no connection to an event. -/
  | entity
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
    ⟨(complement {.cat .v}).toFinset, .content⟩,
    ⟨(complement {.cat .v, .eventive}).toFinset, .zero⟩,
    ⟨(complement {.cat .v}).toFinset, .simpleEvent⟩,
    ⟨(complement {.cat .v, .eventive}).toFinset, .result⟩,
    ⟨(complement {.cat .v}).toFinset, .state⟩,
    ⟨(complement {.cat .v}).toFinset, .entity⟩]

/-! ### Voice allosemy -/

/-- The θ-assigning allosemes of Voice. The complement fixes the role, since the holder cannot
combine with an action predicate nor the agent with a stative one. -/
inductive Voice.Contentful where
  /-- Combines with a dynamic action complement. -/
  | agent
  /-- Combines with a stative complement. -/
  | holder
  /-- The Voice of ECM *have*, over a saturated eventive VoiceP complement. -/
  | engineer
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
  fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The alloseme vocabulary of Voice. The engineer takes a saturated eventive complement, the
holder a stative one, and the expletive is the elsewhere case. -/
def Voice.vocabulary : RuleSet (VocabularyItem Feature Voice.Alloseme) :=
  [⟨(complement {.cat .v, .eventive}).toFinset, .engineer⟩,
    ⟨(complement {.stative}).toFinset, .holder⟩, ∅ ⟷ .expletive]

/-- The Voice alloseme selected from `Voice.vocabulary` by the complement's features. -/
def Voice.Alloseme.fromComplement (fs : Finset Feature) : Voice.Alloseme :=
  (subsetPrinciple Voice.vocabulary (complement fs)).getD .expletive

/-- The syntactic Voice head of an alloseme. All four allosemes realize an active Voice with a DP
specifier, the θ-role distinction being resolved at LF, and the map picks the head matching each
alloseme's syntactic behavior. -/
def Voice.Alloseme.toHead : Voice.Alloseme → Head
  | .agent    => Minimalist.Voice.agentive
  | .holder   => Minimalist.Voice.experiencer
  | .engineer => Minimalist.Voice.agentive
  | .expletive => Minimalist.Voice.anticausative

/-- An alloseme assigns a thematic role iff its syntactic head does. -/
theorem Voice.theta_consistent (a : Voice.Alloseme) :
    a.AssignsTheta ↔ a.toHead.AssignsTheta := by
  revert a; decide

/-! ### Nominalization readings -/

/-- The readings of a deverbal nominalization. -/
inductive NominalizationReading where
  /-- The complex event reading, with the verb's event and its argument structure. -/
  | complexEvent
  /-- The simple event reading, an event without argument structure. -/
  | simpleEvent
  /-- An entity whose existence results from an event. -/
  | result
  /-- A state. -/
  | simpleState
  /-- An entity with no connection to an event. -/
  | simpleEntity
  /-- Propositional content, with a clausal complement. -/
  | content
  deriving DecidableEq, Repr, Fintype

/-- The reading of a nominalization from the allosemes of v and n. The complex event reading
pairs eventive v with zero n, the noun inheriting the verb meaning; the simple readings pair zero
v with the event, state, and entity allosemes of n. The result and content readings admit both
derivations, with v vacuous or contributing the eventive component. The non-deverbal allosemes
yield no nominalization reading: their semantics is the relationalizer and the closure of its
possessor slot. -/
def readingFromAllosemes : Verbalizer.Alloseme → Nominalizer.Alloseme → Option NominalizationReading
  | .eventive, .zero        => some .complexEvent
  | .eventive, .result      => some .result
  | .eventive, .content     => some .content
  | .zero,     .simpleEvent => some .simpleEvent
  | .zero,     .state       => some .simpleState
  | .zero,     .entity      => some .simpleEntity
  | .zero,     .result      => some .result
  | .zero,     .content     => some .content
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
a contextual realization `interp` by readings — with an empty List-2 form side, since
allosemy is meaning-only. Contextual meaning variation, Benz's core
claim that allosemy is allomorphy's LF analogue, is then literally
`Realization.Interpreted.IsAllosemous`. -/

/-- The allosemy engine as a `Realization.Interpreted` view, whose one head is interpreted as the
alloseme the Subset Principle picks. -/
def toInterpreted {Sem : Type} (v : RuleSet (VocabularyItem Feature Sem)) :
    Morphology.Realization.Interpreted Unit (Neighborhood (Finset Feature)) Unit Sem where
  realize _ _ := ∅
  interp := toRealization v fun _ n ↦ n

/-- The verbal categorizer is allosemous, eventive under an eventive complement and zero
elsewhere. -/
theorem Verbalizer.isAllosemous :
    (toInterpreted Verbalizer.vocabulary).IsAllosemous () :=
  Morphology.Realization.isSuppletive_of_mem (c := complement {.eventive}) (c' := ∅)
    (f := .eventive) (f' := .zero) (by decide) (by decide) (by decide)

end DistributedMorphology.Allosemy
