/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Clause.Complementation
public import Linglib.Syntax.Clause.Embedding
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Syntax.Category.Verb.Diathesis
public import Linglib.Syntax.Voice.Defs
public import Linglib.Syntax.Obligatoriness
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Aspect.AspectualClass
public import Linglib.Semantics.Aspect.Viewpoint.Defs
public import Linglib.Syntax.Feature.Case.Spatial
public import Linglib.Semantics.Aspect.Phasal
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.Degree.Gradability
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Semantics.ArgumentStructure.Root.Basic
public import Linglib.Morphology.Morph

/-!
# Verb entries

A verb entry records what a grammar and a dictionary say of one verb: the morphs of its citation
form, its root, its valency, the auxiliaries of its perfect and the voices its grammar mentions,
the viewpoint, scale, direction of motion and phase it lexicalizes, and what it does with a
clausal complement. A language with verbal inflection extends `Verb` with its paradigm. The
classifications of an entry, unaccusative, factive, control verb and so on, are not recorded:
they are predicates the theories define on these fields.

## Main definitions

* `Verb`: the verb entry.
* `Verb.form`: the citation form.
* `Verb.changeScale`: the scale along which a degree achievement measures change.
* `Verb.TakesClausal`: some frame of the verb has a clausal position.
* `Verb.IsTrigger`: the verb triggers a presupposition by its complement or its phase.

## Implementation notes

* `Verb` extends `Clause.Embedding`, which adjectives extend too and which has lemmas of its own.
  Its other fields are flat: a group of fields with no declaration stated about the group is
  not a parent structure.
* The degree semantics of a verb is one optional `Gradability` and not a dimension with a pole
  and a standard beside it, so an entry without a scale records no pole.
* The citation form is the list `morphs`, and `Verb.form` is its surface string, so a language
  file builds a derived form, a converb or a causative, by attaching morphs to `v.morphs`.
* `Verb.voiceType` records whether the verb has an external argument where the linking rules of
  `Semantics/ArgumentStructure/Unaccusativity.lean` do not decide it from the other fields.

## References

* [dowty-1991]
* [grimm-2011]
* [levin-2019]
* [levin-hovav-1995]
* [noonan-2007]
* [pantcheva-2011]
* [roberts-simons-2024]
* [schwarzer-2026]
* [wood-2015]
-/

@[expose] public section

open Aspect ArgumentStructure
open Morphology (Morph)

/-! ### Selectional and inflectional enums -/

/-- What an entry records of the external argument of a verb. -/
inductive VoiceType where
  /-- An external argument is introduced, as in transitives and unergatives. -/
  | agentive
  /-- No external argument is introduced, as in unaccusatives and anticausatives. -/
  | nonThematic
  /-- An agent that binds the internal argument ([wood-2015]). -/
  | reflexive
  deriving DecidableEq, Repr

/-- The voice type introduces an external argument. -/
def VoiceType.AssignsTheta (vt : VoiceType) : Prop := vt = .agentive ∨ vt = .reflexive

instance : DecidablePred VoiceType.AssignsTheta := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The auxiliary of the perfect in a language that forms it with *be* or *have*, as Romance and
Germanic languages do. -/
inductive Verb.PerfectAuxiliary where
  /-- Italian *essere*, French *être*, German *sein*, Dutch *zijn*. -/
  | be
  /-- Italian *avere*, French *avoir*, German *haben*, Dutch *hebben*. -/
  | have
  deriving DecidableEq, Repr, Fintype

/-- The sense that distinguishes polysemous entries sharing a citation form, as *remember* the
implicative and *remember* the question-embedding factive. -/
inductive SenseTag where
  /-- The primary sense. -/
  | default
  /-- The question-embedding sense. -/
  | rogative
  /-- The causative use of an otherwise non-causative verb. -/
  | causative
  /-- The inchoative use of an otherwise non-inchoative verb, as Spanish *cortarse* 'snap' beside
  *cortar* 'cut'. -/
  | inchoative
  /-- The instrument-specific sense. -/
  | instrumental
  /-- The stative reading of a polysemous verb, as positional *suivre* 'follow'. -/
  | stative
  deriving DecidableEq, Repr

/-! ### The verb entry -/

/-- A verb entry is what a predicate does with a clausal complement (`Clause.Embedding`) together
with the verb's form, root, valency, and the aspectual and scalar properties it lexicalizes. -/
structure Verb extends Clause.Embedding where
  /-- The morphs of the citation form, in surface order, are the stem with the affixes and
  particles it is cited with. A citation form the entry does not analyse is a single root. -/
  morphs : List Morph
  /-- The spelling in the native script, where the morphs are a romanization. -/
  script : Option String := none
  /-- The sense, for entries that share a citation form. -/
  senseTag : SenseTag := .default
  /-- The kinds of lexical entailment the verb's root carries; the default is the unannotated
  root. -/
  root : ArgumentStructure.Root := {}
  /-- The verb's participants, with the proto-role entailment profiles the entry records for
  them ([dowty-1991], [grimm-2011], [levin-2019]), and its diatheses, the basic diathesis
  first; the default records no participant. An implicit argument is a frame position
  (`ArgumentFrame.objectDrop`). -/
  valency : Verb.Valency := .of []
  /-- Whether an external argument is introduced, where the entry records it. -/
  voiceType : Option VoiceType := none
  /-- The auxiliaries the verb forms its perfect with, as its grammar gives them, both where it
  gives both; empty where the language has no choice or the entry records none. -/
  perfectAuxiliaries : Finset Verb.PerfectAuxiliary := ∅
  /-- What the verb's grammar says of single voices for this verb: excluded, possible beside the
  basic construction, or the verb's only construction. A voice the grammar does not mention
  for the verb is absent. -/
  voices : List (Voice × Obligatoriness) := []
  /-- The viewpoint the stem lexicalizes, in a language that encodes the opposition of perfective
  and imperfective on verb stems, as the Slavic languages do, at its dictionary value; `none`
  where the language does not. -/
  perfectivity : Option Perfectivity := none
  /-- The degree semantics of a gradable verb: the dimension along which a degree achievement
  measures change and on which a gradable state such as *believe* measures its holder, with the
  pole measured towards, negative for *dry*, a decrease in wetness, and for *doubt*, the antonym
  of *believe*. -/
  gradability : Option Gradability := none
  /-- The direction of the path along which a verb of motion displaces its theme, relative to
  the ground ([pantcheva-2011]). It is `.goal` for *arrive* and *come*, `.source` for
  *leave*, and `.place` for a verb of manner of motion, which displaces its theme without a
  direction ([levin-hovav-1995] p. 147, *roll*, *walk*, *swim* against *arrive*, *come*,
  *fall*), and `none` for a verb that says nothing of its theme's path. -/
  direction : Option Locative.Direction := none
  /-- The phasal class of a phasal verb such as *stop*, *start* or *continue*. -/
  phasal : Option Phasal := none
  /-- The verb denotes the performance of an illocutionary act, as *say*, *tell*, *claim* and
  *ask* do. -/
  speechActVerb : Bool := false
  deriving DecidableEq

/-- The citation form of a verb is the surface form of its morphs, in boundary notation. -/
def Verb.form (v : Verb) : String := Morph.surface v.morphs

/-- The scale along which a degree achievement measures change is the scale of a verb that is not
a verb of attitude, since the scale of *believe* measures its holder's attitude and no change. -/
def Verb.changeScale (v : Verb) : Option Boundedness :=
  if v.attitude.isSome then none else v.gradability.map (·.boundedness)

/-! ### Readers of the valency -/

/-- Every frame of the verb is intransitive. -/
def Verb.IsIntransitive (v : Verb) : Prop := ∀ fr ∈ v.valency.frames, fr.IsIntransitive

instance (v : Verb) : Decidable v.IsIntransitive :=
  inferInstanceAs (Decidable (∀ fr ∈ v.valency.frames, _))

/-- Some diathesis of the verb has a participant controlling its clausal complement. -/
def Verb.HasController (v : Verb) : Prop := ∃ d ∈ v.valency.diatheses, d.controller.isSome

instance (v : Verb) : Decidable v.HasController :=
  inferInstanceAs (Decidable (∃ d ∈ v.valency.diatheses, _))

/-- The [noonan-2007] complement types the verb's frames restrict a complement to. -/
def Verb.codings (v : Verb) : Finset Clause.ComplementType :=
  Finset.univ.filter fun c ↦ ∃ fr ∈ v.valency.frames, c ∈ fr.codings

/-- Some frame of the verb selects the sentence type `t`. -/
def Verb.TakesType (v : Verb) (t : Clause.SentenceType) : Prop :=
  ∃ fr ∈ v.valency.frames, fr.hasType t

instance (v : Verb) (t : Clause.SentenceType) : Decidable (v.TakesType t) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- The verb selects some interrogative sentence type, as the responsives and rogatives
*know*, *wonder* and *ask* do. -/
def Verb.TakesQuestion (v : Verb) : Prop := ∃ t, t.IsInterrogative ∧ v.TakesType t

instance (v : Verb) : Decidable v.TakesQuestion := inferInstanceAs (Decidable (∃ _t, _ ∧ _))

/-- Some frame of the verb has a clausal position, so the verb selects a CP or
    reduced clause ([schwarzer-2026]'s CP-selecting verbs). -/
def Verb.TakesClausal (v : Verb) : Prop := ∃ fr ∈ v.valency.frames, fr.HasClausal

instance (v : Verb) : Decidable v.TakesClausal :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- Some frame of the verb has a spatial adpositional position, so the verb selects a locative or
    directional phrase as a complement. -/
def Verb.TakesSpatial (v : Verb) : Prop :=
  ∃ fr ∈ v.valency.frames, ∃ p ∈ fr.complements, p.relation = {.spatial}

instance (v : Verb) : Decidable v.TakesSpatial :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- Some frame of the verb has a nominal position, so the verb selects a DP. -/
def Verb.TakesNominal (v : Verb) : Prop := ∃ fr ∈ v.valency.frames, fr.HasNominal

instance (v : Verb) : Decidable v.TakesNominal :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- The verb triggers a presupposition when what it does with its complement does
(`Clause.Embedding.IsTrigger`) or when it is phasal, presupposing the prior state
(`Aspect.Phasal.denote`). [roberts-simons-2024] explain factives and phasals alike as
preconditions of the event the verb describes. -/
def Verb.IsTrigger (v : Verb) : Prop := v.toEmbedding.IsTrigger ∨ v.phasal ≠ none

instance : DecidablePred Verb.IsTrigger := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem Clause.Embedding.IsTrigger.verb {v : Verb} (h : v.toEmbedding.IsTrigger) : v.IsTrigger :=
  .inl h
