module

public import Linglib.Syntax.Clause.Complementation
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Syntax.Category.Verb.Diathesis
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Logic.Natural.ImplicationSignature
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Events.Path
public import Linglib.Semantics.Attitudes.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Basic
public import Linglib.Logic.Natural.Signature
public import Linglib.Semantics.Aspect.Phasal
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.Degree.Gradability
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Semantics.Root.Defs
public import Linglib.Morphology.Morph

/-!
# Verb entries

`Verb` is the framework-neutral verb entry shared by every language's fragment. Its fields are
grouped into the facets `Verb.ArgStructure`, `Verb.Aspect`, `Verb.Presupposition` and
`Verb.Attitude`, beside the selectional and inflectional enums `VoiceType`,
`Verb.PerfectAuxiliary` and `SenseTag`.
A verb's valency is its participants and their diatheses, each with the participant that
controls its clausal complement, and a frame-conditioned attitude or opacity lives on a
`Verb.Reading` row. The classifications of an entry, factive,
implicative, trigger and so on, are read off these fields by the theories that make them.

## Implementation notes

* `Verb` composes its facets by `extends`, so a field is reached flat, as `v.valency`, and a
  language fragment extends `Verb` with its inflectional paradigm.
* The citation form is the list `morphs`, and `Verb.form` is its surface string, so a fragment
  builds a derived form, a converb or a causative, by attaching morphs to `v.morphs`.
* The facets share their names with the theory namespaces whose values they hold, so a
  facet field names its type with `_root_`.

## References

* [bale-schwarz-2026]
* [dayal-2025]
* [heim-1992]
* [icard-2012]
* [kennedy-2007]
* [levin-hovav-1995]
* [maier-2015]
* [pantcheva-2011]
* [qing-uegaki-2025]
* [rappaport-hovav-levin-2024]
* [rappaport-hovav-levin-1998]
* [solstad-bott-2024]
-/

@[expose] public section

open Aspect ArgumentStructure Presupposition
open NaturalLogic (Signature)
open Morphology (Morph)

/-! ### Selectional and inflectional enums -/

/-- The external-argument dimension of a verb's frame, neutral between syntactic frameworks. -/
inductive VoiceType where
  /-- An external argument is introduced, as in transitives and unergatives. -/
  | agentive
  /-- No external argument is introduced, as in unaccusatives and anticausatives. -/
  | nonThematic
  /-- The head has no specifier and no semantics, as in the middle voice. -/
  | expletive
  /-- An agent that binds the internal argument ([wood-2015]). -/
  | reflexive
  /-- An experiencer external argument ([wood-2015]). -/
  | experiencer
  deriving DecidableEq, Repr

/-- The voice type introduces an external argument. -/
def VoiceType.AssignsTheta (vt : VoiceType) : Prop :=
  vt = .agentive ∨ vt = .reflexive ∨ vt = .experiencer

instance : DecidablePred VoiceType.AssignsTheta :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

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
  /-- The occasion sense, with an agent-evocator subject ([solstad-bott-2024]). -/
  | occasion
  /-- The stative reading of a polysemous verb, as positional *suivre* 'follow'. -/
  | stative
  deriving DecidableEq, Repr

/-! ### Field facets

Each facet groups a concern's fields; `Verb` composes them via `extends`,
so flat access (`v.valency`) is preserved. -/

namespace Verb

/-- The argument structure and realization of a verb are its valency and voice. An implicit
    argument is a frame position (`ArgumentFrame.objectDrop`). -/
structure ArgStructure where
  /-- The verb's participants, with the proto-role entailment profiles the entry records for
      them ([dowty-1991], [grimm-2011], [levin-2019]), and its diatheses, the basic diathesis
      first; the default records no participant. -/
  valency : Verb.Valency := .of []
  /-- The voice type, which fixes whether an external argument is introduced. -/
  voiceType : Option VoiceType := none
  /-- Can the verb passivize? -/
  passivizable : Bool := true
  /-- The auxiliaries the verb forms its perfect with, as its grammar gives them, both where it
      gives both; empty where the language has no choice or the entry records none. -/
  perfectAuxiliaries : Finset Verb.PerfectAuxiliary := ∅
  deriving BEq

/-- The aspectual class of a verb is its Vendler class, lexical viewpoint, scale, direction of
    motion, incrementality and phasal class. -/
structure Aspect where
  /-- [vendler-1957] aspectual class of the verb's base VP.
      For verbs whose class depends on the object NP (eat apples = activity,
      eat two apples = accomplishment), record the class with a quantized
      (bounded) object. `none` for verbs where Vendler class is inapplicable
      (e.g., clause-embedding verbs). -/
  vendlerClass : Option VendlerClass := none
  /-- The viewpoint the stem lexicalizes, in a language that encodes the opposition of perfective
      and imperfective on verb stems, as the Slavic languages do, at its dictionary value; `none`
      where the language does not. -/
  perfectivity : Option Perfectivity := none
  /-- The dimension of a gradable verb's scale, along which a degree achievement measures change
      and on which a gradable state such as *believe* measures its holder. -/
  scaleDimension : Option Degree.ScalarDimension := none
  /-- The pole of the dimension the verb measures towards, negative for *dry*, a decrease in
      wetness, and for *doubt*, the antonym of *believe*. -/
  scalePolarity : Polarity := .positive
  /-- The positive standard the verb's lexicon fixes, `none` taking its scale's default. -/
  lexicalStandard : Option Degree.PositiveStandard := none
  /-- The direction of the path along which a verb of motion displaces its theme, relative to
      the ground ([pantcheva-2011]). It is `.goal` for *arrive* and *come*, `.source` for
      *leave*, and `.place` for a verb of manner of motion, which displaces its theme without a
      direction ([levin-hovav-1995] p. 147, *roll*, *walk*, *swim* against *arrive*, *come*,
      *fall*), and `none` for a verb that says nothing of its theme's path. -/
  direction : Option Spatial.Path.Direction := none
  /-- The [krifka-1998] incrementality class of the theme relation, `none` for intransitives
      and clause-embedding verbs. -/
  incrementality : Option Incrementality := none
  /-- The phasal class of a phasal verb such as *stop*, *start* or *continue*. -/
  phasal : Option Phasal := none
  deriving Repr, BEq

/-- The presupposition profile of a verb is its factivity class and its implication signature.
    Whether the verb triggers a presupposition is derived (`Verb.IsTrigger`). -/
structure Presupposition where
  /-- The [karttunen-1971b] factivity class of a factive predicate; `none` for a
      non-factive. -/
  factivity : Option _root_.Presupposition.Factivity := none
  /-- The [nairn-condoravdi-karttunen-2006] implication signature of the verb, the polarity of
      the complement it implies in a positive and in a negative context; `⊥` for a verb that
      implies nothing. -/
  implicative : NaturalLogic.ImplicationSignature := ⊥
  deriving Repr, BEq

/-- A frame-conditioned reading of a verb ([bondarenko-2022] §4.4.3 *hanaxa*; Greek
    *thimame*) overrides the lexeme-level attitude, factivity and opacity for its frame (`none`
    inherits `Verb.attitude`, `Verb.factivity` and `Verb.opaqueContext`) and records the sort of
    the frame's complement. -/
structure Reading where
  /-- The reading applies to every frame of the verb refining this one, in the refinement order
      on `ArgumentFrame`. -/
  frame : ArgumentFrame
  /-- Frame-conditioned attitude override. -/
  attitude : Option _root_.Attitude := none
  /-- Frame-conditioned opacity override. -/
  opaqueContext : Option Bool := none
  /-- Frame-conditioned factivity override, `none` inheriting `Verb.factivity`. -/
  factivity : Option _root_.Presupposition.Factivity := none
  /-- The semantic sort of the complement on this frame
      ([wurmbrand-lohninger-2023]). -/
  size : Option Clause.Size := none
  deriving DecidableEq, Repr

/-- The attitudinal and intensional properties of a verb are its attitude classification,
    opacity, question-embedding and complement monotonicity. -/
structure Attitude where
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- The attitude the verb expresses, doxastic or preferential, if it is an attitude verb. -/
  attitude : Option _root_.Attitude := none
  /-- The frame-conditioned readings ([bondarenko-2022] §4.4.3), per-frame attitude and opacity
      overrides keyed to the frames of `valency`. -/
  readings : List Reading := []
  /-- Entailment signature of the complement position.
      Classifies this verb's monotonicity w.r.t. its clausal complement.
      `.mono` is upward monotone, the report closed under entailment of
      the complement, as in Hintikka-style doxastic semantics
      ([hintikka-1962]). Set only where the classification is textbook
      consensus (believe, think, know); preferential attitudes (want, hope)
      are contested ([heim-1992]) and stay `none`. -/
  complementSig : Option Signature := none
  deriving Repr, BEq

end Verb

/--
The cross-linguistic verb core holds the semantic fields shared across languages.

Composes the `Verb.*` facets (argument structure, aspect, presupposition,
attitude, root) plus the morphs of the citation form, speech-act status, and a
polysemy disambiguator. Language-specific fragments extend this with
morphological fields appropriate to their inflectional system.
-/
structure Verb extends Verb.ArgStructure, Verb.Aspect, Verb.Presupposition, Verb.Attitude where
  /-- The [levin-1993] classes whose member lists carry the citation form, for the English
      entries; the classes are Levin's, so entries for other languages carry none. A verb Levin
      cross-lists carries every class, and a study chooses a sense by membership. -/
  levinClasses : Finset LevinClass := ∅
  /-- Levin classes that list the citation form in a sense this entry is not, and so are left
      out of `levinClasses`. -/
  levinExcluded : Finset LevinClass := ∅
  /-- The meaning of the verb's root, its kind signature and within-class content, read
      rather than the verb's Levin classes. The default `{}` is the unannotated root. -/
  root : ArgumentStructure.Root := {}
  /-- The morphs of the citation form, in surface order, are the stem with the affixes and
      particles it is cited with. A citation form the entry does not analyse is a single root. -/
  morphs : List Morph
  /-- The spelling in the native script, where the morphs are a romanization. -/
  script : Option String := none
  /-- Does the verb denote the performance of an illocutionary act?
      True for speech-act verbs (say, tell, claim, ask). This is a genuine
      semantic primitive that cannot be derived from other fields. -/
  speechActVerb : Bool := false
  /-- Disambiguates entries that share a citation form.
      Most verbs use `.default`; polysemous entries use descriptive tags. -/
  senseTag : SenseTag := .default
  deriving BEq

/-- The citation form of a verb is the surface form of its morphs, in boundary notation. -/
def Verb.form (v : Verb) : String := Morph.surface v.morphs

/-- The degree semantics of a verb, `none` for a verb without a scale. -/
def Verb.gradability? (v : Verb) : Option Degree.Gradability :=
  v.scaleDimension.map fun d ↦ ⟨d, v.scalePolarity, v.lexicalStandard⟩

/-- The scale of a gradable verb. -/
def Verb.boundedness (v : Verb) : Option Degree.Boundedness :=
  v.gradability?.map (·.boundedness)

/-- The positive standard of a gradable verb. -/
def Verb.standard (v : Verb) : Option Degree.PositiveStandard :=
  v.gradability?.map (·.standard)

/-- The scale along which a degree achievement measures change is the scale of a verb that is not
a state, since a state measures no change. -/
def Verb.changeScale (v : Verb) : Option Degree.Boundedness :=
  if v.vendlerClass = some .state then none else v.boundedness

/-! ### ArgumentFrame accessors

Readers over the frames of `Verb.valency` and over `Verb.readings`, such as whether some diathesis
has a controller. -/

/-- The reading keyed to frame `fr` is the first whose frame `fr` refines. -/
def Verb.reading? (v : Verb) (fr : ArgumentFrame) : Option Verb.Reading :=
  v.readings.find? fun r ↦ decide (r.frame ≤ fr)

/-- Every frame of the verb is intransitive. -/
def Verb.IsIntransitive (v : Verb) : Prop := ∀ fr ∈ v.valency.frames, fr.IsIntransitive

instance (v : Verb) : Decidable v.IsIntransitive :=
  inferInstanceAs (Decidable (∀ fr ∈ v.valency.frames, _))

/-- Some diathesis of the verb has a participant controlling its clausal complement. -/
def Verb.HasController (v : Verb) : Prop := ∃ d ∈ v.valency.diatheses, d.controller.isSome

instance (v : Verb) : Decidable v.HasController :=
  inferInstanceAs (Decidable (∃ d ∈ v.valency.diatheses, _))

/-- The effective attitude on frame `fr` is the reading's override, else the lexeme's
    default. -/
def Verb.attitudeOn (v : Verb) (fr : ArgumentFrame) : Option _root_.Attitude :=
  ((v.reading? fr).bind (·.attitude)).orElse fun _ ↦ v.attitude

/-- The effective factivity on frame `fr` is the reading's override, else the lexeme's
    default. -/
def Verb.factivityOn (v : Verb) (fr : ArgumentFrame) : Option _root_.Presupposition.Factivity :=
  ((v.reading? fr).bind (·.factivity)).orElse fun _ ↦ v.factivity

/-- All [noonan-2007] codings across the verb's frames. -/
def Verb.codings (v : Verb) : List Clause.ComplementType :=
  v.valency.frames.flatMap ArgumentFrame.codings

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
  ∃ fr ∈ v.valency.frames, ∃ p ∈ fr.complements, p.relation? = some .spatial

instance (v : Verb) : Decidable v.TakesSpatial :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- Some frame of the verb has a nominal position, so the verb selects a DP. -/
def Verb.TakesNominal (v : Verb) : Prop := ∃ fr ∈ v.valency.frames, fr.HasNominal

instance (v : Verb) : Decidable v.TakesNominal :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))
