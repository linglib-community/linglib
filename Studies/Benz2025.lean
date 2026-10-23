module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.DistributedMorphology.Allosemy
public import Linglib.Data.Examples.Benz2025
public import Linglib.Fragments.German.Verbs
public import Linglib.Semantics.ArgumentStructure.Unaccusativity

/-!
# Benz (2025): Structure and interpretation across categories

Three case studies on the syntax–LF interface in German run on the contextual-allosemy
substrate of `DistributedMorphology.Allosemy`. One nominalization structure
yields the event, referential and content readings of *Beobachtung*, the variation lying in
the allosemes of v and n (Ch. 3, after Wood). The co-occurrence restrictions among
inseparable prefixes, separable particles and resultative secondary predicates follow from a
phrase-structural factor, that the inner element be a head, together with an event-structural
one, Tenny's Single Delimiting Constraint (Ch. 4), and the particle "structure
problem" of Lüdeling is solved differently by the three nominalization types, whose
distribution of preverbal elements follows from their solutions, while *-ung* further demands
the complex change-of-state structure of Roßdeutscher and Kamp (Ch. 5).

## Implementation notes

Alloseme selection is the substrate's own engine: allosemes are Vocabulary Items over
neighborhoods, applicability is the Subset Principle, and the canonical choice is Elsewhere
competition. The readings are derived from typed denotations, and the co-occurrence and
nominalization paradigms are predicted cell by cell against the example rows, the Table 3
combinations, the resultative data of Creemers and the *-ung* and *Ge-…-e* forms of
Ch. 5, with the base verbs read from the German fragment.

## References

* [benz-2025]
* [wood-2023]
* [tenny-1994]
* [luedeling-2001]
* [rossdeutscher-kamp-2010]
* [williams-2015]
* [creemers-2020]
-/

@[expose] public section

namespace Benz2025

open DistributedMorphology DistributedMorphology.Allosemy German.Verbs
  ArgumentStructure
open Aspect

/-- The fragment entry of a verb form named in a row. -/
def entryOf (form : String) : Option German.Verb := allVerbs.find? (·.form = form)

/-! ## Content nominalizations (Ch. 3) -/

/-- The (32) stimulus rows, in margin-label order Event, RN, Content. -/
def beobachtungRows : List Datum :=
  [Examples.ex32a, Examples.ex32b, Examples.ex32c]

/-- The reading a stimulus row exemplifies, from its `reading` feature. The paper's loose "RN"
label is rendered as the simple entity reading. -/
def readingOf (e : Datum) : Option NominalizationReading :=
  match e.feature? "reading" with
  | some "Event" => some .complexEvent
  | some "RN" => some .simpleEntity
  | some "Content" => some .content
  | _ => none

/-! ### Readings from allosemes -/

/-- The alloseme pair deriving each reading on the adopted analysis, where v is semantically
vacuous on all readings but the CEN (§3.5, following [wood-2023]). By `adopted_roundtrip` and
`adopted_unique`, this is the unique derivation of each reading in which the two heads are not
both contentful. -/
def adoptedAllosemes : NominalizationReading → Verbalizer.Alloseme × Nominalizer.Alloseme
  | .complexEvent => (.eventive, .zero)
  | .simpleEvent  => (.zero, .simpleEvent)
  | .result       => (.zero, .result)
  | .simpleState  => (.zero, .state)
  | .simpleEntity => (.zero, .entity)
  | .content      => (.zero, .content)

theorem adopted_roundtrip (r : NominalizationReading) :
    readingFromAllosemes (adoptedAllosemes r).1 (adoptedAllosemes r).2 = some r := by
  cases r <;> rfl

theorem adopted_unique (r : NominalizationReading) (v : Verbalizer.Alloseme)
    (n : Nominalizer.Alloseme) (hr : readingFromAllosemes v n = some r)
    (h : v.introducesEvent = false ∨ n = .zero) :
    (v, n) = adoptedAllosemes r := by
  revert hr h; revert r v n; decide

/-- The reading pins the division of labor (the "mirror image" claim of §3.5): an event reading
arises only from contentful v with vacuous n, while a result or content reading forces the
corresponding contentful n, whatever v contributes. -/
theorem reading_determines_contentful_head (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    (readingFromAllosemes v n = some .complexEvent →
      v.introducesEvent = true ∧ n = .zero) ∧
    (readingFromAllosemes v n = some .result → n = .result) ∧
    (readingFromAllosemes v n = some .content → n = .content) := by
  revert v n; decide

/-! ### Alloseme selection in the nominalization structure -/

/-- `vContext eventive` is v's context in the nominalization structure [n [v √]], with the root,
event-entailing or not, as its complement and n above it. -/
def vContext (eventive : Bool) : Neighborhood (Finset Feature) :=
  ⟨∅, [if eventive then {.eventive} else ∅], [{.cat .n}]⟩

/-- `nContext eventive` is n's context in [n [v √]], with a verbal complement, eventive or not. -/
def nContext (eventive : Bool) : Neighborhood (Finset Feature) :=
  complement (insert (.cat .v) (if eventive then {.eventive} else ∅))

/-- `availableReadings eventive` lists the readings derivable in the nominalization structure,
those of any licensed v alloseme composed with any licensed n alloseme. -/
def availableReadings (eventive : Bool) : List NominalizationReading :=
  (licensed Verbalizer.vocabulary (vContext eventive)).flatMap (λ v =>
    (licensed Nominalizer.vocabulary (nContext eventive)).filterMap
      (readingFromAllosemes v))

theorem v_allosemes_licensed :
    licensed Verbalizer.vocabulary (vContext true) = [.eventive, .zero] ∧
    licensed Verbalizer.vocabulary (vContext false) = [.zero] := ⟨rfl, rfl⟩

open Morphology.Exponence in
theorem ofKinds_is_selectBy_winner (s : Semantics.Root.Kinds) :
    (winner? Verbalizer.vocabulary
        (vContext (decide (.result ∈ Semantics.Root.Kinds.close s)))).map (·.exponent) =
      some (Verbalizer.Alloseme.ofKinds s) := by
  unfold Verbalizer.Alloseme.ofKinds; split_ifs with h <;> simp only [h, decide_true,
    decide_false] <;> rfl

/-- Every attested *Beobachtung* reading ((32)) is available in the single structure: the
engine licenses the allosemes and composition delivers the readings. -/
theorem beobachtung_readings_available :
    ∀ r ∈ beobachtungRows.filterMap readingOf, r ∈ availableReadings true := by
  decide

/-- Without an event-entailing root neither the complex event nor the result reading is
derivable; the content reading survives, since simple content nouns like *Gerücht* 'rumor'
need no verbal source (Table 2). -/
theorem nonEventive_readings :
    availableReadings false = [.content, .simpleEvent, .simpleState, .simpleEntity] := rfl

/-! ### Typed alloseme denotations (Ch. 3)

The denotations of the deverbal allosemes, after [wood-2023] as taken over
in Ch. 3: nominalization semantics runs over a domain in which eventualities
are entities, and each n alloseme builds an entity predicate from what v
hands it. The reading typology is then derived, not tabulated: readings exist
exactly where the composition is defined
(`readingFromAllosemes_isSome_iff_denote`), and the analytical options for
the result and content readings compose to identical entity predicates
(`result_options_pred_agree`, `content_options_agree`). -/

variable {E S : Type*}

/-- A model for nominalization denotations embeds the eventualities into the entity domain, since
a nominal can describe an event as an entity, and splits them into stative and dynamic; `result`
relates an entity to the eventuality that produced it, and `hasContent` picks out the entities with
propositional content. -/
structure NominalizationModel (E S : Type*) where
  /-- Eventualities as entities. -/
  ev : S → E
  ev_injective : Function.Injective ev
  /-- Stative eventualities. -/
  stative : S → Prop
  /-- The entity is the result of the eventuality. -/
  result : E → S → Prop
  /-- The entity has propositional content (*rumor*, *idea*, *claim*). -/
  hasContent : E → Prop

/-- A root contributes to nominalization semantics what it says of entities and of eventualities,
and its Theme relation, which relates an eventuality of the root's kind to the entity it is
predicated of. -/
structure RootMeaning (E S : Type*) where
  onEntities : E → Prop
  onEvents : S → Prop
  theme : E → S → Prop

/-- v hands to n verbal event content together with the Theme position it introduces under the
eventive alloseme (§2.2), and the untouched root with no argument position under the zero
alloseme, since v then introduces none (§3.5). -/
inductive VerbalDenotation (E S : Type*) where
  | eventive (p : S → Prop) (theme : E → S → Prop)
  | zero (ρ : RootMeaning E S)

/-- `denoteV ρ a` applies the v alloseme `a` to the root `ρ`. -/
def denoteV (ρ : RootMeaning E S) : Verbalizer.Alloseme → VerbalDenotation E S
  | .eventive => .eventive ρ.onEvents ρ.theme
  | .zero     => .zero ρ

/-- A nominal denotation is the entity predicate, together with the internal-argument relation
when the nominal retains one. The relation is
present exactly when v introduced the Theme position — no such position
is part of the denotation unless v contributes it (§2.2, §3.5). -/
structure NominalDenotation (E S : Type*) where
  /-- What the nominal describes. -/
  pred : E → Prop
  /-- `internalArg y x` holds when `y` saturates the Theme position of the nominal `x` (*the
  observation of the sky*). -/
  internalArg : Option (E → E → Prop) := none

/-- `denoteN m d a` applies the n alloseme `a` to v's output `d`, and is `none` where the
combination is uninterpretable. The CEN describes the events the verb describes and
retains the Theme position v introduced; the SEN predicates the root's
entity content of an event-entity; the result alloseme picks out what an
event of the root's kind produced ([wood-2023]'s denotation); the content
alloseme ignores the verbal layer entirely. The non-deverbal allosemes
have their semantics in `Semantics/Possession/Relationalizer.lean`. -/
def denoteN (m : NominalizationModel E S) :
    VerbalDenotation E S → Nominalizer.Alloseme → Option (NominalDenotation E S)
  | .eventive p θ, .zero =>
      some { pred := fun x => ∃ e, x = m.ev e ∧ p e
           , internalArg := some fun y x => ∃ e, x = m.ev e ∧ p e ∧ θ y e }
  | .eventive p θ, .result =>
      some { pred := fun x => ∃ e, p e ∧ m.result x e
           , internalArg := some fun y x => ∃ e, p e ∧ θ y e ∧ m.result x e }
  | .eventive _ _, .content => some { pred := m.hasContent }
  | .zero ρ, .simpleEvent =>
      some { pred := fun x => ρ.onEntities x ∧ ∃ e, x = m.ev e }
  | .zero ρ, .state =>
      some { pred := fun x => ∃ e, x = m.ev e ∧ m.stative e ∧ ρ.onEvents e }
  | .zero ρ, .result =>
      some { pred := fun x => ∃ e, ρ.onEvents e ∧ m.result x e }
  | .zero ρ, .entity => some { pred := ρ.onEntities }
  | .zero _, .content => some { pred := m.hasContent }
  | _, _ => none

/-- The event and result readings are mirror images at the
entity-predicate level: the two analytical options for the result
reading — eventive v with n's result alloseme, or vacuous v with the
same — agree on what the nominal describes (§3.5, crediting
[wood-2023]). -/
theorem result_options_pred_agree (m : NominalizationModel E S) (ρ : RootMeaning E S) :
    (denoteN m (denoteV ρ .eventive) .result).map (·.pred)
      = (denoteN m (denoteV ρ .zero) .result).map (·.pred) := rfl

/-- ...but not on argument structure: on the both-heads-interpreted
option the result nominal retains the internal-argument position v
introduced, on the v-vacuous option it has none. Since result nominals
cannot saturate an internal argument, this is the reason for adopting the
vacuous option for the RN reading (§3.5, following [wood-2023]). -/
theorem result_options_disagree_on_arguments (m : NominalizationModel E S)
    (ρ : RootMeaning E S) :
    (∃ r, denoteN m (denoteV ρ .eventive) .result = some r ∧ r.internalArg.isSome)
      ∧ ∃ r, denoteN m (denoteV ρ .zero) .result = some r ∧ r.internalArg = none :=
  ⟨⟨_, rfl, rfl⟩, _, rfl, rfl⟩

theorem cen_retains_argument_structure (m : NominalizationModel E S) (ρ : RootMeaning E S) :
    ∃ r, denoteN m (denoteV ρ .eventive) .zero = some r ∧ r.internalArg.isSome :=
  ⟨_, rfl, rfl⟩

/-- No zero-v reading has an internal-argument position: none is
introduced by v, so none is part of the denotation (§3.5). -/
theorem zero_v_no_argument_structure (m : NominalizationModel E S) (ρ : RootMeaning E S)
    (n : Nominalizer.Alloseme) {r : NominalDenotation E S}
    (h : denoteN m (denoteV ρ .zero) n = some r) : r.internalArg = none := by
  rcases n with _ | cn
  · simp [denoteV, denoteN] at h
  · cases cn <;> simp only [denoteV, denoteN, Option.some.injEq, reduceCtorEq] at h <;>
      (try subst h) <;> rfl

/-- The content reading likewise ignores the verbal layer: both v
options compose to `hasContent`, which is how simple content nouns can
have the reading with no verbal source at all (§3.5). -/
theorem content_options_agree (m : NominalizationModel E S) (ρ : RootMeaning E S) :
    denoteN m (denoteV ρ .eventive) .content = denoteN m (denoteV ρ .zero) .content := rfl

theorem readingFromAllosemes_isSome_iff_denote (m : NominalizationModel E S)
    (ρ : RootMeaning E S) (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    (readingFromAllosemes v n).isSome ↔ (denoteN m (denoteV ρ v) n).isSome := by
  rcases v with _ | cv <;> rcases n with _ | cn <;> (try cases cv) <;> (try cases cn) <;>
    simp [readingFromAllosemes, denoteV, denoteN]

theorem cen_denotes_events (m : NominalizationModel E S) (ρ : RootMeaning E S)
    {r : NominalDenotation E S} (h : denoteN m (denoteV ρ .eventive) .zero = some r) :
    ∀ x, r.pred x → ∃ e, x = m.ev e := by
  simp only [denoteV, denoteN, Option.some.injEq] at h
  subst h
  rintro x ⟨e, rfl, -⟩
  exact ⟨e, rfl⟩

/-! ## Prefixes, particles, and resultatives (Ch. 4) -/

/-- A German preverbal element is an inseparable prefix (*be-*, *ent-*, *er-*, *ver-*, *zer-*), a
separable particle (*ab-*, *an-*, *auf-*, *aus-*, *ein-*) or a resultative secondary predicate
(*platt*, *tot*, *kaputt*). -/
inductive PreverbalElement where
  | pfx
  | prt
  | rsp
  deriving DecidableEq, Repr, Fintype

/-- A head, which can sit inside a complex head, or a phrase, which cannot incorporate. -/
inductive SynLevel where
  | head
  | phrase
  deriving DecidableEq, Repr

/-- Prefixes are heads forming a complex head with the root, inseparable under V2 movement;
particles and resultatives are phrasal, stranded under V2 ([wurmbrand-1998],
[zeller-2001]). -/
def PreverbalElement.synLevel : PreverbalElement → SynLevel
  | .pfx => .head
  | .prt => .phrase
  | .rsp => .phrase

/-- An element either obligatorily specifies a result state, as prefixes and resultatives do, or
does not, as particles with their non-delimiting directional and completive readings (§4.4). -/
inductive ResultStateSpec where
  | specifies
  | neutral
  deriving DecidableEq, Repr

def PreverbalElement.resultSpec : PreverbalElement → ResultStateSpec
  | .pfx => .specifies
  | .prt => .neutral
  | .rsp => .specifies

/-! ### The two factors -/

/-- The inner element, closer to the root, must be a head: a head outside a phrase cannot form
a complex head with the root, and a phrasal outer element competes with a phrasal inner one
for the verb's single complement position (§4.4). -/
def IncorporationAllowed (_outer inner : SynLevel) : Prop := inner = .head

instance (outer inner : SynLevel) : Decidable (IncorporationAllowed outer inner) :=
  inferInstanceAs (Decidable (_ = _))

/-- Two obligatory result-state specifiers conflict, since the end state of a complex event is
specified once: [tenny-1994]'s Single Delimiting Constraint, (159). -/
def ResultStatesCompatible (a b : ResultStateSpec) : Prop :=
  ¬ (a = .specifies ∧ b = .specifies)

instance (a b : ResultStateSpec) : Decidable (ResultStatesCompatible a b) :=
  inferInstanceAs (Decidable (¬ _))

variable (outer inner : PreverbalElement)

def StructurallyCompatible : Prop := IncorporationAllowed outer.synLevel inner.synLevel

def InterpretivelyCompatible : Prop := ResultStatesCompatible outer.resultSpec inner.resultSpec

/-- A combination is predicted possible iff both factors permit it (§4.4). -/
def Allowed : Prop := StructurallyCompatible outer inner ∧ InterpretivelyCompatible outer inner

instance : Decidable (StructurallyCompatible outer inner) :=
  inferInstanceAs (Decidable (IncorporationAllowed _ _))

instance : Decidable (InterpretivelyCompatible outer inner) :=
  inferInstanceAs (Decidable (ResultStatesCompatible _ _))

instance : Decidable (Allowed outer inner) := inferInstanceAs (Decidable (_ ∧ _))

/-- The particle-over-prefix order is the one allowed combination ((84) *aus-er-wählen*,
*an-ver-trauen*, *vor-ent-halten*). -/
theorem allowed_iff : Allowed outer inner ↔ outer = .prt ∧ inner = .pfx := by
  revert outer inner; decide

theorem two_factors_needed :
    (StructurallyCompatible .pfx .pfx ∧ ¬ Allowed .pfx .pfx) ∧
      (InterpretivelyCompatible .pfx .prt ∧ ¬ Allowed .pfx .prt) := by
  decide

/-- The printed Table 3 marks the merged pfx/PRT-RSP row's interpretation cell excluded, but
on the account's own classification only the prefix half is: for a particle over a resultative
the structural factor does the work, and only some such verbs are also ruled out semantically
(§4.4). -/
theorem prt_rsp_particle_dependent :
    ¬ StructurallyCompatible .prt .rsp ∧ InterpretivelyCompatible .prt .rsp := by
  decide

/-! ### Blocking derivations -/

/-- A derivation that a combination violates one of the two principles. -/
inductive Blocked : PreverbalElement → PreverbalElement → Prop where
  /-- A phrasal element cannot occupy the inner position (§4.4). -/
  | byPhrasalInner {o i : PreverbalElement} : i.synLevel = .phrase → Blocked o i
  /-- Two obligatory result-state specifiers conflict ((159)). -/
  | bySingleDelimiting {o i : PreverbalElement} :
      o.resultSpec = .specifies → i.resultSpec = .specifies → Blocked o i

theorem blocked_iff : Blocked outer inner ↔ ¬ Allowed outer inner := by
  constructor
  · rintro (hi | ⟨ho, hi⟩)
    · exact λ ⟨hs, _⟩ => by simp [StructurallyCompatible, IncorporationAllowed, hi] at hs
    · exact λ ⟨_, hint⟩ => hint ⟨ho, hi⟩
  · intro h
    revert h
    cases outer <;> cases inner <;> intro h <;>
      first
      | exact absurd (by decide) h
      | exact .byPhrasalInner rfl
      | exact .bySingleDelimiting rfl rfl

/-! ### The paradigm against the examples -/

def elementOf : String → Option PreverbalElement
  | "pfx" => some .pfx
  | "prt" => some .prt
  | "rsp" => some .rsp
  | _ => none

/-- `CellAcceptable e` holds when the combination the row tests is acceptable, the combination
being the row's alternative where it gives one ((87) and (88) pair a resultative baseline with the
blocked prefixed or particle form) and the row itself otherwise. -/
def CellAcceptable (e : Datum) : Prop :=
  match e.alternatives with
  | [] => e.judgment = .acceptable
  | a :: _ => a.2 = .acceptable

instance (e : Datum) : Decidable (CellAcceptable e) := by
  unfold CellAcceptable; split <;> infer_instance

/-- Table 3 agrees with its examples ((81)–(84), (86)–(88)): a combination is acceptable exactly
when both factors allow it. -/
theorem allowed_rows :
    ∀ e ∈ Examples.all, ∀ o ∈ (e.feature? "outer").bind elementOf,
      ∀ i ∈ (e.feature? "inner").bind elementOf, (Allowed o i ↔ CellAcceptable e) := by
  decide

/-! ### German resultative data (§4.2)

Complex predicate semantics after [williams-2015], adopted at (158): the M(eans) predicate is
the verb, the R(esult) predicate the resultative, and the End Theme Postulate (108) links the
complex event's Theme to the end state. -/

/-- The resultative stimulus rows ((89), (115); the (115) rows are due to [creemers-2020]). -/
def rspRows : List Datum :=
  [Examples.ex89a, Examples.ex89b, Examples.ex115a, Examples.ex115e, Examples.ex115f]

theorem rsp_rows_have_entries :
    ∀ e ∈ rspRows, ((e.feature? "m_predicate").bind entryOf).isSome := by
  decide

theorem rsp_verb_classes :
    ∀ e ∈ rspRows, ∀ v ∈ (e.feature? "m_predicate").bind entryOf,
      (e.feature? "verb_class" = some "unaccusative" ↔ v.toVerb.IsUnaccusative) := by
  decide

/-- German allows non-unergative means predicates in resultatives ((115e) *frieren*), against
weak-resultative reanalyses of the whole class. -/
theorem unaccusative_means :
    ∃ e ∈ rspRows, ∃ v ∈ (e.feature? "m_predicate").bind entryOf, v.toVerb.IsUnaccusative := by
  decide

/-! ## Prefixes in nominalizations (Ch. 5) -/

/-- German nominalizes by *-ung* suffixation, by *Ge-…-e* circumfixation, and by the nominalized
infinitive. -/
inductive NominalizationType where
  | ung
  | geE
  | infinitive
  deriving DecidableEq, Repr

/-- A solution to the particle structure problem ([luedeling-2001]), how a phrasal particle
ends up inside a derived nominal: the nominalizer takes phrasal structure, the particle
attaches low as a head, or the particle attaches outside the nominalizer. -/
inductive StructureSolution where
  | phrasalInput
  | particleAsHead
  | outerAttachment
  deriving DecidableEq, Repr

/-- The solution each type favors (§5.2–5.4): nominalized infinitives take phrasal inputs,
*-ung* particles as heads, *Ge-…-e* outer attachment ((223)), since its eventive semantics
without an internal argument conflicts with prefix verbs' argument-structural demands. -/
def NominalizationType.solution : NominalizationType → StructureSolution
  | .infinitive => .phrasalInput
  | .ung => .particleAsHead
  | .geE => .outerAttachment

/-- The element can attach as a non-phrasal head: prefixes always, particles low (§5.3), and
resultatives never ((205)–(206)). -/
def PreverbalElement.CanAttachAsHead : PreverbalElement → Prop
  | .rsp => False
  | _ => True

instance : DecidablePred PreverbalElement.CanAttachAsHead
  | .pfx => inferInstanceAs (Decidable True)
  | .prt => inferInstanceAs (Decidable True)
  | .rsp => inferInstanceAs (Decidable False)

/-- `s.Admits pe` holds when the solution `s` accommodates the element `pe`: phrasal inputs admit
everything, particles-as-heads the head-attachers, outer attachment the phrasal elements, since a
prefix is a verbal head and cannot attach outside a noun. -/
def StructureSolution.Admits : StructureSolution → PreverbalElement → Prop
  | .phrasalInput, _ => True
  | .particleAsHead, pe => pe.CanAttachAsHead
  | .outerAttachment, pe => pe.synLevel = .phrase

instance (s : StructureSolution) (pe : PreverbalElement) : Decidable (s.Admits pe) := by
  cases s <;> unfold StructureSolution.Admits <;> infer_instance

/-- *-ung* requires complex change-of-state event structure ([rossdeutscher-kamp-2010],
endorsed at §5.3.1), the accomplishments of the fragment. -/
def CanUngNominalize (v : German.Verb) : Prop := v.vendlerClass = some .accomplishment

instance (v : German.Verb) : Decidable (CanUngNominalize v) :=
  inferInstanceAs (Decidable (_ = _))

def typeOf : String → Option NominalizationType
  | "ung" => some .ung
  | "geE" => some .geE
  | "infinitive" => some .infinitive
  | _ => none

/-- A row's nominalization type. -/
def nominalizationOf (e : Datum) : Option NominalizationType :=
  (e.feature? "nominalization").bind typeOf

/-- `Predicted e` holds when the account predicts the nominalization row `e`: the type's solution
accommodates the preverbal element, and an *-ung* form has a base with complex change-of-state
structure. -/
def Predicted (e : Datum) : Prop :=
  (∀ nt ∈ nominalizationOf e, ∀ pe ∈ (e.feature? "element").bind elementOf,
    nt.solution.Admits pe) ∧
    (nominalizationOf e = some .ung → ∀ v ∈ (e.feature? "verb").bind entryOf, CanUngNominalize v)

instance (e : Datum) : Decidable (Predicted e) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem nominalization_rows_have_entries :
    ∀ e ∈ Examples.all, (nominalizationOf e).isSome →
      ((e.feature? "verb").bind entryOf).isSome := by
  decide

/-- The Ch. 5 distribution ((193), (197), (198), (204), (212), (216), (218)): a nominalization
is acceptable exactly when the account predicts it. -/
theorem nominalization_rows :
    ∀ e ∈ Examples.all, (nominalizationOf e).isSome → (Predicted e ↔ e.judgment = .acceptable) := by
  decide

end Benz2025
