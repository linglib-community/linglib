module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.DistributedMorphology.Nominalization
public import Linglib.Semantics.Composition.BareStructure
public import Linglib.Semantics.Composition.Rules
public import Linglib.Data.Examples.Benz2025
public import Linglib.Fragments.German.Verbs
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Data.Examples.Readers

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
competition. The readings are those of the licensed allosemes that compose, by type, on the
composition engine; with (65b)'s Theme-introducing v the result alloseme does not compose over
an interpreted v, and (69a)'s two-place root under a vacuous v is read as a relation the root
supplies. The co-occurrence and
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

/-! ### Alloseme selection in the nominalization structure -/

/-- `vContext eventive` is v's context in the nominalization structure [n [v √]], with the root,
event-entailing or not, as its complement and n above it. -/
def vContext (eventive : Bool) : Neighborhood (Finset Feature) :=
  ⟨∅, [if eventive then {.eventive} else ∅], [{.cat .n}]⟩

/-- `nContext eventive` is n's context in [n [v √]], with a verbal complement, eventive or not. -/
def nContext (eventive : Bool) : Neighborhood (Finset Feature) :=
  complement (insert (.cat .v) (if eventive then {.eventive} else ∅))

theorem v_allosemes_licensed :
    licensed Verbalizer.vocabulary (vContext true) = [.eventive, 0] ∧
    licensed Verbalizer.vocabulary (vContext false) = [0] := ⟨rfl, rfl⟩

/-! ### The composition of the readings

The meanings of the nominalization are composed from the typed items of
`DistributedMorphology/Nominalization.lean`, the complex head `[[√ v] n]` being read with its
zero heads pruned. -/

/-- The rules of the complex head: Functional Application and Predicate Conjunction. -/
abbrev grammar : ManySorted.Language (Interpreter.Ty Interpreter.Base) :=
  Interpreter.application.sum Interpreter.predicateModification

/-- The items a terminal of the complex head may be. Eventive v introduces the Theme, (65b), and
the root is a predicate of entities or of eventualities, or the relation of (69a). -/
def items : Unit ⊕ Categorizer → List (Σ a, Item a)
  | .inl _ => [⟨_, .rootEntity⟩, ⟨_, .rootEvent⟩, ⟨_, .rootRel⟩]
  | .inr (.v .eventive) => [⟨_, .theme⟩]
  | .inr (.v _) => []
  | .inr (.n a) => a.items

/-- The complex head of the nominalization with the allosemes `v` and `n`. -/
def nominal (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    ComplexHead Unit Categorizer :=
  ⟨(), [.v v, .n n]⟩

/-- The types of the derivations of the nominalization. -/
def types (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    List (Interpreter.Ty Interpreter.Base) :=
  ((nominal v n).skeleton Categorizer.IsZero).elim [] fun s ↦
    ((Interpreter.typeDriven grammar).derivs items s).map (·.1)

/-- The allosemes `v` and `n` compose on some construal of the root. -/
def Composes (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) : Prop := types v n ≠ []

instance : DecidableRel Composes := fun _ _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- Eventive v gives a relation between an entity and an eventuality, which the noun keeps when
n is pruned and which only the content alloseme of n takes; with v pruned the root meets n. -/
theorem composes_iff (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    Composes v n ↔ (v = .eventive ∧ (n = 0 ∨ n = .content)) ∨
      (v = 0 ∧ (n = .simpleEvent ∨ n = .state ∨ n = .entity ∨ n = .result ∨
        n = .content)) := by
  revert v n
  decide

/-- The alloseme pair deriving each reading on the adopted analysis, where v is semantically
vacuous on all readings but the complex event one (§3.5, following [wood-2023]). -/
def adoptedAllosemes (r : NominalizationReading) : Verbalizer.Alloseme × Nominalizer.Alloseme :=
  (if r = .complexEvent then .eventive else 0, Nominalizer.Alloseme.readingEquiv.symm r)

-- The alloseme pair adopted for each reading composes.
theorem adopted_composes (r : NominalizationReading) :
    Composes (adoptedAllosemes r).1 (adoptedAllosemes r).2 := by
  revert r
  decide

/-- The adopted pair is the only derivation of a reading that composes with one of the two heads
vacuous. -/
theorem adopted_unique {v : Verbalizer.Alloseme} {n : Nominalizer.Alloseme} (hc : Composes v n)
    (h : v = 0 ∨ n = 0) : (v, n) = adoptedAllosemes n.reading := by
  revert hc h; revert v n; decide

-- §3.5: the complex event reading has an interpreted v.
theorem eventive_of_complexEvent {v : Verbalizer.Alloseme} {n : Nominalizer.Alloseme}
    (hc : Composes v n) (h : n.reading = .complexEvent) : v = .eventive := by
  revert hc h; revert v n; decide

/-- The result alloseme does not compose over eventive v: a result nominalization has no
position for an argument. -/
theorem not_composes_eventive_result : ¬ Composes .eventive .result := by decide

/-- `availableReadings eventive` lists the readings of the nominalization over a root that is
event-entailing or not: those of the allosemes of v and n licensed in their contexts that
compose. -/
def availableReadings (eventive : Bool) : List NominalizationReading :=
  (licensed Verbalizer.vocabulary (vContext eventive)).flatMap fun v ↦
    ((licensed Nominalizer.vocabulary (nContext eventive)).filter (Composes v ·)).map (·.reading)

-- (32)
theorem beobachtung_readings_available :
    ∀ r ∈ beobachtungRows.filterMap readingOf, r ∈ availableReadings true := by
  decide

-- Table 2
theorem nonEventive_readings :
    availableReadings false = [.content, .simpleEvent, .simpleState, .simpleEntity] := by
  decide

section Denotations

variable {E V : Type} (m : NominalizationModel E V) (ρ : RootMeaning E V)

/-- The denotations of the nominalization, one for each of its derivations. -/
def denotations (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    List (Interpreter.Denotation E Unit { eventuality := V }) :=
  ((nominal v n).skeleton Categorizer.IsZero).elim [] <|
    (Interpreter.typeDriven grammar).values
      (D := Interpreter.Ty.Dom (Interpreter.Base.Dom E Unit { eventuality := V })) inferInstance
      (Item.val m ρ) items

/-- (65): on the event reading n is vacuous and the noun has the verb's meaning, a relation of
the Theme to the eventuality. -/
theorem denotations_event :
    denotations m ρ .eventive 0 = [⟨.evt, fun x e ↦ ρ.onEvents e ∧ m.theme x e⟩] :=
  rfl

-- (67): the result reading, over a vacuous v.
theorem denotations_result :
    denotations m ρ 0 .result = [⟨.et, fun x ↦ ∃ e, ρ.onEvents e ∧ m.result x e⟩] :=
  rfl

-- (69a): the content reading over a vacuous v, the root relating the entity to an eventuality.
theorem denotations_content :
    denotations m ρ 0 .content = [⟨.et, fun x ↦ (∃ e, ρ.rel x e) ∧ m.hasContent x⟩] :=
  rfl

/-- The content reading also composes over eventive v, and describes the same entities as over
a vacuous v when the root's relation is its event predicate with the Theme. -/
theorem denotations_content_eventive
    (h : ρ.rel = fun x e ↦ ρ.onEvents e ∧ m.theme x e) :
    denotations m ρ .eventive .content = denotations m ρ 0 .content := by
  rw [denotations_content, h]
  rfl

end Denotations

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

-- (84)
theorem allowed_iff : Allowed outer inner ↔ outer = .prt ∧ inner = .pfx := by
  revert outer inner; decide

theorem two_factors_needed :
    (StructurallyCompatible .pfx .pfx ∧ ¬ Allowed .pfx .pfx) ∧
      (InterpretivelyCompatible .pfx .prt ∧ ¬ Allowed .pfx .prt) := by
  decide

-- Table 3, §4.4
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
    · exact fun ⟨hs, _⟩ ↦ by simp [StructurallyCompatible, IncorporationAllowed, hi] at hs
    · exact fun ⟨_, hint⟩ ↦ hint ⟨ho, hi⟩
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
  match e.contrasts with
  | [] => e.judgment = .acceptable
  | a :: _ => a.2 = .acceptable

instance (e : Datum) : Decidable (CellAcceptable e) := by
  unfold CellAcceptable; split <;> infer_instance

-- Table 3, (81), (84), (86), (88)
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

-- (115e)
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
endorsed at §5.3.1), read off the entry as an object that undergoes a change of state. -/
def CanUngNominalize (v : German.Verb) : Prop :=
  ∃ θ ∈ v.slotProfile? (.complement 0), .changeOfState ∈ θ

instance (v : German.Verb) : Decidable (CanUngNominalize v) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

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

-- Ch. 5, (193), (197), (198), (204), (212), (216), (218)
theorem nominalization_rows :
    ∀ e ∈ Examples.all, (nominalizationOf e).isSome → (Predicted e ↔ e.judgment = .acceptable) := by
  decide

end Benz2025
