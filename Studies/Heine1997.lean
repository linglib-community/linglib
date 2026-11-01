module

public import Linglib.Data.Examples.Heine1997
public import Linglib.Syntax.Case.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.SymmDiff
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Heine (1997): Possession

This file formalizes the second chapter of [heine-1997], on the sources of predicative
possession. Possessive constructions derive by grammaticalization from eight event schemas,
propositional templates for everyday situations: *X takes Y*, *Y is located at X*, *X is with
Y*, *X's Y exists*, *Y exists for X*, *Y exists from X*, *as for X, Y exists*, and *Y is X's*.
Each schema is a `Formula` giving its predicate nucleus, which participant it makes the subject,
and how the other participant enters, and the contrastive properties the chapter tabulates
follow from the formulas: only the Action Schema has a lexical nucleus, only Action and
Location are basic rather than extended by an adjunct or modifier, and only Action and
Companion encode the possessor as the subject, the others marking it by an oblique case
(`Schema.possessorCase`). Grammaticalization follows the Overlap Model: a construction carries
the source meaning alone, then both meanings, then the target meaning alone, and
`overlap_of_gradual` derives the middle stage for any development that changes one meaning at
a time and is never meaningless. The rows carry the chapter's examples, the Russian locative
construction at each of the three stages (`russian_stages`), the Telugu division of labour
between the Location Schema for physical possession and the Goal Schema for the permanent and
inalienable notions (`Notion`, `telugu_notions`), and the Ewe and English cases.

The chapter's survey of source schemas in a hundred languages, the correlations between
schemas and *have* or *belong* constructions, and the probabilistic generalizations about
which notions each schema tends to express stay in prose: Location and Goal are the most
frequent sources and Action a minority one, Location gives *have* constructions and Equation
*belong* constructions, and the Existence schemas are seldom recruited for physical
possession.

## Implementation notes

* The formulas are the chapter's; the classification of nuclei as lexical or schematic and of
  the second participant's entry as core or grafted on are the chapter's criteria, applied
  once to each formula.
* The Source Schema, absent from the chapter's tables, is treated as an Existence schema with
  an ablative possessor.

## References

* [heine-1997]
* [heine-1993]
-/

@[expose] public section

namespace Heine1997

/-! ### The event schemas -/

/-- The eight event schemas from which predicative possession derives. -/
inductive Schema where
  | action
  | location
  | companion
  | genitive
  | goal
  | source
  | topic
  | equation
  deriving DecidableEq, Repr, Fintype

/-- The predicate nucleus of a schema's formula is the lexical verb *take*, the locative copula *be
at*, the existential *exist*, or the equative copula *be*. -/
inductive Nucleus where
  | take
  | beAt
  | exist
  | be
  deriving DecidableEq, Repr

/-- A nucleus is lexical if it retains lexical content, as *take* does and the schematic predicates
of location, existence, and equation do not. -/
def Nucleus.IsLexical : Nucleus → Prop
  | .take => True
  | .beAt | .exist | .be => False

instance : DecidablePred Nucleus.IsLexical
  | .take => isTrue trivial
  | .beAt | .exist | .be => isFalse id

/-- The two participants of a possessive situation. -/
inductive Participant where
  | possessor
  | possessee
  deriving DecidableEq, Repr

/-- The participant that is not the subject enters the formula as the object or the locative
argument of the nucleus, or grafted on as a comitative, dative, or ablative adjunct, a genitival
modifier, or a topic. -/
inductive Entry where
  | object
  | locative
  | comitative
  | genitive
  | dative
  | ablative
  | topic
  deriving DecidableEq, Repr

/-- Whether the entry is an argument of the nucleus rather than an addition to a simpler
structure. -/
def Entry.IsCore : Entry → Prop
  | .object | .locative => True
  | .comitative | .genitive | .dative | .ablative | .topic => False

instance : DecidablePred Entry.IsCore
  | .object | .locative => isTrue trivial
  | .comitative | .genitive | .dative | .ablative | .topic => isFalse id

/-- The case that marks an entry, when it is a case-marked oblique. -/
def Entry.case : Entry → Option Case
  | .locative => some .loc
  | .comitative => some .com
  | .genitive => some .gen
  | .dative => some .dat
  | .ablative => some .abl
  | .object | .topic => none

/-- A formulaic description of a schema gives its nucleus, the participant it encodes as the
subject, and how the other participant enters. -/
structure Formula where
  nucleus : Nucleus
  subject : Participant
  entry : Entry
  deriving DecidableEq, Repr

/-- The formulas of the eight schemas. -/
def Schema.formula : Schema → Formula
  | .action => ⟨.take, .possessor, .object⟩
  | .location => ⟨.beAt, .possessee, .locative⟩
  | .companion => ⟨.be, .possessor, .comitative⟩
  | .genitive => ⟨.exist, .possessee, .genitive⟩
  | .goal => ⟨.exist, .possessee, .dative⟩
  | .source => ⟨.exist, .possessee, .ablative⟩
  | .topic => ⟨.exist, .possessee, .topic⟩
  | .equation => ⟨.be, .possessee, .genitive⟩

/-- A schema is basic when its second participant is an argument of the nucleus, extended when
it is grafted onto a simpler structure. -/
def Schema.IsBasic (s : Schema) : Prop := s.formula.entry.IsCore

instance : DecidablePred Schema.IsBasic := fun s ↦
  inferInstanceAs (Decidable s.formula.entry.IsCore)

/-- The case marking the possessor when it is not the subject. -/
def Schema.possessorCase (s : Schema) : Option Case :=
  if s.formula.subject = .possessee then s.formula.entry.case else none

/-! The contrastive properties of the schemas follow from their formulas. -/

theorem isLexical_iff (s : Schema) : s.formula.nucleus.IsLexical ↔ s = .action := by
  cases s <;> decide

theorem isBasic_iff (s : Schema) : s.IsBasic ↔ s = .action ∨ s = .location := by
  cases s <;> decide

theorem subject_possessor_iff (s : Schema) :
    s.formula.subject = .possessor ↔ s = .action ∨ s = .companion := by
  cases s <;> decide

theorem possessorCase_isSome_iff (s : Schema) :
    s.possessorCase.isSome ↔ s.formula.subject = .possessee ∧ s ≠ .topic := by
  cases s <;> decide

/-! ### The Overlap Model

A construction grammaticalizing from a source schema to a possessive target carries the source
meaning alone at Stage I, both meanings at Stage II, where it is ambiguous, and the target
meaning alone at Stage III. -/

/-- The meanings a construction can carry are that of its source schema and the possessive target.
-/
inductive Meaning where
  | source
  | target
  deriving DecidableEq, Repr, Fintype

/-- The three stages of the Overlap Model. -/
def stage : Fin 3 → Finset Meaning
  | 0 => {.source}
  | 1 => {.source, .target}
  | 2 => {.target}

/-- A development is gradual when consecutive stages differ in at most one meaning and no
stage is meaningless. -/
def Gradual (f : ℕ → Finset Meaning) : Prop :=
  ∀ i, (f i).Nonempty ∧ (symmDiff (f i) (f (i + 1))).card ≤ 1

theorem overlap_of_gradual (f : ℕ → Finset Meaning) (hf : Gradual f) (h0 : f 0 = stage 0)
    {n : ℕ} (hn : f n = stage 2) : ∃ i ≤ n, f i = stage 1 := by
  have hex : ∃ i, Meaning.target ∈ f i := ⟨n, by simp [hn, stage]⟩
  have hstep : ∀ s t : Finset Meaning, s.Nonempty → (symmDiff s t).card ≤ 1 →
      Meaning.target ∉ s → Meaning.target ∈ t → t = stage 1 := by
    decide
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h ↦ ?_
    have := Nat.find_spec hex
    rw [h, h0] at this
    simp [stage] at this
  refine ⟨Nat.find hex, Nat.find_min' hex (by simp [hn, stage]), ?_⟩
  rw [hj]
  exact hstep (f j) (f (j + 1)) (hf j).1 (hf j).2
    (Nat.find_min hex (by omega)) (hj ▸ Nat.find_spec hex)

/-! ### The rows -/

/-- The schema a row instantiates. -/
def schema (r : Datum) : Option Schema :=
  r.parse? "schema" [("action", .action), ("location", .location), ("companion", .companion),
    ("genitive", .genitive), ("goal", .goal), ("source", .source), ("topic", .topic),
    ("equation", .equation)]

/-- The meanings a row's construction carries, read from whether the source and the target
readings are available. -/
def meanings (r : Datum) : Finset Meaning :=
  (if r.feature? "source" = some "true" then {Meaning.source} else ∅) ∪
    (if r.feature? "target" = some "true" then {Meaning.target} else ∅)

/-- The meaning sets of the Russian rows (73), stages I, II, and III of the Location Schema's
grammaticalization. -/
def russianData : List (Finset Meaning) :=
  (Examples.all.filter fun r ↦ r.language = .russian).map meanings

/-- The Russian locative construction is attested at each stage of the Overlap Model, with the
ambiguous (73c) at the overlap stage. -/
theorem russian_stages : ∀ i, stage i ∈ russianData := by decide +kernel

/-- The possessive notions of §1.3 (pp. 34–35). -/
inductive Notion where
  /-- Possessor and possessee are physically associated at reference time (29). -/
  | physical
  /-- The possessor disposes of the possessee for a limited time without owning it (30). -/
  | temporary
  /-- The possessee is the possessor's property (31). -/
  | permanent
  /-- The possessee is inseparable from the possessor, as a body part or a relative (32). -/
  | inalienable
  /-- The possessee is not tangible, as a disease or a feeling (33). -/
  | abstract
  /-- An inanimate possessor with an inseparable possessee (34). -/
  | inanimateInalienable
  /-- An inanimate possessor with a separable possessee (35). -/
  | inanimateAlienable
  deriving DecidableEq, Repr

/-- The possessive notion a row expresses. -/
def notion (r : Datum) : Option Notion :=
  r.parse? "notion" [("physical", .physical), ("temporary", .temporary),
    ("permanent", .permanent), ("inalienable", .inalienable), ("abstract", .abstract),
    ("inanimateInalienable", .inanimateInalienable), ("inanimateAlienable", .inanimateAlienable)]

/-- The schema and notion of each Telugu row (85). -/
def teluguData : List (Schema × Notion) :=
  (Examples.all.filter fun r ↦ r.language = .telugu).filterMap fun r ↦ do
    pure (← schema r, ← notion r)

theorem telugu_notions : ∀ d ∈ teluguData, d.1 = .location ↔ d.2 = .physical := by
  decide +kernel

end Heine1997
