module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Fragments.Norwegian.WordOrder
public import Linglib.Fragments.English.WordOrder
public import Linglib.Fragments.German.WordOrder
public import Linglib.Fragments.Danish.WordOrder
public import Linglib.Data.Examples.Westergaard2009
public import Linglib.Semantics.Focus.Marking
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Readers

/-!
# Westergaard (2009): The Acquisition of Word Order: Micro-Cues, Information Structure, and Economy

Westergaard argues that verb second is not a single parameter but a family of micro-parameters, one
for each clause-type head of a split ForceP: Decl⁰, Int⁰, Pol⁰, Excl⁰ and Imp⁰ for root
declaratives, wh-questions, yes/no-questions, exclamatives and imperatives, and Fin⁰ and Wh⁰ for
embedded declaratives and embedded questions whose head no complementizer fills. A language sets
each head positively or negatively, and her Table 3.1 gives the settings of six Germanic varieties.
Measured against the word order of those varieties, each grammar contains the [heads](##heads)
where verb second is required and lies within those where it is allowed: for five of the six it is
[exactly the required heads](##table_3_1_eq_required), and [the Danish one](##danish_table_3_1) is
the heads where verb second is possible. The exception is Imp⁰, which [only Belfast English
sets](##imp_row): it is movement of the verb past an overt subject, while the imperatives of
Norwegian and German front their verb without counting as movement to Imp⁰. [Each of her examples
has a word order its variety allows](##rows_consistent).

What children acquire, on this view, are micro-cues: pieces of structure stating for one clause
type what its specifier holds and whether the finite verb fills its head. [Four cues separate the
five grammars of Table 3.2](##table_3_2).

In the Tromsø dialect the monosyllabic *wh*-words *ka* 'what', *kem* 'who' and *kor* 'where' are
heads that occupy Int⁰ themselves and so block verb movement there. The verb second that still
occurs is movement to a lower Top⁰, whose feature a given subject checks from the specifier and a
focused subject leaves to the verb, so that [these questions are verb second exactly when the
subject is new](##isV2_order_iff).

## Implementation notes

* The word order of each variety is its fragment's distribution of verb second over sentence types
  and embedding contexts, read off the left edges the fragment admits for Norwegian, Danish and
  German. A grammar's [heads](##heads) are read off it: the root heads from the verb-second
  distribution, Fin⁰ and Wh⁰ from the left edges without a complementizer, at the
  `quasiSubordinated` cells of Bhatt and Dayal where the complements of bridge and rogative verbs
  lie. Her Wh⁰ is the yes/no cell her Belfast example instantiates.
* Fin⁰ is verb movement in an embedded declarative whose head no complementizer fills (p. 40).
  German verb second after a bridge verb is optional, excluded with *dass* and required without it,
  while Norwegian verb second there is optional with and without *at* (36), which her table marks
  as no movement to Fin⁰.
* Imp⁰ is movement of the verb past an overt imperative subject, which Belfast English shows (19).
  Norwegian and German imperatives leave the forefield empty and front the verb, as Faarlund, Lie
  and Vannebo and Truckenbrodt describe them, so their fragments require verb second there; the
  heads compared with the table leave Imp⁰ out.
* Only some Danish exclamatives are verb second, which her table counts as movement to Excl⁰. The
  Danish fragment takes its exclamative cell from Westergaard and the others from Vikner, and
  leaves the imperative unrecorded.
* The cues (57) and (60) for verb movement to I°, which she motivates with Icelandic, the cue for
  English inflectional elements, *som*-insertion, focus-sensitive adverbs, *kanskje*, and the
  acquisition chapters are not formalized. The Tromsø rows have no fragment and enter only the
  *wh*-word model.

## References

* [westergaard-2009]
* [rizzi-1997]
* [henry-1997]
* [vikner-1995]
-/

@[expose] public section

namespace Westergaard2009

open Clause

/-- A verb-second grammar in Westergaard's sense: the clause-type heads the finite verb moves to,
each taken as the cell it types, a sentence type in an embedding context. -/
abbrev V2Grammar := SetRel SentenceType EmbeddingContext

/-! ### Micro-parameters (Table 3.1) -/

/-- Standard Norwegian moves the verb to Decl⁰, Int⁰ and Pol⁰. -/
abbrev stdNorwegian : V2Grammar := {root .declarative, root .constituent, root .polar}

/-- Standard English moves the verb to Int⁰ and Pol⁰. -/
abbrev stdEnglish : V2Grammar := {root .constituent, root .polar}

/-- Nordmøre Norwegian moves the verb to Decl⁰ and Pol⁰. -/
abbrev nordmore : V2Grammar := {root .declarative, root .polar}

/-- Belfast English moves the verb to Int⁰, Pol⁰, Imp⁰ and Wh⁰, the last in an embedded
yes/no-question without a complementizer. -/
abbrev belfast : V2Grammar :=
  {root .constituent, root .polar, root .imperative, (.polar, .quasiSubordinated)}

/-- German moves the verb to Decl⁰, Int⁰, Pol⁰ and, in an embedded declarative without a
complementizer, Fin⁰. -/
abbrev german : V2Grammar :=
  {root .declarative, root .constituent, root .polar, (.declarative, .quasiSubordinated)}

/-- Danish moves the verb to Decl⁰, Int⁰, Pol⁰ and Excl⁰. -/
abbrev danish : V2Grammar := {root .declarative, root .constituent, root .polar, root .exclamative}

/-- The heads other than Imp⁰ that a variety sets at the occurrences in `s`: the root clause-type
heads read off its verb-second distribution `d`, and Fin⁰ and Wh⁰ off the embedded cells of its
distribution `bare` in clauses without a complementizer, which by default records nothing. Imp⁰ is
left out, since Westergaard diagnoses it by an overt subject the verb precedes rather than by the
verb's place at the left edge. -/
def heads (s : Set Occurrence) (d : Distribution) (bare : Distribution := .empty) :
    V2Grammar :=
  {c ∈ d.preimage s | c.2 = .matrix ∧ c.1 ≠ .imperative} ∪ {c ∈ bare.preimage s | c.2 ≠ .matrix}

instance {s : Set Occurrence} [DecidablePred (· ∈ s)] {d bare : Distribution} :
    DecidablePred (· ∈ heads s d bare) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∨ _ ∧ _))

/-- Away from Imp⁰, Table 3.1 sets exactly the heads where verb second is required for Standard
Norwegian, Standard English, Nordmøre, Belfast English and German. -/
theorem table_3_1_eq_required :
    heads {.obligatory} Norwegian.verbSecond (Norwegian.leftEdges.restrict false).verbSecond =
        stdNorwegian ∧
      heads {.obligatory} English.verbSecond = stdEnglish ∧
      heads {.obligatory} Norwegian.Nordmore.verbSecond = nordmore ∧
      heads {.obligatory} English.Belfast.verbSecond
        English.Belfast.verbSecondWithoutComplementizer = belfast \ {root .imperative} ∧
      heads {.obligatory} German.verbSecond (German.leftEdges.restrict false).verbSecond =
        german := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext c <;> revert c <;> decide

/-- Table 3.1's Danish grammar contains the heads where verb second is required and is the heads
where it is possible, since Westergaard counts verb second in some exclamatives as movement to
Excl⁰. -/
theorem danish_table_3_1 :
    heads {.obligatory} Danish.verbSecond (Danish.leftEdges.restrict false).verbSecond ⊆ danish ∧
      heads {.excluded}ᶜ Danish.verbSecond (Danish.leftEdges.restrict false).verbSecond =
        danish := by
  refine ⟨fun c ↦ ?_, Set.ext fun c ↦ ?_⟩ <;> revert c <;> decide

-- Imp⁰ is Belfast English's inversion past an overt subject, (19) p. 41 and note 4 p. 19: the
-- Norwegian and German imperatives front their verb too, but Table 3.1 does not count it.
theorem imp_row :
    root .imperative ∈ belfast ∧ root .imperative ∈ English.Belfast.verbSecond.required ∧
      root .imperative ∈ Norwegian.verbSecond.required ∧ root .imperative ∉ stdNorwegian ∧
      root .imperative ∈ German.verbSecond.required ∧ root .imperative ∉ german := by
  decide

-- p. 40
theorem nordmore_english_mirror :
    root .declarative ∈ Norwegian.Nordmore.verbSecond.required ∧
      root .constituent ∉ Norwegian.Nordmore.verbSecond.required ∧
      root .declarative ∉ English.verbSecond.required ∧
      root .constituent ∈ English.verbSecond.required := by
  decide

/-! ### Micro-cues (§4) -/

/-- The specifier of the cue's head holds nothing, a non-subject phrase, or a *wh*-element. -/
inductive Filler
  | none | xp | wh
  deriving DecidableEq, Repr

/-- A micro-cue: for one cell, what its specifier holds and whether the finite verb fills its
head. -/
structure MicroCue where
  target : SentenceType × EmbeddingContext
  spec : Filler
  verbInHead : Bool
  deriving DecidableEq, Repr

/-- The cue (45) is V2 in *wh*-questions. -/
def cueIntV2 : MicroCue := ⟨root .constituent, .wh, true⟩

/-- The cue (46) is V2 in declaratives. -/
def cueDeclV2 : MicroCue := ⟨root .declarative, .xp, true⟩

/-- The cue (49) is V2 in yes/no-questions. -/
def cuePolV2 : MicroCue := ⟨root .polar, .none, true⟩

/-- The cue (52) is V2 in exclamatives. -/
def cueExclV2 : MicroCue := ⟨root .exclamative, .wh, true⟩

/-- The cue (53) is V2 in embedded questions, here Belfast English's embedded yes/no-question. -/
def cueWhV2 : MicroCue := ⟨(.polar, .quasiSubordinated), .wh, true⟩

/-- The cue (54) is V2 in imperatives. -/
def cueImpV2 : MicroCue := ⟨root .imperative, .none, true⟩

/-- The cue (58) is non-V2 in exclamatives. -/
def cueExclNonV2 : MicroCue := ⟨root .exclamative, .wh, false⟩

/-- The cue (59) is non-V2 in embedded questions. -/
def cueWhNonV2 : MicroCue := ⟨(.polar, .quasiSubordinated), .wh, false⟩

/-- A grammar expresses a cue when its setting for the cue's cell is the cue's. -/
def Expresses (lang : V2Grammar) (c : MicroCue) : Prop := c.target ∈ lang ↔ c.verbInHead = true

instance (lang : V2Grammar) (c : MicroCue) [Decidable (c.target ∈ lang)] :
    Decidable (Expresses lang c) :=
  inferInstanceAs (Decidable (_ ↔ _))

theorem not_expresses_both (lang : V2Grammar) {c c' : MicroCue} (ht : c.target = c'.target)
    (hv : c.verbInHead ≠ c'.verbInHead) : ¬ (Expresses lang c ∧ Expresses lang c') :=
  fun ⟨h, h'⟩ ↦ hv <| Bool.eq_iff_iff.2 <| h.symm.trans (ht ▸ h')

/-- The four cues of Table 3.2. -/
def tableCues : List MicroCue := [cueIntV2, cueDeclV2, cueExclV2, cueWhV2]

/-- The five grammars of Table 3.2. -/
def tableGrammars : List V2Grammar := [stdNorwegian, stdEnglish, nordmore, belfast, danish]

/-- Table 3.2 shows that the four cues separate the five grammars: any two differ on some cue. -/
theorem table_3_2 :
    tableGrammars.Pairwise fun g g' ↦
      ∃ c ∈ tableCues, ¬ (Expresses g c ↔ Expresses g' c) := by
  simp [tableGrammars, tableCues, Expresses, cueIntV2, cueDeclV2, cueExclV2, cueWhV2]

theorem norwegian_nonV2_cues :
    Expresses stdNorwegian cueExclNonV2 ∧ Expresses stdNorwegian cueWhNonV2 := by
  simp [Expresses, cueExclNonV2, cueWhNonV2]

/-! ### The rows -/

/-- The cell of each value of the `clause` feature; an embedded question is Belfast English's
yes/no-question. -/
def clauseCells : List (String × SentenceType × EmbeddingContext) :=
  [("declarative", root .declarative), ("subject-initial declarative", root .declarative),
    ("non-subject-initial declarative", root .declarative), ("wh-question", root .constituent),
    ("yes/no-question", root .polar), ("imperative", root .imperative),
    ("exclamative", root .exclamative), ("embedded declarative", embedded .declarative),
    ("embedded question", (.polar, .quasiSubordinated))]

/-- The cell a row records: that of its `clause` feature, or a root wh-question for a row with a
`wh` feature only, in the quasi-subordinated context when it follows a bridge verb. -/
def cellOf (r : Datum) : Option (SentenceType × EmbeddingContext) :=
  let cell := match r.feature? "clause" with
    | some s => clauseCells.lookup s
    | none => (r.feature? "wh").map fun _ ↦ root .constituent
  cell.map fun c ↦ (r.parse? "embedding" [("bridge verb", .quasiSubordinated)]).elim c (c.1, ·)

/-- The orders a row's `order` feature attests, as an occurrence of verb movement: the moved
order alone, as in V2 and in the V1 of a yes/no-question, the unmoved one alone, or both. -/
def orderOf (r : Datum) : Option Occurrence :=
  r.parse? "order"
    [("V2", .obligatory), ("V1", .obligatory), ("non-V2", .excluded), ("non-V2 or V2", .optional),
      ("V2 or non-V2", .optional)]

/-- The fragments of a row's variety, Standard Norwegian, Nordmøre, Standard or Belfast English
or Danish: its verb-second distribution and its distribution in embedded clauses without a
complementizer. The Tromsø rows have none. -/
def fragmentsOf (r : Datum) : Option (Distribution × Distribution) :=
  match r.feature? "variety", r.language with
  | some "Nordmøre", _ => some (Norwegian.Nordmore.verbSecond, Distribution.empty)
  | some "Belfast English", _ =>
    some (English.Belfast.verbSecond, English.Belfast.verbSecondWithoutComplementizer)
  | some "Standard Norwegian", _ | none, "norw1258" =>
    some (Norwegian.verbSecond, (Norwegian.leftEdges.restrict false).verbSecond)
  | none, "stan1293" => some (English.verbSecond, Distribution.empty)
  | none, "dani1285" => some (Danish.verbSecond, (Danish.leftEdges.restrict false).verbSecond)
  | _, _ => none

/-- The distribution a row is judged by: its variety's distribution without a complementizer
when the row has none, otherwise its verb-second distribution. -/
def grammarOf (r : Datum) : Option Distribution :=
  (fragmentsOf r).map fun p ↦ if r.feature? "complementizer" = some "none" then p.2 else p.1

/-- Every judged word order in the data falls on a cell the fragment of its variety records and
is allowed there, apart from the *kanskje* rows, which the chapter treats as a lexical
exception. -/
theorem rows_consistent :
    ∀ r ∈ Examples.all, r.feature? "adverb" = none →
      ∀ d ∈ grammarOf r, ∀ c ∈ cellOf r, ∀ o ∈ orderOf r,
        ∃ o' ∈ d c.1 c.2, o.allowed ⊆ o'.allowed := by
  decide +kernel

/-! ### *Wh*-heads and information structure (§3.2, §3.3) -/

/-- A *wh*-element is a head, sitting in Int⁰ itself, or a phrase in its specifier. -/
inductive WhStatus
  | head
  | phrase
  deriving DecidableEq, Repr

/-- A monosyllabic *wh*-word is a head, a longer one a phrase. -/
def WhStatus.ofSyllables (n : ℕ) : WhStatus := if n ≤ 1 then .head else .phrase

/-- A *wh*-head sits in Int⁰ itself and blocks verb movement to it in a root *wh*-question; a
phrase in the specifier blocks nothing. -/
def WhStatus.Blocks (w : WhStatus) (c : SentenceType × EmbeddingContext) : Prop :=
  w = .head ∧ c = root .constituent

instance : DecidableRel WhStatus.Blocks := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The *wh*-elements of the Tromsø dialect. -/
inductive TromsøWh
  | ka | kem | kor | korfor | korsen | katti
  deriving DecidableEq, Repr, Fintype

/-- The syllable count of each Tromsø *wh*-word. -/
def TromsøWh.syllables : TromsøWh → ℕ
  | .ka | .kem | .kor => 1
  | .korfor | .korsen | .katti => 2

/-- The status of each *wh*-word, by its syllable count. -/
def TromsøWh.status (w : TromsøWh) : WhStatus := .ofSyllables w.syllables

theorem tromsøWh_blocking :
    ∀ w : TromsøWh, w.status.Blocks (root .constituent) ↔ w.syllables = 1 := by
  decide

/-- Which element checks the [−foc] feature of Top⁰ in a monosyllabic *wh*-question: a
[−foc] subject from the specifier (32), otherwise the finite verb in the head (31). -/
inductive Checker
  | subject | verb
  deriving DecidableEq, Repr

/-- The checker, by the focus marking of the subject. -/
def checker : Focus.Mark → Checker
  | .unfeatured => .subject
  | .focused => .verb

/-- The words whose order the two structures fix. -/
inductive Word
  | wh | subject | verb
  deriving DecidableEq, Repr

/-- The surface order puts the *wh*-head in Int⁰, then the specifier and head of TopP, then the
rest of the clause. -/
def order (subjectFoc : Focus.Mark) : List Word :=
  match checker subjectFoc with
  | .subject => [.wh, .subject, .verb]
  | .verb => [.wh, .verb, .subject]

/-- Verb second holds when the finite verb is the second word. -/
def IsV2 (l : List Word) : Prop := l[1]? = some .verb

instance (l : List Word) : Decidable (IsV2 l) := inferInstanceAs (Decidable (_ = _))

/-- A monosyllabic *wh*-question is V2 exactly when its subject is new information. -/
theorem isV2_order_iff (subjectFoc : Focus.Mark) :
    IsV2 (order subjectFoc) ↔ subjectFoc = .focused := by
  cases subjectFoc <;> decide

end Westergaard2009
