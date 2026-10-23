module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Fragments.Norwegian.V2
public import Linglib.Fragments.English.V2
public import Linglib.Fragments.German.V2
public import Linglib.Fragments.Danish.V2
public import Linglib.Data.Examples.Westergaard2009
public import Linglib.Semantics.Focus.Marking
public import Mathlib.Tactic.DeriveFintype

/-!
# Westergaard (2009): The Acquisition of Word Order: Micro-Cues, Information Structure, and Economy

This file formalizes the syntactic model of Westergaard's monograph. Verb second is not one
parameter but a setting per clause-type head of a split ForceP, one head per sentence type in
root clauses and one each for embedded declaratives and embedded questions, so that a
language's grammar is the set of cells, a sentence type in an embedding context, in which the
finite verb moves to the left periphery. Her Table 3.1 gives that set for six Germanic
varieties. The fragments record, from the reference grammars and from her own descriptions,
where verb second is obligatory, optional or excluded, and her binary settings agree with
them: each grammar contains the cells where the fragment requires verb second and lies within
the cells where it allows it, and for five of the six varieties it is exactly the required
cells. What children acquire are micro-cues, pieces of structure stating for one cell what its
specifier holds and whether the verb fills its head, and four cues separate the five grammars
of her Table 3.2. In the Tromsø dialect the monosyllabic *wh*-words *ka*, *kem* and *kor* are
heads and sit in Int⁰ themselves, which blocks verb movement there; the verb second that still
occurs is movement to a lower Top⁰, whose feature a given subject checks from the specifier and
a focused subject leaves for the verb, so that these questions are verb second exactly when the
subject is new.

## Main definitions

* `V2Grammar`: a set of cells, the clause-type heads the finite verb moves to.
* `stdNorwegian`, `stdEnglish`, `nordmore`, `belfast`, `german`, `danish`: the grammars of
  Table 3.1.
* `MicroCue`, `Expresses`: a cue and its expression by a grammar.
* `TromsøWh`, `WhStatus`, `order`: the Tromsø *wh*-words, their status, and the word order of a
  monosyllabic *wh*-question.

## Main results

* `table_3_1_eq_required`, `danish_table_3_1`: Table 3.1 against the fragments.
* `nordmore_english_mirror`, `embedded_german_polar_all`: the mirror image and the two
  universals read off the fragments.
* `table_3_2`, `not_expresses_both`: the four cues separate the five grammars.
* `rows_consistent`: every judged word order in the data is consistent with its fragment.
* `isV2_order_iff`: a Tromsø monosyllabic *wh*-question is verb second iff its subject is new.

## Implementation notes

Westergaard's Fin⁰ and Wh⁰ heads are realized as the embedded root-like cells of Bhatt and
Dayal: German complementizer-less verb-second complements and Belfast English embedded
inversion are both `quasiSubordinated`, and her Wh⁰ is the yes/no cell her Belfast example
instantiates. Danish is the one variety whose table entry is not the fragment's required set,
since only some Danish exclamatives are verb second. The cues (57) and (60) for verb movement
to I°, which she motivates with Icelandic, the cue for English inflectional elements,
*som*-insertion, focus-sensitive adverbs, *kanskje*, and the acquisition chapters are not
formalized; the Tromsø rows have no fragment and enter only the *wh*-word model.

## References

* [westergaard-2009]
* [rizzi-1997]
* [henry-1997]
-/

@[expose] public section

namespace Westergaard2009

open Clause

/-- A verb-second grammar is the set of cells, a sentence type in an embedding context, in
which the finite verb moves to the left periphery: Westergaard's clause-type heads. -/
abbrev V2Grammar := SetRel SentenceType EmbeddingContext

/-! ### Micro-parameters (Table 3.1) -/

/-- Standard Norwegian moves the verb to Decl⁰, Int⁰ and Pol⁰. -/
abbrev stdNorwegian : V2Grammar := {root .declarative, root .constituent, root .polar}

/-- Standard English moves the verb to Int⁰ and Pol⁰. -/
abbrev stdEnglish : V2Grammar := {root .constituent, root .polar}

/-- Nordmøre Norwegian moves the verb to Decl⁰ and Pol⁰. -/
abbrev nordmore : V2Grammar := {root .declarative, root .polar}

/-- Belfast English moves the verb to Int⁰, Pol⁰, Imp⁰ and Wh⁰, the last in an embedded
root-like yes/no-question. -/
abbrev belfast : V2Grammar :=
  {root .constituent, root .polar, root .imperative, (.polar, .quasiSubordinated)}

/-- German moves the verb to Decl⁰, Int⁰, Pol⁰ and, in a complementizer-less embedded
declarative, Fin⁰. -/
abbrev german : V2Grammar :=
  {root .declarative, root .constituent, root .polar, (.declarative, .quasiSubordinated)}

/-- Danish moves the verb to Decl⁰, Int⁰, Pol⁰ and Excl⁰. -/
abbrev danish : V2Grammar := {root .declarative, root .constituent, root .polar, root .exclamative}

/-- Table 3.1 is the required set of the fragment for Standard Norwegian, Standard English,
Nordmøre, Belfast English and German. -/
theorem table_3_1_eq_required :
    Norwegian.verbSecond.required = stdNorwegian ∧ English.V2.verbSecond.required = stdEnglish ∧
      Norwegian.Nordmore.verbSecond.required = nordmore ∧
      English.V2.Belfast.verbSecond.required = belfast ∧ German.verbSecond.required = german := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext c <;> revert c <;> decide

/-- Table 3.1's Danish grammar lies between the fragment's required and possible cells, since
verb second in some exclamatives only is marked as movement to Excl⁰. -/
theorem danish_table_3_1 :
    Danish.verbSecond.required ⊆ danish ∧ danish ⊆ Danish.verbSecond.possible := by
  refine ⟨?_, ?_⟩ <;> intro c <;> revert c <;> decide

theorem nordmore_english_mirror :
    root .declarative ∈ Norwegian.Nordmore.verbSecond.required ∧
      root .constituent ∉ Norwegian.Nordmore.verbSecond.required ∧
      root .declarative ∉ English.V2.verbSecond.required ∧
      root .constituent ∈ English.V2.verbSecond.required := by
  decide

theorem embedded_german_polar_all :
    (.declarative, .quasiSubordinated) ∈ German.verbSecond.required ∧
      (.declarative, .quasiSubordinated) ∉ Norwegian.verbSecond.required ∧
      (.declarative, .quasiSubordinated) ∉ English.V2.verbSecond.required ∧
      (.declarative, .quasiSubordinated) ∉ Danish.verbSecond.required ∧
      root .polar ∈ Norwegian.verbSecond.required ∧
      root .polar ∈ English.V2.verbSecond.required ∧
      root .polar ∈ Norwegian.Nordmore.verbSecond.required ∧
      root .polar ∈ English.V2.Belfast.verbSecond.required ∧
      root .polar ∈ German.verbSecond.required ∧
      root .polar ∈ Danish.verbSecond.required := by
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

/-- The cue (53) is V2 in embedded questions, the embedded root-like yes/no-question of Belfast
English. -/
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
  fun ⟨h, h'⟩ ↦ hv (by
    unfold Expresses at h h'
    rw [ht] at h
    cases hc : c.verbInHead <;> cases hc' : c'.verbInHead <;> simp_all)

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

/-- The cell a row's `clause` or `wh` feature records; an embedded question is Belfast's
yes/no-question. -/
def cellOf (r : Datum) : Option (SentenceType × EmbeddingContext) :=
  match r.feature? "clause", r.feature? "wh" with
  | some "declarative", _ | some "subject-initial declarative", _
  | some "non-subject-initial declarative", _ => some (root .declarative)
  | some "wh-question", _ | none, some _ => some (root .constituent)
  | some "yes/no-question", _ => some (root .polar)
  | some "imperative", _ => some (root .imperative)
  | some "exclamative", _ => some (root .exclamative)
  | some "embedded declarative", _ => some (embedded .declarative)
  | some "embedded question", _ => some (.polar, .quasiSubordinated)
  | _, _ => none

/-- A row records the verb as moved, as in V2 and in the V1 of a yes/no-question, as unmoved,
or as either. -/
inductive Order
  | moved | unmoved | either
  deriving DecidableEq, Repr

/-- The order a row's `order` feature records. -/
def orderOf (r : Datum) : Option Order :=
  r.parse? "order"
    [("V2", .moved), ("V1", .moved), ("non-V2", .unmoved), ("non-V2 or V2", .either),
      ("V2 or non-V2", .either)]

/-- The fragment of a row's variety, Standard Norwegian, Nordmøre, Standard or Belfast English
or Danish; the Tromsø rows have none. -/
def grammarOf (r : Datum) : Option Distribution :=
  match r.feature? "variety", r.language with
  | some "Nordmøre", _ => some Norwegian.Nordmore.verbSecond
  | some "Belfast English", _ => some English.V2.Belfast.verbSecond
  | some "Standard Norwegian", _ | none, "norw1258" => some Norwegian.verbSecond
  | none, "stan1293" => some English.V2.verbSecond
  | none, "dani1285" => some Danish.verbSecond
  | _, _ => none

/-- An order is consistent with a distribution at a cell when a moved verb sits where verb
second is possible, an unmoved one where it is not required, and either where it is optional. -/
def Order.Consistent (d : Distribution) (c : SentenceType × EmbeddingContext) : Order → Prop
  | .moved => c ∈ d.possible
  | .unmoved => c ∉ d.required
  | .either => c ∈ d.possible ∧ c ∉ d.required

instance (d : Distribution) (c : SentenceType × EmbeddingContext) :
    DecidablePred (Order.Consistent d c)
  | .moved => inferInstanceAs (Decidable (_ ∈ _))
  | .unmoved => inferInstanceAs (Decidable (_ ∉ _))
  | .either => inferInstanceAs (Decidable (_ ∧ _))

theorem rows_consistent :
    ∀ r ∈ Examples.all, r.feature? "adverb" = none →
      ∀ d ∈ grammarOf r, ∀ c ∈ cellOf r, ∀ o ∈ orderOf r, o.Consistent d c := by
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

/-- Their syllable counts. -/
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

theorem isV2_order_iff (subjectFoc : Focus.Mark) :
    IsV2 (order subjectFoc) ↔ subjectFoc = .focused := by
  cases subjectFoc <;> decide

end Westergaard2009
