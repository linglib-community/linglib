module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs
public import Linglib.Data.Examples.Sorace2000
public import Linglib.Data.Examples.Languages
public import Linglib.Languages.Dutch.Verbs
public import Linglib.Languages.German.Verbs
public import Linglib.Languages.Romance.French.Verbs
public import Linglib.Languages.Romance.Italian.Verbs

/-!
# Sorace (2000): Gradients in auxiliary selection with intransitive verbs

[sorace-2000] orders the monadic intransitive verbs of Italian, French, Dutch and German by their
aspectual and thematic type on the Auxiliary Selection Hierarchy, `AuxiliarySelectionHierarchy`:
the transitions and states by decreasing telicity, then the processes by increasing control. The
verbs at the two ends choose their auxiliary in every language and every sentence, a verb of
change of location *be* (`changeOfLocation_selects_be`) and a verb of controlled nonmotional
process *have* (`nonmotionalProcess_selects_have`), and the types between them are exactly those
with a verb that takes both auxiliaries alike (`free_alternation_iff`).

A sentence *selects* an auxiliary when the paper judges it acceptable with that auxiliary and
with no other it prints, and does not merely attest it. For a language $l$ and an auxiliary $a$, `Language.typesWith l a` is the
set of types of the verbs whose sentences select $a$, among the sentences that keep the default
predicate and subject of their type. Each language draws its boundary between *be* and *have* in
the sense that, along the types it attests, its *be* types form a lower set and its *have* types
an upper set (`typesWith_ordered`): a type whose verbs all take *be* lies below every type with a
verb that takes *have*, and a type whose verbs all take *have* above every type with a verb that
takes *be*. A language varies on the types with verbs of both kinds: none in Italian, a change
and the continuation of a state in French, the continuation and the existence of a state in
Dutch, and these two and motional process in German. The cutoff points of $l$,
`Language.cutoffs l`, are the types that bound its *be* types above and its *have* types below,
the interval from the highest *be* type to the lowest *have* type (`cutoffs_eq_Icc`). Only Italian
has any, the existence of a state and uncontrolled process, where the states end and the
processes begin (`cutoffs_italian`, `cutoffs_eq_empty`).

The order entails part of the paper's typological prediction: a language whose verbs of change of
location admit *have* has no type whose verbs consistently take *be*
(`subset_of_changeOfLocation_mem`), and dually at the other end of the hierarchy. It does not
exclude a type whose verbs consistently take *have* while change of location varies
(`exists_ordered_bot_varies`).

A directional phrase moves Dutch and German verbs of motion to *be* and leaves French ones with
*have* (`directional_motionalProcess`).

An example marks its auxiliary and its participle, each with the lexeme it is a form of, and the
study reads it through the typed readers of `Examples.Example`. A verb with an entry in its
language's language file is mapped to it. Where the paper accepts an auxiliary that the language
file's entry
does not record for the verb, the verb is at neither end of the hierarchy
(`position_mem_Ioo_of_not_mem_perfectAuxiliaries`).

## Implementation notes

* The paper classifies verbs, not sentences, so the type of a verb is a function of its lexeme,
  `Examples.Lexeme.position?`, read from the section of the paper that discusses it. *Cedere*
  'yield', from the controlled affecting processes, a subclass of the controlled processes, is a
  nonmotional process.
* The diacritics are read on the `Judgment` scale: unmarked is acceptable, `?` marginal, `??`
  questionable, `?*` and `*?` unacceptable, `*` ungrammatical.
* A sentence printed with one auxiliary selects it where it is acceptable, as the paper prints such
  sentences to show the auxiliary a verb takes; a sentence printed with both and judged alike
  selects neither, and an example attested in a text or cited from a grammar, which shows that an
  auxiliary is possible but not that another is not, selects nothing. The boundary is read off the sentences that keep their type's default: an
  example records a phrase that changes the telicity of the predicate, or a subject whose
  agentivity departs from the default, where the paper points to one.
* Omitted examples: frozen *be* in Romanian and English, which have no choice of auxiliary; the
  anticausatives, dyadic and off the hierarchy, except the one change-of-location verb printed
  with *have*; and the sense 'be elusive' of *échapper*, which the paper places on no type.
* The discussion of the projectionist and constructional models of the lexicon-syntax interface is
  argument, not formalized here.

## References

* [sorace-2000]
* [van-hout-1993]
* [maiden-robustelli-2007]
* [broekhuis-corver-2026e]
* [durrell-2011]
* [grevisse-goosse-2008]
-/

@[expose] public section

namespace Sorace2000

open ArgumentStructure
open Verb (PerfectAuxiliary)
open Examples (Example)

/-- The four languages of the paper. -/
inductive Language
  | italian | french | dutch | german
  deriving DecidableEq, Repr, Fintype

/-- The Glottocode of a language. -/
def Language.glottocode : Language → Glottocode
  | .italian => .italian
  | .french => .french
  | .dutch => .dutch
  | .german => .german

/-! ### The lexemes -/

namespace Examples.Lexeme

/-- The type of a verb on the hierarchy, from the section of the paper that discusses it. -/
def position? : Lexeme → Option AuxiliarySelectionHierarchy
  -- §3.1
  | venire | arriver | komen | ankommen | arrivare | cadere => some .changeOfLocation
  -- §3.2
  | salire | marcire | fiorire | naitre | sterven | gebaren | groeien | steigen | stijgen
  | devenir | rougir | paraitre | echapper => some .changeOfState
  -- §3.3
  | rimanere | durare | survivre | halten | verweilen | overblijven | duren | rester | blijven
  | bleiben => some .continuationOfState
  -- §3.4
  | esistere | bastare | sembrare | appartenere | scarseggiare | exister | gefallen | genugen
  | liegen | abhangen | staan | bestaan | blijken | sein | zijn => some .existenceOfState
  -- §4.4
  | tentennare | tossire | squillare | risuonare | rimbombare | rintoccare | piovere | nevicare
  | grandinare | tuonare | lampeggiare => some .uncontrolledProcess
  -- §4.3
  | correre | lopen | nager | rennen | laufen | schwimmen | rollen | tanzen | nuotare | courir
  | saltare | atterrare => some .motionalProcess
  -- §4.1, §4.2
  | chiacchierare | travailler | blazen | arbeiten | funzionare | lavorare
  | cedere => some .nonmotionalProcess
  | essere | avere | etre | avoir | hebben | haben => none

/-- The auxiliary a lexeme is, where it is one. -/
def auxiliary? : Lexeme → Option PerfectAuxiliary
  | essere | etre | zijn | sein => some .be
  | avere | avoir | hebben | haben => some .have
  | _ => none

end Examples.Lexeme

/-! ### The examples -/

namespace Examples.Example

/-- The auxiliary of the example's perfect. -/
def auxiliary? (x : Example) : Option PerfectAuxiliary :=
  (x.lexemes .auxiliary).head?.bind (·.auxiliary?)

/-- The verb of the example, the lexeme of its participle. -/
def verb? (x : Example) : Option Lexeme := (x.lexemes .participle).head?

/-- The type of the example's verb. -/
def position? (x : Example) : Option AuxiliarySelectionHierarchy := x.verb?.bind (·.position?)

/-- The judgment of the example with the auxiliary `a`, where the paper prints it with `a`. -/
def judgment? (x : Example) (a : PerfectAuxiliary) : Option Judgment :=
  if x.auxiliary? = some a then some x.datum.judgment else x.datum.contrasts.head?.map (·.2)

/-- The example is a sentence of the language `l`. -/
def In (x : Example) (l : Language) : Prop := x.datum.language = l.glottocode

instance (x : Example) (l : Language) : Decidable (x.In l) :=
  inferInstanceAs (Decidable (_ = _))

/-- The example selects `a` when the paper judges it acceptable with `a` and with no other
auxiliary it prints, and does not merely attest it or cite it from a grammar. -/
def Selects (x : Example) (a : PerfectAuxiliary) : Prop :=
  x.datum.method ≠ some .corpus ∧ x.datum.method ≠ some .description ∧
    x.judgment? a = some .acceptable ∧ ∀ b ≠ a, x.judgment? b ≠ some .acceptable

instance (x : Example) (a : PerfectAuxiliary) : Decidable (x.Selects a) := by
  unfold Selects; infer_instance

end Examples.Example

-- every example has an auxiliary, a verb on the hierarchy and one of the four languages
theorem example_complete :
    ∀ x : Example, x.auxiliary?.isSome ∧ x.position?.isSome ∧ ∃ l, x.In l := by
  decide

/-! ### The core -/

/-- A verb of change of location takes *be* and rejects *have* in all four languages. -/
theorem changeOfLocation_selects_be : ∀ x : Example, x.position? = some .changeOfLocation →
    (∀ j ∈ x.judgment? .be, j = .acceptable) ∧ ∀ j ∈ x.judgment? .have, j = .ungrammatical := by
  decide

/-- A verb of controlled nonmotional process takes *have* in all four languages, and *be* at best
marginally. -/
theorem nonmotionalProcess_selects_have : ∀ x : Example, x.position? = some .nonmotionalProcess →
    (∀ j ∈ x.judgment? .have, j = .acceptable) ∧ ∀ j ∈ x.judgment? .be, j ≤ .marginal := by
  decide

/-- Some verb of a type takes both auxiliaries acceptably exactly when the type is not at either
end of the hierarchy. -/
theorem free_alternation_iff (t : AuxiliarySelectionHierarchy) :
    (∃ x : Example, x.position? = some t ∧ x.judgment? .be = some .acceptable ∧
      x.judgment? .have = some .acceptable) ↔ t ≠ ⊥ ∧ t ≠ ⊤ := by
  revert t; decide

/-! ### The boundary -/

/-- The types of the verbs whose sentences in `l` select `a`, among the sentences that depart from
the default of their type in neither predicate nor subject. -/
def Language.typesWith (l : Language) (a : PerfectAuxiliary) :
    Finset AuxiliarySelectionHierarchy :=
  ({x : Example | x.In l ∧ x.predicate = none ∧ x.subject = none ∧ x.Selects a} :
    Finset Example).biUnion (·.position?.toFinset)

/-- Along the types a language attests, its *be* types form a lower set and its *have* types an
upper set. -/
theorem typesWith_ordered (l : Language) :
    AntitoneOn (· ∈ l.typesWith .be) ↑(l.typesWith .be ∪ l.typesWith .have) ∧
      MonotoneOn (· ∈ l.typesWith .have) ↑(l.typesWith .be ∪ l.typesWith .have) := by
  simp only [AntitoneOn, MonotoneOn, Finset.mem_coe, le_Prop_eq]
  refine ⟨?_, ?_⟩ <;> cases l <;> decide

-- §6, fn. 32: a language whose *have* types form an upper set of its attested types, and whose
-- verbs of change of location admit *have*, takes *have* in every type in which it takes *be*
theorem subset_of_changeOfLocation_mem {B H : Set AuxiliarySelectionHierarchy}
    (h : MonotoneOn (· ∈ H) (B ∪ H)) (hH : .changeOfLocation ∈ H) : B ⊆ H :=
  fun _ hb ↦ h (.inr hH) (.inl hb) bot_le hH

-- §6, at the other end of the hierarchy
theorem subset_of_nonmotionalProcess_mem {B H : Set AuxiliarySelectionHierarchy}
    (h : AntitoneOn (· ∈ B) (B ∪ H)) (hB : .nonmotionalProcess ∈ B) : H ⊆ B :=
  fun _ hh ↦ h (.inr hh) (.inl hB) le_top hB

-- the order allows *have* to be consistent at a type while change of location varies
theorem exists_ordered_bot_varies : ∃ B H : Finset AuxiliarySelectionHierarchy,
    AntitoneOn (· ∈ B) ↑(B ∪ H) ∧ MonotoneOn (· ∈ H) ↑(B ∪ H) ∧ ⊥ ∈ B ∩ H ∧
      .uncontrolledProcess ∈ H \ B := by
  refine ⟨{⊥}, {⊥, .uncontrolledProcess}, ?_, ?_, by decide, by decide⟩ <;>
    simp only [AntitoneOn, MonotoneOn, Finset.mem_coe, le_Prop_eq] <;> decide

-- §3.4, (20); the alternations of (21) are attested
theorem italian_varies :
    Language.italian.typesWith .be ∩ Language.italian.typesWith .have = ∅ := by
  decide

-- §3.2, (12) against (13); §3.3, (19a) against (16)
theorem french_varies : Language.french.typesWith .be ∩ Language.french.typesWith .have =
    {.changeOfState, .continuationOfState} := by
  decide

-- (18), (19b) and (24)
theorem dutch_varies : Language.dutch.typesWith .be ∩ Language.dutch.typesWith .have =
    {.continuationOfState, .existenceOfState} := by
  decide

-- (17), (19c); (23), (25a); (38) against (40a)
theorem german_varies : Language.german.typesWith .be ∩ Language.german.typesWith .have =
    {.continuationOfState, .existenceOfState, .motionalProcess} := by
  decide

/-- §6: the cutoff points of a language, the types that bound its *be* types above and its *have*
types below. -/
def Language.cutoffs (l : Language) : Set AuxiliarySelectionHierarchy :=
  upperBounds ↑(l.typesWith .be) ∩ lowerBounds ↑(l.typesWith .have)

theorem cutoffs_eq_Icc (l : Language) :
    l.cutoffs = Set.Icc ((l.typesWith .be).sup id) ((l.typesWith .have).inf id) := by
  rw [Language.cutoffs, Finset.isLUB_sup_id.upperBounds_eq, Finset.isGLB_inf_id.lowerBounds_eq,
    Set.Ici_inter_Iic]

-- §6, (20) against (37), (41), (44)–(47) and (50)
theorem cutoffs_italian :
    Language.italian.cutoffs = Set.Icc .existenceOfState .uncontrolledProcess := by
  rw [cutoffs_eq_Icc, show (Language.italian.typesWith .be).sup id = .existenceOfState by decide,
    show (Language.italian.typesWith .have).inf id = .uncontrolledProcess by decide]

-- §6, "the cutoff point cannot be identical in all languages"; fn. 17
theorem cutoffs_eq_empty (l : Language) (hl : l ≠ .italian) : l.cutoffs = ∅ := by
  rw [cutoffs_eq_Icc, Set.Icc_eq_empty_iff]
  revert l; decide

/-! ### Directional phrases -/

-- §4.3, (39), (40) against (42b)
theorem directional_motionalProcess : ∀ x : Example, x.position? = some .motionalProcess →
    x.predicate = some .telicized →
    (x.In .dutch ∨ x.In .german → x.Selects .be) ∧ (x.In .french → x.Selects .have) := by
  decide

-- §4.3, (41b) against (41d): *correre* 'run' moves to *essere*, *nuotare* 'swim' does not
theorem italian_directional_split :
    (∃ x : Example, x.verb? = some .correre ∧ x.predicate = some .telicized ∧ x.Selects .be) ∧
      ∃ x : Example, x.verb? = some .nuotare ∧ x.predicate = some .telicized ∧
        x.Selects .have := by
  decide

/-! ### The language files -/

/-- The entry of a verb in its language's language file, where the language file has one. -/
def Examples.Lexeme.entry? : Examples.Lexeme → Option Verb
  | .venire => some Italian.Verbs.venire.toVerb
  | .arrivare => some Italian.Verbs.arrivare.toVerb
  | .cadere => some Italian.Verbs.cadere.toVerb
  | .salire => some Italian.Verbs.salire.toVerb
  | .marcire => some Italian.Verbs.marcire.toVerb
  | .fiorire => some Italian.Verbs.fiorire.toVerb
  | .rimanere => some Italian.Verbs.rimanere.toVerb
  | .durare => some Italian.Verbs.durare.toVerb
  | .esistere => some Italian.Verbs.esistere.toVerb
  | .bastare => some Italian.Verbs.bastare.toVerb
  | .sembrare => some Italian.Verbs.sembrare.toVerb
  | .appartenere => some Italian.Verbs.appartenere.toVerb
  | .chiacchierare => some Italian.Verbs.chiacchierare.toVerb
  | .lavorare => some Italian.Verbs.lavorare.toVerb
  | .correre => some Italian.Verbs.correre.toVerb
  | .saltare => some Italian.Verbs.saltare.toVerb
  | .nuotare => some Italian.Verbs.nuotare.toVerb
  | .tossire => some Italian.Verbs.tossire.toVerb
  | .squillare => some Italian.Verbs.squillare.toVerb
  | .arriver => some French.Verbs.arriver
  | .naitre => some French.Verbs.naitre
  | .devenir => some French.Verbs.devenir
  | .rougir => some French.Verbs.rougir
  | .paraitre => some French.Verbs.paraitre
  | .survivre => some French.Verbs.survivre
  | .rester => some French.Verbs.rester
  | .exister => some French.Verbs.exister
  | .travailler => some French.Verbs.travailler
  | .nager => some French.Verbs.nager
  | .courir => some French.Verbs.courir
  | .komen => some Dutch.Verbs.komen.toVerb
  | .sterven => some Dutch.Verbs.sterven.toVerb
  | .groeien => some Dutch.Verbs.groeien.toVerb
  | .stijgen => some Dutch.Verbs.stijgen.toVerb
  | .blijven => some Dutch.Verbs.blijven.toVerb
  | .overblijven => some Dutch.Verbs.overblijven.toVerb
  | .duren => some Dutch.Verbs.duren.toVerb
  | .staan => some Dutch.Verbs.staan.toVerb
  | .bestaan => some Dutch.Verbs.bestaan.toVerb
  | .blazen => some Dutch.Verbs.blazen.toVerb
  | .lopen => some Dutch.Verbs.lopen.toVerb
  | .rollen => some Dutch.Verbs.rollen.toVerb
  | .ankommen => some German.Verbs.ankommen.toVerb
  | .bleiben => some German.Verbs.bleiben.toVerb
  | .liegen => some German.Verbs.liegen.toVerb
  | .arbeiten => some German.Verbs.arbeiten.toVerb
  | .rennen => some German.Verbs.rennen.toVerb
  | .laufen => some German.Verbs.laufen.toVerb
  | .tanzen => some German.Verbs.tanzen.toVerb
  | _ => none

-- each entry is written as the example names the lexeme of its span
theorem entry?_form : ∀ x : Example, ∀ s ∈ x.datum.spans, ∀ l ∈ Examples.lexeme? s,
    ∀ v ∈ l.entry?, s.lexeme = some v.form := by
  decide +kernel

-- each entry's basic frame, the first, has no complement
theorem entry?_intransitive : ∀ l : Examples.Lexeme, ∀ v ∈ l.entry?,
    (v.valency.frames.headD .intransitive).IsIntransitive := by
  decide

-- (8a), (11), (21a), (23c), (47a): the paper accepts an auxiliary the language file's entry lacks
theorem acceptable_not_mem_perfectAuxiliaries :
    ({x : Example | ∃ v ∈ x.verb?.bind (·.entry?), ∃ a, x.judgment? a = some .acceptable ∧
      v.perfectAuxiliaries.Nonempty ∧ a ∉ v.perfectAuxiliaries} : Finset Example) =
      {.ex8a, .ex11, .ex21a, .ex23c, .ex47a} := by
  decide +kernel

/-- Where the paper accepts an auxiliary that the language file's entry does not record for a verb,
the
verb is at neither end of the hierarchy. -/
theorem position_mem_Ioo_of_not_mem_perfectAuxiliaries : ∀ x : Example,
    ∀ v ∈ x.verb?.bind (·.entry?), ∀ a, x.judgment? a = some .acceptable →
      v.perfectAuxiliaries.Nonempty → a ∉ v.perfectAuxiliaries →
        ∀ t ∈ x.position?, t ∈ Set.Ioo ⊥ ⊤ := by
  decide +kernel

end Sorace2000
