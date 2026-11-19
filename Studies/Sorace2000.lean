module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Monotone.Defs
public import Linglib.Data.Examples.Sorace2000
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages
public import Linglib.Fragments.Dutch.Verbs
public import Linglib.Fragments.German.Verbs
public import Linglib.Fragments.Romance.French.Verbs
public import Linglib.Fragments.Romance.Italian.Verbs

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
with no other it prints. For a language $l$ and an auxiliary $a$, `Language.typesWith l a` is the
set of types of the verbs whose sentences select $a$, among the sentences that keep the default
predicate and subject of their type. Each language draws its boundary between *be* and *have* in
the sense that, along the types it attests, its *be* types form a lower set and its *have* types
an upper set (`typesWith_ordered`): a type whose verbs all take *be* lies below every type with a
verb that takes *have*, and a type whose verbs all take *have* above every type with a verb that
takes *be*. A language varies on the types with verbs of both kinds: the existence of a state in
Italian, a change and the continuation of a state in French, the continuation and the existence of
a state in Dutch, and these two and motional process in German. Only Italian varies on a single
type, and so only Italian has a cutoff point on the hierarchy itself (`italian_cutoff`); the
others need adjacent types merged. The paper's typological prediction follows from the order: a
language whose verbs of change of location admit *have* has no type whose verbs consistently take
*be* (`subset_of_changeOfLocation_mem`).

A directional phrase moves Dutch and German verbs of motion to *be* and leaves French ones with
*have* (`directional_motionalProcess`).

A row marks its auxiliary and its participle, each with the lexeme it is a form of. A verb with an
entry in its language's fragment is mapped to it, and the auxiliary each reference grammar gives
an entry is the one its sentences select, except for an attested *avere* with *bastare* 'be
enough', which the Italian grammar does not give (`selects_not_mem_perfectAuxiliaries`).

## Implementation notes

* The paper classifies verbs, not sentences, so the type of a verb is a function of its lexeme,
  `Examples.Lexeme.position?`, read from the section of the paper that discusses it. *Cedere*
  'yield', from the controlled affecting processes, a subclass of the controlled processes, is a
  nonmotional process.
* The diacritics are read on the `Judgment` scale: unmarked is acceptable, `?` marginal, `??`
  questionable, `?*` and `*?` unacceptable, `*` ungrammatical.
* A sentence printed with one auxiliary selects it where it is acceptable, as the paper prints such
  sentences to show the auxiliary a verb takes; a sentence printed with both and judged alike
  selects neither. The boundary is read off the sentences that keep their type's default: a row
  records a phrase that changes the telicity of the predicate, or a subject whose agentivity
  departs from the default, where the paper points to one.
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

/-- The four languages of the paper. -/
inductive Language
  | italian | french | dutch | german
  deriving DecidableEq, Repr, Fintype

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

/-! ### The rows -/

/-- An example sentence, with its language, its verb and the verb's type, the departures from the
default of the type, and the judgment of the sentence with each auxiliary the paper prints. -/
structure Row where
  language : Language
  verb : Examples.Lexeme
  position : AuxiliarySelectionHierarchy
  predicate : Option Examples.PredicateShift
  subject : Option Examples.SubjectShift
  judgment : PerfectAuxiliary → Option Judgment

/-- The lexeme of the span of `e` labelled `l`. -/
def lexemeOf (e : Datum) (l : Examples.SpanLabel) : Option Examples.Lexeme :=
  (e.spans.find? (Examples.label? · = some l)).bind Examples.lexeme?

/-- The row of an example, from its language, the lexemes of its auxiliary and its participle, its
departures from the default of the verb's type, and its alternative with the other
auxiliary. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let language ← e.byLanguage [(.italian, Language.italian), (.french, .french),
    (.dutch, .dutch), (.german, .german)]
  let aux ← (lexemeOf e .auxiliary).bind (·.auxiliary?)
  let verb ← lexemeOf e .participle
  let position ← verb.position?
  pure
    { language, verb, position
      predicate := Examples.predicate e
      subject := Examples.subject e
      judgment := fun a ↦ if a = aux then some e.judgment else e.contrasts.head?.map (·.2) }

/-- The paper's examples. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = Examples.all.length := by decide

/-- The sentence of a row selects `a` when the paper judges it acceptable with `a` and with no
other auxiliary it prints. -/
def Row.Selects (r : Row) (a : PerfectAuxiliary) : Prop :=
  r.judgment a = some .acceptable ∧ ∀ b ≠ a, r.judgment b ≠ some .acceptable

instance (r : Row) (a : PerfectAuxiliary) : Decidable (r.Selects a) := by
  unfold Row.Selects; infer_instance

/-! ### The core -/

/-- A verb of change of location takes *be* and rejects *have* in all four languages. -/
theorem changeOfLocation_selects_be : ∀ r ∈ rows, r.position = .changeOfLocation →
    (∀ j ∈ r.judgment .be, j = .acceptable) ∧ ∀ j ∈ r.judgment .have, j = .ungrammatical := by
  decide

/-- A verb of controlled nonmotional process takes *have* in all four languages, and *be* at best
marginally. -/
theorem nonmotionalProcess_selects_have : ∀ r ∈ rows, r.position = .nonmotionalProcess →
    (∀ j ∈ r.judgment .have, j = .acceptable) ∧ ∀ j ∈ r.judgment .be, j ≤ .marginal := by
  decide

/-- Some verb of a type takes both auxiliaries acceptably exactly when the type is not at either
end of the hierarchy. -/
theorem free_alternation_iff (t : AuxiliarySelectionHierarchy) :
    (∃ r ∈ rows, r.position = t ∧ r.judgment .be = some .acceptable ∧
      r.judgment .have = some .acceptable) ↔ t ≠ ⊥ ∧ t ≠ ⊤ := by
  revert t; decide

/-! ### The boundary -/

/-- The types of the verbs whose sentences in `l` select `a`, among the sentences that depart from
the default of their type in neither predicate nor subject. -/
def Language.typesWith (l : Language) (a : PerfectAuxiliary) :
    Finset AuxiliarySelectionHierarchy :=
  (rows.filterMap fun r ↦ if r.language = l ∧ r.predicate = none ∧ r.subject = none ∧
    r.Selects a then some r.position else none).toFinset

-- §§3–4, the sentences of each language
theorem typesWith_italian_be : Language.italian.typesWith .be =
    {.changeOfLocation, .changeOfState, .continuationOfState, .existenceOfState} := by
  decide

theorem typesWith_italian_have : Language.italian.typesWith .have =
    {.existenceOfState, .uncontrolledProcess, .motionalProcess, .nonmotionalProcess} := by
  decide

theorem typesWith_french_be : Language.french.typesWith .be =
    {.changeOfLocation, .changeOfState, .continuationOfState} := by
  decide

theorem typesWith_french_have : Language.french.typesWith .have =
    {.changeOfState, .continuationOfState, .existenceOfState, .motionalProcess,
      .nonmotionalProcess} := by
  decide

theorem typesWith_dutch_be : Language.dutch.typesWith .be =
    {.changeOfLocation, .changeOfState, .continuationOfState, .existenceOfState} := by
  decide

theorem typesWith_dutch_have : Language.dutch.typesWith .have =
    {.continuationOfState, .existenceOfState, .motionalProcess, .nonmotionalProcess} := by
  decide

theorem typesWith_german_be : Language.german.typesWith .be =
    {.changeOfLocation, .changeOfState, .continuationOfState, .existenceOfState,
      .motionalProcess} := by
  decide

theorem typesWith_german_have : Language.german.typesWith .have =
    {.continuationOfState, .existenceOfState, .motionalProcess, .nonmotionalProcess} := by
  decide

/-- Along the types a language attests, its *be* types form a lower set and its *have* types an
upper set. -/
theorem typesWith_ordered (l : Language) :
    AntitoneOn (· ∈ l.typesWith .be) ↑(l.typesWith .be ∪ l.typesWith .have) ∧
      MonotoneOn (· ∈ l.typesWith .have) ↑(l.typesWith .be ∪ l.typesWith .have) := by
  simp only [AntitoneOn, MonotoneOn, Finset.mem_coe, le_Prop_eq]
  cases l <;>
    simp only [typesWith_italian_be, typesWith_italian_have, typesWith_french_be,
      typesWith_french_have, typesWith_dutch_be, typesWith_dutch_have, typesWith_german_be,
      typesWith_german_have] <;>
    exact ⟨by decide, by decide⟩

/-- A language whose *have* types form an upper set of its attested types, and whose verbs of
change of location admit *have*, takes *have* in every type in which it takes *be*. -/
theorem subset_of_changeOfLocation_mem {B H : Set AuxiliarySelectionHierarchy}
    (h : MonotoneOn (· ∈ H) (B ∪ H)) (hH : .changeOfLocation ∈ H) : B ⊆ H :=
  fun _ hb ↦ h (.inr hH) (.inl hb) bot_le hH

-- §6, at the other end of the hierarchy
theorem subset_of_nonmotionalProcess_mem {B H : Set AuxiliarySelectionHierarchy}
    (h : AntitoneOn (· ∈ B) (B ∪ H)) (hB : .nonmotionalProcess ∈ B) : H ⊆ B :=
  fun _ hh ↦ h (.inr hh) (.inl hB) le_top hB

-- §3.4, (20) against (21)
theorem italian_varies :
    Language.italian.typesWith .be ∩ Language.italian.typesWith .have = {.existenceOfState} := by
  rw [typesWith_italian_be, typesWith_italian_have]; decide

-- §3.2, (12) against (13); §3.3, (19a) against (16)
theorem french_varies : Language.french.typesWith .be ∩ Language.french.typesWith .have =
    {.changeOfState, .continuationOfState} := by
  rw [typesWith_french_be, typesWith_french_have]; decide

-- (18), (19b) and (24)
theorem dutch_varies : Language.dutch.typesWith .be ∩ Language.dutch.typesWith .have =
    {.continuationOfState, .existenceOfState} := by
  rw [typesWith_dutch_be, typesWith_dutch_have]; decide

-- (17), (19c); (23), (25a); (38) against (40a)
theorem german_varies : Language.german.typesWith .be ∩ Language.german.typesWith .have =
    {.continuationOfState, .existenceOfState, .motionalProcess} := by
  rw [typesWith_german_be, typesWith_german_have]; decide

-- §6: "the cutoff point cannot be identical in all languages"
theorem italian_french_disjoint :
    Disjoint (Language.italian.typesWith .be ∩ Language.italian.typesWith .have)
      (Language.french.typesWith .be ∩ Language.french.typesWith .have) := by
  rw [italian_varies, french_varies]; decide

-- §6
theorem italian_cutoff :
    upperBounds ↑(Language.italian.typesWith .be) ∩
      lowerBounds ↑(Language.italian.typesWith .have) =
        {AuxiliarySelectionHierarchy.existenceOfState} := by
  rw [Finset.isLUB_sup_id.upperBounds_eq, Finset.isGLB_inf_id.lowerBounds_eq, Set.Ici_inter_Iic,
    typesWith_italian_be, typesWith_italian_have]
  exact Set.Icc_self _

/-! ### Directional phrases -/

-- §4.3, (39), (40) against (42b)
theorem directional_motionalProcess : ∀ r ∈ rows, r.position = .motionalProcess →
    r.predicate = some .telicized →
    (r.language = .dutch ∨ r.language = .german → r.Selects .be) ∧
      (r.language = .french → r.Selects .have) := by
  decide

-- §4.3, (41b) against (41d): *correre* 'run' moves to *essere*, *nuotare* 'swim' does not
theorem italian_directional_split :
    (∃ r ∈ rows, r.verb = .correre ∧ r.predicate = some .telicized ∧ r.Selects .be) ∧
      ∃ r ∈ rows, r.verb = .nuotare ∧ r.predicate = some .telicized ∧ r.Selects .have := by
  decide

/-! ### The fragments -/

/-- The entry of a verb in its language's fragment, where the fragment has one. -/
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

-- each entry is written as the row names the participle's lexeme
theorem entry?_form : ∀ e ∈ Examples.all, ∀ s ∈ e.spans, ∀ l ∈ Examples.lexeme? s,
    ∀ v ∈ l.entry?, s.lexeme = some v.form := by
  decide +kernel

-- each entry's basic frame, the first, has no complement
theorem entry?_intransitive : ∀ l : Examples.Lexeme, ∀ v ∈ l.entry?,
    (v.valency.frames.headD .intransitive).IsIntransitive := by
  decide

-- (21a), the attested *avere* with *bastare*, is the one sentence that selects an auxiliary its
-- grammar does not give its verb
theorem selects_not_mem_perfectAuxiliaries :
    (rows.filter fun r ↦ ∃ v ∈ r.verb.entry?, ∃ a, r.Selects a ∧
      v.perfectAuxiliaries.Nonempty ∧ a ∉ v.perfectAuxiliaries).map (·.verb) = [.bastare] := by
  decide +kernel

end Sorace2000
