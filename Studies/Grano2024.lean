module

public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Mood.Defs
public import Linglib.Semantics.Events.Closure
public import Linglib.Data.Examples.Grano2024
public import Linglib.Fragments.Greek.StandardModern.Verbs
public import Linglib.Fragments.Romance.Portuguese.Verbs
public import Linglib.Fragments.Romance.Italian.Verbs
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Fragments.Romanian.Verbs

/-!
# Grano (2024): Intention Reports and Eventuality Abstraction in a Theory of Mood Choice

This file formalizes [grano-2024]'s account of why 'intend' accepts nonfinite and subjunctive
complements but rejects indicative ones across Spanish, French, Portuguese, Italian, Greek,
Romanian, and English, as 'want' does and as 'hope' does not (Table 1). Three premises carry the
argument: intention reports have causally self-referential content ([searle-1983], [harman-1976]),
an intention being carried out only if it causes the outcome in the right way; encoding that content
takes abstraction over the complement's eventuality argument, since causation relates eventualities
(`Event.causedClosure_factorsThrough_iff`); and subjunctive and nonfinite clauses can leave that
argument open where the indicative closes it (`MoodHead`). The pool of the paper's judged
complements records each predicate's class, the complement type, and where it matters the reading,
and `abstraction_rejects_indicative` checks the conclusion over every row that requires abstraction:
intention reports, causatives, the intention-rigid *aim* and *try*, aspectual predicates, the
intention readings of *persuade*, *decide*, *promise*, and *plan*, and the event readings of memory
and perception reports. Section 3's case against [portner-rubinstein-2020] and
[giannakidou-mari-2021] is `intend_like_hope_in_logic`: on realism, consistency, and monotonicity
'intend' patterns with 'hope', whose indicative those theories license by that very profile, yet
every indicative row under 'intend' is rejected. The Hintikka semantics of (73) is the modal box
over intention alternatives, and the three properties follow from their overlap with the doxastic
alternatives (`realism` and its siblings); the verb entries of the language fragments record the
finite moods the pool accepts (`fragments_match_pool`); and section 7's synthesis reads the
availability of the indicative off the two departures from default clausal semantics, a pair of
modal backgrounds and eventuality abstraction (`indicative_possible_iff`).

## Implementation notes

The mood heads are those of section 5, (87) to (89): the subjunctive is ambiguous between a head
that closes the eventuality argument as the indicative does and one that passes it up, so an open
argument implies subjunctive or nonfinite form and not conversely. A head's clause denotes in a
sum type, a proposition or a predicate of eventualities, the type mismatch under 'intend' being
the absence of the second. Nonfinite complements carry the subjunctive's two heads, as the paper
says without illustrating. `sbjvCausal` is the alternative of section 7, (134), which moves the
quantification of 'intend' into the mood head.
Whether a class needs eventuality abstraction is the paper's premise per class; for the hybrid,
commissive, *plan*, memory, and perception predicates the reading of the row decides. The
simplification condition of [portner-rubinstein-2020] is read off the consistency rows: a pair of
backgrounds may collapse when the class rejects inconsistent prejacents. French *faire* with
indicative complements, (43a) and (44b), which the paper leaves as open exceptions, is not in the
pool, and the paper's remarks on nominal *avoir l'intention* and on French and Italian rejecting
non-control complements under 'intend' altogether are recorded as rows without a theorem.

## References

* [grano-2024]
* [portner-rubinstein-2020]
* [giannakidou-mari-2021]
* [searle-1983]
* [harman-1976]
* [heim-1992]
* [higginbotham-1983]
-/

@[expose] public section

namespace Grano2024

open Mood Event
open scoped SetRel

/-! ### The pool -/

/-- The predicate classes of the pool. -/
inductive Class where
  | want
  | hope
  | intend
  | causative
  /-- *aim*, *try*, *endeavor*, *strive*, *seek*, section 6.1. -/
  | intentionRigid
  /-- *persuade*, *convince*, *decide*: intention with a nonfinite or subjunctive complement,
  belief with an indicative one. -/
  | hybrid
  /-- *promise*, *agree*, *pledge*, *swear*: a commissive or an assertion by the same split. -/
  | commissive
  | plan
  | aspectual
  | memory
  | perception
  deriving DecidableEq, Repr, Fintype

/-- The complement types of the pool. -/
inductive Complement where
  | indicative
  | subjunctive
  | infinitive
  | forTo
  | gerund
  | bareInfinitive
  deriving DecidableEq, Repr, Fintype

/-! ### Section 5: mood heads and the eventuality argument -/

/-- The mood heads of section 5. The indicative and the first subjunctive close the eventuality
argument of their clause and the second subjunctive passes it up; mood in nonfinite clauses
patterns with the subjunctive. -/
inductive MoodHead where
  | indic
  | sbjv₁
  | sbjv₂
  deriving DecidableEq, Repr

/-- The morphological mood a head is spelled out as. -/
def MoodHead.mood : MoodHead → Grammatical
  | .indic => .indicative
  | .sbjv₁ | .sbjv₂ => .subjunctive

/-- The head passes the eventuality argument up. -/
def MoodHead.Opens (m : MoodHead) : Prop := m = .sbjv₂

instance : DecidablePred MoodHead.Opens := fun m ↦ inferInstanceAs (Decidable (m = _))

/-- The denotation of a mood head applied to its clause: a proposition once the eventuality
argument is closed, the clause's own predicate of eventualities otherwise. The indicative and the
first subjunctive denote alike, which is why section 7 adds a second departure from the default
to keep the subjunctive out of indicative environments. -/
def MoodHead.denote {W Ev : Type*} (m : MoodHead) (P : W → Ev → Prop) :
    (W → Prop) ⊕ (W → Ev → Prop) :=
  if m.Opens then .inr P else .inl (closure P)

theorem MoodHead.isRight_denote {W Ev : Type*} {m : MoodHead} {P : W → Ev → Prop} :
    (m.denote P).isRight ↔ m.Opens := by
  unfold MoodHead.denote; split <;> simp [*]

-- (87a), (88a)
theorem MoodHead.denote_indic_eq_sbjv₁ {W Ev : Type*} (P : W → Ev → Prop) :
    MoodHead.indic.denote P = MoodHead.sbjv₁.denote P := rfl

theorem MoodHead.mood_of_opens {m : MoodHead} (h : m.Opens) : m.mood = .subjunctive := by
  rw [h]; rfl

theorem MoodHead.not_opens_sbjv₁ : ¬ MoodHead.sbjv₁.Opens := by decide

/-- The mood heads a complement type may carry. -/
def Complement.heads : Complement → List MoodHead
  | .indicative => [.indic]
  | _ => [.sbjv₁, .sbjv₂]

/-- Premise 3 for complement types: some head of the complement leaves its eventuality argument
open. -/
def Complement.Abstracts (c : Complement) : Prop := ∃ m ∈ c.heads, m.Opens

instance (c : Complement) : Decidable c.Abstracts := by unfold Complement.Abstracts; infer_instance

theorem Complement.abstracts_iff {c : Complement} : c.Abstracts ↔ c ≠ .indicative := by
  cases c <;> decide

/-- The reading a row is judged on, where the predicate has more than one. -/
inductive Reading where
  | intention
  | belief
  | assertion
  /-- *plan* as 'regard as fixed for planning purposes', section 6.1. -/
  | foresee
  | event
  | proposition
  deriving DecidableEq, Repr

/-- The logical diagnostics of section 3: an impossible prejacent, two incompatible prejacents,
and a prejacent with a rejected superset. -/
inductive Diagnostic where
  | realism
  | consistency
  | monotonicity
  deriving DecidableEq, Repr, Fintype

/-- A judged complement clause. -/
structure Row where
  language : Glottocode
  cls : Class
  complement : Complement
  reading : Option Reading
  diagnostic : Option Diagnostic
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let cls ← ex.parse? "class"
    [("want", Class.want), ("hope", .hope), ("intend", .intend), ("causative", .causative),
      ("intentionRigid", .intentionRigid), ("hybrid", .hybrid), ("commissive", .commissive),
      ("plan", .plan), ("aspectual", .aspectual), ("memory", .memory), ("perception", .perception)]
  let complement ← ex.parse? "complement"
    [("indicative", Complement.indicative), ("subjunctive", .subjunctive),
      ("infinitive", .infinitive), ("forTo", .forTo), ("gerund", .gerund),
      ("bareInfinitive", .bareInfinitive)]
  pure ⟨ex.language, cls, complement,
    ex.parse? "reading"
      [("intention", Reading.intention), ("belief", .belief), ("assertion", .assertion),
        ("foresee", .foresee), ("event", .event), ("proposition", .proposition)],
    ex.parse? "diagnostic"
      [("realism", Diagnostic.realism), ("consistency", .consistency),
        ("monotonicity", .monotonicity)],
    ex.judgment⟩

/-- The paper's judged complements, sections 2, 3, 6, and 7. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_length : rows.length = Examples.all.length := by decide +kernel

/-! ### Premises 1 and 2 and the conclusion, over the pool -/

/-- The classes whose semantics relates to an eventuality: intention through the causal
self-reference of Premises 1 and 2, causation, the intention-rigid predicates, and aspect. -/
def Class.RequiresAbstraction (c : Class) : Prop :=
  c = .intend ∨ c = .causative ∨ c = .intentionRigid ∨ c = .aspectual

instance : DecidablePred Class.RequiresAbstraction := fun c ↦ by
  unfold Class.RequiresAbstraction; infer_instance

/-- A row requires eventuality abstraction by its class or by an intention or event reading. -/
def Row.RequiresAbstraction (r : Row) : Prop :=
  r.cls.RequiresAbstraction ∨ r.reading = some .intention ∨ r.reading = some .event

instance : DecidablePred Row.RequiresAbstraction := fun r ↦ by
  unfold Row.RequiresAbstraction; infer_instance

/-- Wherever abstraction is required, the indicative is rejected (72d). -/
theorem abstraction_rejects_indicative :
    ∀ r ∈ rows, r.RequiresAbstraction → r.complement = .indicative →
      r.judgment ≠ .acceptable := by
  decide +kernel

theorem abstraction_accepts_open :
    ∀ c : Class, c.RequiresAbstraction →
      ∃ r ∈ rows, r.cls = c ∧ r.complement.Abstracts ∧ r.judgment = .acceptable := by
  decide +kernel

-- (128)
theorem want_rejects_indicative :
    ∀ r ∈ rows, r.cls = .want → r.complement = .indicative → r.judgment ≠ .acceptable := by
  decide +kernel

theorem hope_varies :
    (∃ r ∈ rows, r.cls = .hope ∧ r.complement = .indicative ∧ r.judgment = .acceptable) ∧
      ∃ r ∈ rows, r.cls = .hope ∧ r.complement = .indicative ∧ r.judgment = .ungrammatical := by
  decide

/-! ### Table 1 and the fragment entries -/

/-- The finite moods among the complement types, as codings of a clausal argument position. -/
def Complement.coding? : Complement → Option Clause.ComplementType
  | .indicative => some .indicative
  | .subjunctive => some .subjunctive
  | _ => none

/-- The fragment verb for a language and a class of Table 1. -/
def verbOf : Glottocode → Class → Option Verb
  | "stan1288", .want => some Spanish.Verbs.querer
  | "stan1288", .hope => some Spanish.Verbs.esperar
  | "stan1288", .causative => some Spanish.Verbs.hacer
  | "port1283", .want => some Portuguese.Verbs.querer
  | "port1283", .hope => some Portuguese.Verbs.esperar
  | "port1283", .intend => some Portuguese.Verbs.pretender
  | "port1283", .causative => some Portuguese.Verbs.fazer
  | "ital1282", .want => some Italian.Verbs.volere.toVerb
  | "ital1282", .hope => some Italian.Verbs.sperare.toVerb
  | "ital1282", .intend => some Italian.Verbs.intendere.toVerb
  | "ital1282", .causative => some Italian.Verbs.fare.toVerb
  | "mode1248", .want => some Greek.StandardModern.Verbs.thelo
  | "mode1248", .hope => some Greek.StandardModern.Verbs.elpizo
  | "mode1248", .intend => some Greek.StandardModern.Verbs.protitheme
  | "mode1248", .causative => some Greek.StandardModern.Verbs.vazo
  | "roma1327", .want => some Romanian.Verbs.a_vrea
  | "roma1327", .hope => some Romanian.Verbs.a_spera
  | "roma1327", .intend => some Romanian.Verbs.a_intentiona
  | "roma1327", .causative => some Romanian.Verbs.a_face
  | _, _ => none

/-- The cells of Table 1 with a verb entry, and the causatives of section 2.2. Spanish 'intend' is
the nominal *tener la intención*, and the French and English entries do not record finite mood. -/
def cells : List (Glottocode × Class) :=
  (["port1283", "ital1282", "mode1248", "roma1327"].flatMap fun l ↦
    [(l, .want), (l, .hope), (l, .intend), (l, .causative)]) ++
  [("stan1288", .want), ("stan1288", .hope), ("stan1288", .causative)]

theorem verbOf_isSome : ∀ c ∈ cells, (verbOf c.1 c.2).isSome := by decide

theorem fragments_match_pool :
    ∀ c ∈ cells, ∀ v ∈ verbOf c.1 c.2, ∀ m : Complement, ∀ k ∈ m.coding?,
      (k ∈ v.codings ↔ ∃ r ∈ rows, r.language = c.1 ∧ r.cls = c.2 ∧ r.complement = m ∧
        r.diagnostic = none ∧ r.reading = none ∧ r.judgment = .acceptable) := by
  decide +kernel

theorem esperar_varies :
    .indicative ∈ Portuguese.Verbs.esperar.codings ∧
      .indicative ∉ Spanish.Verbs.esperar.codings := by
  decide

/-! ### Section 3: the logical profile of 'intend' -/

/-- The class fails diagnostic `d` somewhere in the pool. -/
def Class.Fails (c : Class) (d : Diagnostic) : Prop :=
  ∃ r ∈ rows, r.cls = c ∧ r.diagnostic = some d ∧ r.judgment ≠ .acceptable

instance (c : Class) (d : Diagnostic) : Decidable (c.Fails d) := by
  unfold Class.Fails; infer_instance

theorem intend_like_hope_in_logic :
    (∀ d, Class.hope.Fails d ∧ Class.intend.Fails d ∧ ¬ Class.want.Fails d) ∧
      (∃ r ∈ rows, r.cls = .hope ∧ r.complement = .indicative ∧ r.judgment = .acceptable) ∧
      ∀ r ∈ rows, r.cls = .intend → r.complement = .indicative → r.judgment ≠ .acceptable := by
  decide +kernel

/-! ### The semantics of intention reports, section 4

(73) is necessity over the worlds compatible with the agent's intentions, `□[int]`. Its one
substantive constraint is that those worlds overlap the worlds compatible with the agent's
beliefs, `◇[int] (w ~[dox] ·) w`, from which realism, consistency, and monotonicity follow.
(78) moves to the de se triples of an intention state, and (79) adds the causal
self-reference, closing the complement's eventuality argument over what the state causes. -/

section Hintikka

open ModalLogic SetRel

variable {W : Type*} {int dox : SetRel W W} {p q : W → Prop} {w : W}

theorem realism (h : ◇[int] (w ~[dox] ·) w) (hp : □[int] p w) : ◇[dox] p w :=
  diamond_of_box h hp

theorem consistency (h : ◇[int] (w ~[dox] ·) w) (hp : □[int] p w) (hq : □[int] q w) :
    ◇[dox] (fun v ↦ p v ∧ q v) w :=
  realism h ((box_and int q).2 ⟨hp, hq⟩)

theorem monotonicity (hpq : p ≤ q) (hp : □[int] p w) : □[int] q w :=
  box_mono int hpq w hp

end Hintikka

/-- The ingredients of (78) and (79): intention states, their holders, their content as world,
time, and individual triples, and causation in the right way between eventualities. -/
structure IntentionFrame (E W T Ev : Type*) where
  intention : Ev → W → Prop
  holder : E → Ev → W → Prop
  content : Ev → Set (W × T × E)
  causeStar : W → SetRel Ev Ev

namespace IntentionFrame

variable {E W T Ev : Type*} [LT T] (F : IntentionFrame E W T Ev)

/-- (78): `x` intends `Q` at `w` when some intention state of `x` has, at every triple of its
content, a later time at which `Q` holds. The complement is a property of individuals, times, and
worlds, which an indicative clause can supply. -/
def Report₃ (x : E) (Q : E → T → W → Prop) (w : W) : Prop :=
  ∃ s, F.intention s w ∧ F.holder x s w ∧ ∀ c ∈ F.content s, ∃ t > c.2.1, Q c.2.2 t c.1

/-- (79): as (78), but at every triple of its content the state causes in the right way an
eventuality of the complement at a later time. The complement keeps its eventuality argument,
closed here over what the state causes. -/
def Report (x : E) (P : E → T → W → Ev → Prop) (w : W) : Prop :=
  ∃ s, F.intention s w ∧ F.holder x s w ∧
    ∀ c ∈ F.content s, causedClosure F.causeStar s (fun w' e ↦ ∃ t > c.2.1, P c.2.2 t w' e) c.1

variable {F} {x : E} {P : E → T → W → Ev → Prop} {w : W}

theorem Report.mono {Q : E → T → W → Ev → Prop} (hPQ : ∀ y t w e, P y t w e → Q y t w e)
    (h : F.Report x P w) : F.Report x Q w :=
  let ⟨s, hs, hx, hc⟩ := h
  ⟨s, hs, hx, fun c hcs ↦
    causedClosure_mono (fun _ _ ⟨t, ht, hP⟩ ↦ ⟨t, ht, hPQ _ _ _ _ hP⟩) (hc c hcs)⟩

theorem Report.report₃ (h : F.Report x P w) : F.Report₃ x (fun y t ↦ closure (P y t)) w :=
  let ⟨s, hs, hx, hc⟩ := h
  ⟨s, hs, hx, fun c hcs ↦ let ⟨e, _, t, ht, hP⟩ := hc c hcs; ⟨t, ht, e, hP⟩⟩

-- (79), (78)
theorem report_iff_report₃ (h : ∀ s e w, s ~[F.causeStar w] e) :
    F.Report x P w ↔ F.Report₃ x (fun y t ↦ closure (P y t)) w :=
  ⟨Report.report₃, fun ⟨s, hs, hx, hc⟩ ↦
    ⟨s, hs, hx, fun c hcs ↦ let ⟨t, ht, e, hP⟩ := hc c hcs; ⟨e, h s e c.1, t, ht, hP⟩⟩⟩

end IntentionFrame

/-- The subjunctive of (134), for a theory that moves the modal quantification from 'intend' into
the mood head: simple necessity over the content worlds of the attitude state, with the causally
self-referential prejacent. -/
def sbjvCausal {W Ev : Type*} (content : Ev → W → Prop) (causeStar : W → SetRel Ev Ev)
    (P : W → Ev → Prop) (s : Ev) : Prop :=
  ∀ w, content s w → causedClosure causeStar s P w

/-! ### Section 7: the two departures from default clausal semantics -/

/-- A class whose reports carry two modal backgrounds, the doxastic-like and the bouletic
([portner-rubinstein-2020]); 'intend' is taken to carry one, the paper's footnote 50. -/
def Class.TwoBackgrounds (c : Class) : Prop := c = .want ∨ c = .hope

instance : DecidablePred Class.TwoBackgrounds := fun c ↦ by
  unfold Class.TwoBackgrounds; infer_instance

/-- [portner-rubinstein-2020]'s simplification read off the pool: the pair may collapse to one
background when the class requires its backgrounds to be consistent, that is, rejects
inconsistent prejacents. -/
def Class.Simplifiable (c : Class) : Prop := c.Fails .consistency

instance : DecidablePred Class.Simplifiable := fun c ↦ by unfold Class.Simplifiable; infer_instance

/-- The indicative is available when neither departure is in force: no eventuality abstraction,
and a single background or a pair that may simplify. -/
def Class.IndicativePossible (c : Class) : Prop :=
  ¬ c.RequiresAbstraction ∧ (¬ c.TwoBackgrounds ∨ c.Simplifiable)

instance : DecidablePred Class.IndicativePossible := fun c ↦ by
  unfold Class.IndicativePossible; infer_instance

theorem indicative_possible_iff :
    ∀ c ∈ [Class.want, .hope, .intend, .causative],
      (c.IndicativePossible ↔
        ∃ r ∈ rows, r.cls = c ∧ r.complement = .indicative ∧ r.judgment = .acceptable) := by
  decide +kernel

end Grano2024
