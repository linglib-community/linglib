module

public import Linglib.Discourse.Gameboard.Basic
public import Linglib.Data.Examples.Ginzburg2012

/-!
# Ginzburg (2012): The Interactive Stance

This file formalizes the conversational rules of [ginzburg-2012] over the dialogue gameboard
`Gameboard`: each participant's turn holder and addressee, the commonly accepted FACTS, the MOVES
made, the questions under discussion and, once metacommunication enters, the ungrounded utterances
PENDING. A rule is a partial map from gameboards meeting its preconditions to updated gameboards
(`Rule.apply`: the inventory of Appendix B, with the utterance, question or turn a nondeterministic
rule chooses made an argument), a conversation composes rules (`run`), and an utterance is coherent
when some rule makes it the latest move (`Coherent`). Asking a question keeps `non-resolve-cond`
exactly when no fact resolves it, the Question Introduction Appropriateness Condition, and FACTS
update restores the condition (`askQud_nonResolveCond_iff`, `factUpdate_nonResolveCond`); a genre
makes an initiating move a relevant Free Speech move (`IsInitiating`, `coherent_of_isInitiating`);
each clarification rule is a question and a turn merged with Utterance Interpolation
(`Gameboard.clarify`), so it makes the clarified constituent of the maximal pending utterance the
focus-establishing constituent of MaxQUD (`focusEstablishing_clarify`); and self-repair is
Parameter Identification with the turn held (`parameterIdentification_eq_repair_swapTurn`).

The worked traces of Ch. 4 reach the tabulated gameboards (`Ex66.trace`, `Ex66.trace68_table`,
`Ex79.trace`), and after "Is George here? / Is WHO here?" the two participants' gameboards differ
in QUD and PENDING although both processed the same utterances (`George.differ`). The turn each
rule leaves is a general property of the inventory: the clarification rules pass it to the
clarifier, repair keeps it, and QSPEC leaves it open (`speaker_parameterIdentification`,
`speaker_repair`, `speaker_qspec`); the rows of Chs. 1 and 8 record who holds the turn after a
clarification request, a self-repair and a bare follow-up question, as the rules predict
(`rows_turn`).

## Implementation notes

* The schematic content types of the traces (`Content`, `Clarifiable`) fix exactly the aboutness,
  influence and resolution relations each trace's side conditions require. Utterances are
  written orthographically, and the categories and contextual parameters are those the examples
  need (`grammar`).
* Contextual Instantiation takes the labels of the parameters it witnesses rather than the
  witnessing record, so the utterance it produces is a contextual extension of MaxPending by
  `LocutionaryProposition.exists_eq_instantiate_iff`.
* Three of the book's tables misprint: trace (66) labels the QUD update after B's question "Assert
  QUD-incrementation" where it is Ask QUD-incrementation; trace (68) ends with `QUD := ⟨q0⟩`
  although no `q0` occurs, and Fact update/QUD-downdate leaves QUD empty; Table 7.4 heads the
  Answers block with 413 while its cells sum to 403, the figure the total of Table 7.3 needs.
* Appendix B's backwards-looking appropriateness repair ((29) p. 375) makes the pending utterance
  the focus-establishing constituent, where its statement in the text ((31) p. 287) and every
  other clarification rule make it the clarified constituent; the rule follows (31).
* Utterance Interpolation ((67) p. 190) also adds the most recent speech event to FACTS; the
  rules here leave FACTS as it is.
* Co-propositionality is approximated by identity (`Copropositional`): a move addresses MaxQUD
  when it contributes MaxQUD's own question. A correction, which asserts an answer, contributes
  its polar question instead and is not covered.
* Ask and Assert QUD-incrementation push their question with no focus-establishing constituent,
  as in Ch. 4; the Ch. 7 version that pairs a wh-question with its wh-phrase (p. 241) is not
  modelled.
* The clarification-request forms of §6.2.1 and the non-sentential-utterance classes of Tables
  7.3–7.4 are recorded as taxonomies (`CRForm`, `NSUClass`, `NSUClass.function`).

## References

* [ginzburg-2012]
-/

@[expose] public section

namespace Ginzburg2012

open Discourse
open Discourse.Gameboard (Turn)

/-- The syntactic categories of the examples' utterances and sub-utterances. -/
inductive Category
  | s
  | np
  deriving DecidableEq, Repr

/-- The contextual parameters of the examples are the referents of "George" and "Bo". -/
inductive Parameter
  | george
  | bo
  deriving DecidableEq, Repr

/-- The grammatical domain of the examples has orthographic forms, their categories, and the
parameters, which are also the denotations of the names contributing them. -/
abbrev grammar : GrammaticalDomain :=
  { Form := String, Category := Category, Label := Parameter, Denotation := Parameter }

/-- An illocutionary act is the illocutionary relation of an illocutionary proposition applied
to its content ((8c) p. 361), without the speaker and addressee that the proposition also
records. The inventory is that of the rules of Ch. 4 less parting and counter-parting. -/
inductive IllocutionaryAct (Fact Question : Type*) where
  /-- Asserting a fact. -/
  | assert : Fact → IllocutionaryAct Fact Question
  /-- Asking a question. -/
  | ask : Question → IllocutionaryAct Fact Question
  /-- Accepting an assertion. -/
  | accept : Fact → IllocutionaryAct Fact Question
  /-- Asking for confirmation of an assertion. -/
  | check : Fact → IllocutionaryAct Fact Question
  /-- Confirming in response to a check. -/
  | confirm : Fact → IllocutionaryAct Fact Question
  /-- Greeting. -/
  | greet : IllocutionaryAct Fact Question
  /-- Counter-greeting. -/
  | counterGreet : IllocutionaryAct Fact Question
  deriving Repr, DecidableEq

/-- What a gameboard's content types supply: the polar question `p?`, the
aboutness and influence relations of q-specificity, and resolution, with `p`
resolving `p?`. -/
class Content (Fact Q : Type) where
  polar : Fact → Q
  About : Fact → Q → Prop
  Influences : Q → Q → Prop
  Resolves : Fact → Q → Prop
  decAbout : DecidableRel About
  decInfluences : DecidableRel Influences
  decResolves : DecidableRel Resolves
  resolves_polar (p : Fact) : Resolves p (polar p)

attribute [reducible, instance] Content.decAbout Content.decInfluences Content.decResolves

/-- The questions clarification accommodates: `λx.Mean(A, u, x)`, what `A`
meant by the sub-utterance `u` (Parameter Identification), and `λx.v(u ↦ x)`,
the content `v` with `u`'s contextual parameter abstracted (Parameter
Focussing). -/
class Clarifiable (P Fact Q : Type) where
  mean : P → SubUtterance grammar → Q
  focus : IllocutionaryAct Fact Q → SubUtterance grammar → Q

/-- The domain of a gameboard whose utterances carry illocutionary content. -/
abbrev domain (P Fact Q : Type) [DecidableEq P] [DecidableEq Fact] [DecidableEq Q] :
    Gameboard.Domain :=
  { toGrammaticalDomain := grammar, Participant := P, Fact := Fact, Question := Q
    Content := IllocutionaryAct Fact Q }

/-- A gameboard whose utterances, in MOVES and PENDING, carry illocutionary content. -/
abbrev Board (P Fact Q : Type) [DecidableEq P] [DecidableEq Fact] [DecidableEq Q] :=
  Gameboard (domain P Fact Q)

/-- An utterance with illocutionary content. -/
abbrev Utterance (Fact Q : Type) := LocutionaryProposition grammar (IllocutionaryAct Fact Q)

/-- The two participants of a duologue. -/
inductive Agent
  | A
  | B
  deriving DecidableEq, Repr

section Rules

variable {P Fact Q : Type} [DecidableEq P] [DecidableEq Fact] [DecidableEq Q] [Content Fact Q]

/-- The utterance of a bare move, a clause with no recorded form, when only its content matters
(Ch. 4). -/
def ofMove (m : IllocutionaryAct Fact Q) : Utterance Fact Q :=
  { form := "", category := .s, content := m }

/-- The question a move contributes to QUD: `q` for `Ask(q)`, `p?` for `Assert(p)`. -/
def qudContrib : IllocutionaryAct Fact Q → Option Q
  | .ask q => some q
  | .assert p => some (Content.polar p)
  | _ => none

/-- `r` is specific to `q`: About `q` for an assertion, Influencing `q` for a
question. -/
def QSpecific : IllocutionaryAct Fact Q → Q → Prop
  | .assert p, q => Content.About p q
  | .ask q', q => Content.Influences (Fact := Fact) q' q
  | _, _ => False

instance (m : IllocutionaryAct Fact Q) (q : Q) : Decidable (QSpecific m q) := by
  unfold QSpecific; split <;> infer_instance

/-- Co-propositionality of a move's content with a question ((67) p. 190), approximated by
identity: the move contributes that question itself to QUD. -/
def Copropositional (m : IllocutionaryAct Fact Q) (q : Q) : Prop :=
  qudContrib m = some q

instance : DecidableRel (Copropositional (Fact := Fact) (Q := Q)) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

/-- A clarification rule pairing its question with the clarified constituent makes that
constituent, a constituent of MaxPending, the focus-establishing constituent of MaxQUD. -/
theorem focusEstablishing_clarify {t : Turn} {q : Utterance Fact Q → SubUtterance grammar → Q}
    {u : SubUtterance grammar} {cr : Utterance Fact Q} {d d' : Board P Fact Q}
    (h : d.clarify Copropositional t (fun v u ↦ ⟨q v u, {u}⟩) u cr = some d') :
    (∃ v ∈ d.maxPending, u ∈ v.constituents) ∧
      d'.qud.head?.map (·.focusEstablishing) = some {u} := by
  obtain ⟨v, hv, hu, h⟩ := d.qud_clarify h
  exact ⟨⟨v, hv, hu⟩, by simp [h]⟩

/-- The conversational rules of [ginzburg-2012] (Appendix B), with the utterance,
question or turn a nondeterministic rule chooses made an argument. Ch. 4:
greeting and counter-greeting, Free Speech, QSPEC, Ask and Assert
QUD-incrementation, Assertion checking, Accept and Confirm, Fact update/QUD-
downdate, QCoord. Ch. 6: Pending Update, Contextual Instantiation,
pendification of a move-update rule (the move originates in PENDING), the
two CCURs — Parameter Identification and Parameter Focussing, each merged with
Utterance Interpolation — and CR Accommodation. §8.2: Backwards-looking
appropriateness repair. -/
inductive Rule (P Fact Q : Type)
  | greeting
  | counterGreeting
  | freeSpeech (u : Utterance Fact Q) (t : Turn)
  | qspec (u : Utterance Fact Q) (t : Turn)
  | askQud
  | assertQud
  | check (u : Utterance Fact Q) (t : Turn)
  | accept (u : Utterance Fact Q)
  | confirm (u : Utterance Fact Q)
  | factUpdate
  | qcoord (u : Utterance Fact Q)
  | pendingUpdate (u : Utterance Fact Q) (speaker addressee : P)
  | contextualInstantiation (s : Finset Parameter)
  | pendified (r : Rule P Fact Q)
  | parameterIdentification (u : SubUtterance grammar) (cr : Utterance Fact Q)
  | parameterFocussing (u : SubUtterance grammar) (cr : Utterance Fact Q)
  | crAccommodation (u : SubUtterance grammar)
  | repair (u : SubUtterance grammar) (cr : Utterance Fact Q)

variable [Clarifiable P Fact Q]

/-- A rule as a partial map: `none` when the gameboard fails its preconditions.
Accept, Confirm and the CCURs change the turn; Free Speech, QSPEC and
checking leave it underspecified; the rest keep it. Contextual Instantiation
witnesses the parameters `s` of MaxPending, as an agent does who believes their witnesses are
the ones the speaker intended; CR Accommodation integrates the other party's clarification
request, so the clarified speaker is the current addressee. -/
def Rule.apply : Rule P Fact Q → Board P Fact Q → Option (Board P Fact Q)
  | .greeting, d => match d.moves, d.qud with
    | [], [] => some (d.recordMove (ofMove IllocutionaryAct.greet))
    | _, _ => none
  | .counterGreeting, d => match d.latestContent with
    | some .greet => some (d.swapTurn.recordMove (ofMove IllocutionaryAct.counterGreet))
    | _ => none
  | .freeSpeech u t, d => match d.qud with
    | [] => some ((t.act d).recordMove u)
    | _ => none
  | .qspec u t, d => match d.qud with
    | i :: _ => if QSpecific u.content i.question then some ((t.act d).recordMove u) else none
    | [] => none
  | .askQud, d => match d.latestContent with
    | some (.ask q) => some (d.pushQud ⟨q, ∅⟩)
    | _ => none
  | .assertQud, d => match d.latestContent with
    | some (.assert p) => some (d.pushQud ⟨Content.polar p, ∅⟩)
    | _ => none
  | .check u t, d => match d.latestContent, u.content with
    | some (.assert p), .check p' =>
      if p = p' ∧ d.maxQud = some (Content.polar p) then some ((t.act d).recordMove u) else none
    | _, _ => none
  | .accept u, d => match d.latestContent, u.content with
    | some (.assert p), .accept p' =>
      if p = p' ∧ d.maxQud = some (Content.polar p) then some (d.swapTurn.recordMove u) else none
    | _, _ => none
  | .confirm u, d => match d.latestContent, u.content with
    | some (.check p), .confirm p' =>
      if p = p' ∧ d.maxQud = some (Content.polar p) then some (d.swapTurn.recordMove u) else none
    | _, _ => none
  | .factUpdate, d => match d.latestContent with
    | some (.accept p) | some (.confirm p) =>
      if d.maxQud = some (Content.polar p) then some ((d.addFact p).downdateQud Content.Resolves)
      else none
    | _ => none
  | .qcoord u, d => match d.latestContent, u.content, d.qud with
    | some (.ask q), .ask q₁, i :: rest =>
      if i.question = q ∧ ¬ Content.Influences (Fact := Fact) q₁ q then
        some { d.recordMove u with qud := i :: ⟨q₁, ∅⟩ :: rest } else none
    | _, _, _ => none
  | .pendingUpdate u s a, d => some { d.pushPending u with speaker := s, addressee := a }
  | .contextualInstantiation s, d => match d.pending with
    | u :: rest => some { d with pending := u.instantiate s :: rest }
    | [] => none
  | .pendified r, d => match d.pending with
    | u :: rest =>
      if u.parameters = ∅ then (r.apply { d with pending := rest }).filter (·.latestMove = some u)
      else none
    | [] => none
  | .parameterIdentification u cr, d =>
    d.clarify Copropositional .change
      (fun _ u ↦ ⟨Clarifiable.mean (Fact := Fact) d.speaker u, {u}⟩) u cr
  | .parameterFocussing u cr, d =>
    d.clarify Copropositional .change (fun v u ↦ ⟨Clarifiable.focus (P := P) v.content u, {u}⟩) u cr
  | .crAccommodation u, d => match d.pending, d.latestMove with
    | v :: rest, some v₀ =>
      if u ∈ v₀.constituents ∧
          (qudContrib v.content = some (Clarifiable.mean (Fact := Fact) d.addressee u) ∨
            qudContrib v.content = some (Clarifiable.focus (P := P) v₀.content u)) then
        match qudContrib v.content with
        | some q => some { (d.pushQud ⟨q, {u}⟩).recordMove v with pending := rest }
        | none => none
      else none
    | _, _ => none
  | .repair u cr, d =>
    d.clarify Copropositional .keep (fun _ u ↦ ⟨Clarifiable.mean (Fact := Fact) d.speaker u, {u}⟩)
      u cr

/-- Apply a trace of rules in sequence (the composition of conversational rules). -/
def run (trace : List (Rule P Fact Q)) (d : Board P Fact Q) : Option (Board P Fact Q) :=
  trace.foldlM (fun d r ↦ r.apply d) d

/-- An utterance is coherent relative to a gameboard when some rule makes it the
latest move (Ch. 4 M-Coherence; Appendix B Utterance Coherence). -/
def Coherent (d : Board P Fact Q) (u : Utterance Fact Q) : Prop :=
  ∃ r : Rule P Fact Q, ∃ d', r.apply d = some d' ∧ d'.latestMove = some u

/-- `d'` is a possible development of `d`. -/
def Reachable (d d' : Board P Fact Q) : Prop := ∃ trace, run trace d = some d'

/-! ### QUD well-formedness

The Question Introduction Appropriateness Condition (52) p. 89 lets a question
enter QUD only if no fact resolves it; (53) builds it into the gameboard type
as `non-resolve-cond`, here the predicate `Gameboard.NonResolveCond`. -/

theorem askQud_nonResolveCond_iff {d d' : Board P Fact Q} {q : Q}
    (hm : d.latestContent = some (.ask q)) (h : Rule.askQud.apply d = some d') :
    d'.NonResolveCond Content.Resolves ↔
      (¬∃ f ∈ d.facts, Content.Resolves f q) ∧ d.NonResolveCond Content.Resolves := by
  simp only [Rule.apply, hm, Option.some.injEq] at h
  exact h ▸ d.nonResolveCond_pushQud_iff _

theorem factUpdate_nonResolveCond {d d' : Board P Fact Q}
    (h : Rule.factUpdate.apply d = some d') : d'.NonResolveCond Content.Resolves := by
  unfold Rule.apply at h
  split at h <;> simp only [Option.ite_none_right_eq_some, reduceCtorEq] at h <;>
    exact Option.some.inj h.2 ▸ Gameboard.nonResolveCond_downdateQud _ _

theorem factUpdate_polar {d d' : Board P Fact Q} {p : Fact}
    (hm : d.latestContent = some (.accept p))
    (h : Rule.factUpdate.apply d = some d') : ∀ i ∈ d'.qud, i.question ≠ Content.polar p := by
  have := factUpdate_nonResolveCond h
  intro i hi hq
  refine this i hi ⟨p, ?_, hq ▸ Content.resolves_polar p⟩
  simp only [Rule.apply, hm, Option.ite_none_right_eq_some] at h
  exact Option.some.inj h.2 ▸ Finset.mem_insert_self _ _

/-! ### Conversational genres (§4.6)

A genre is a type of the gameboards that end conversations of that kind (ex. 88
pp. 104–105), here a set of gameboards; the three genres of (88) differ only in the issues
they require among the questions no longer under discussion. A move is relevant to a genre
when some development of the gameboard after it is of that type, `outcome(dgb, G)` fulfilled
(exx. 89–90 p. 105). Initiating Move (ex. 94 p. 108) is Free Speech restricted to moves the
speaker takes to be relevant to the genre, which the private part of their information state
records (ex. 93 p. 107); here the genre is an argument. -/

/-- `u` is relevant to `G` in `d` when some development of `d` extended by `u` is of type `G`. -/
def GenreRelevant (G : Set (Board P Fact Q)) (d : Board P Fact Q) (u : Utterance Fact Q) : Prop :=
  ∃ d', Reachable (d.recordMove u) d' ∧ d' ∈ G

/-- Initiating Move: with QUD empty, a move relevant to the assumed genre. -/
def IsInitiating (G : Set (Board P Fact Q)) (d : Board P Fact Q) (u : Utterance Fact Q) : Prop :=
  d.qud = [] ∧ GenreRelevant G d u

theorem coherent_of_isInitiating {G : Set (Board P Fact Q)} {d : Board P Fact Q}
    {u : Utterance Fact Q} (h : IsInitiating G d u) : Coherent d u :=
  ⟨.freeSpeech u .keep, d.recordMove u, by simp [Rule.apply, h.1, Turn.act], by simp⟩

/-! ### Clarification (§6.6, §8.2)

A Clarification Context Update Rule fixes the question it accommodates and who takes the turn,
and is merged with Utterance Interpolation ((71) p. 192). In the final versions of the rules
(Appendix B (26e) p. 374, and (31) p. 287 for repair), MaxQUD is paired with the clarified
sub-utterance, a constituent of the maximal pending utterance, as its focus-establishing
constituent, which a reprise fragment must then match in category (p. 254). Backwards-looking
appropriateness repair ((31) p. 287) is Parameter Identification ((70) p. 192) without the turn
change: the speaker of a pending utterance accommodates the issue of what they meant by one of its
constituents and continues co-propositionally with it. -/

theorem parameterIdentification_eq_repair_swapTurn (u : SubUtterance grammar)
    (cr : Utterance Fact Q) (d : Board P Fact Q) :
    (Rule.parameterIdentification u cr).apply d =
      ((Rule.repair u cr).apply d).map Gameboard.swapTurn := by
  simp only [Rule.apply, Gameboard.clarify, Gameboard.interpolate, Turn.act]
  cases d.maxPending with
  | none => rfl
  | some v => simp only [Option.bind_some]; split_ifs <;> rfl

/-! ### Worked traces (Ch. 4)

The book abbreviates contents as `qᵢ` and `pᵢ` and tabulates each trace as
the sequence of rules applied with the gameboard they produce. The schematic
content types below fix exactly the relations each trace's side conditions
require. -/

/-- The initial gameboard: `A` addressing `B`, with no moves. -/
def initial (facts : Finset Fact := ∅) : Board Agent Fact Q :=
  Gameboard.initial .A .B facts

/-- The columns of a trace table: FACTS, QUD and the contents of MOVES. -/
def table (d : Board Agent Fact Q) : Finset Fact × List Q × List (IllocutionaryAct Fact Q) :=
  (d.facts, d.qud.map (·.question), d.moves.map (·.content))

end Rules

/-! Trace (66) p. 95 of dialogue (65): `q₀` who to invite, `q₁` who will agree to
come (influencing `q₀`), `p₁` an answer resolving `q₁`, `p₂` About `q₀`; and
trace (68) p. 95 of dialogue (67): A asserts `p₁`, checks it, B confirms. -/
namespace Ex66

inductive Fact
  | p₁
  | p₂
  deriving DecidableEq, Repr

inductive Q
  | q₀
  | q₁
  | polar (p : Fact)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  Resolves f q := q = .polar f ∨ f = .p₁ ∧ q = .q₁
  decResolves _ _ := inferInstanceAs (Decidable (_ ∨ _))
  polar := .polar
  About f q := f = .p₁ ∧ q = .q₁ ∨ f = .p₂ ∧ q = .q₀
  Influences q q' := q = .q₁ ∧ q' = .q₀
  decAbout _ _ := inferInstanceAs (Decidable (_ ∨ _))
  decInfluences _ _ := inferInstanceAs (Decidable (_ ∧ _))
  resolves_polar _ := Or.inl rfl

instance : Clarifiable Agent Fact Q where
  mean _ _ := .q₀
  focus _ _ := .q₀

/-- A asks `q₀`; B asks `q₁`; A asserts `p₁`; B accepts; B asserts `p₂`; A accepts. -/
def trace66 : List (Rule Agent Fact Q) :=
  [.freeSpeech (ofMove (.ask .q₀)) .keep, .askQud,
   .qspec (ofMove (.ask .q₁)) .change, .askQud,
   .qspec (ofMove (.assert .p₁)) .change, .assertQud,
   .accept (ofMove (.accept .p₁)), .factUpdate,
   .qspec (ofMove (.assert .p₂)) .keep, .assertQud,
   .accept (ofMove (.accept .p₂)), .factUpdate]

/-- After (65): FACTS `{p₁, p₂}`, QUD `⟨q₀⟩`, the six moves recorded. -/
theorem trace : (run trace66 initial).map table =
    some ({.p₁, .p₂}, [.q₀],
      [.accept .p₂, .assert .p₂, .accept .p₁, .assert .p₁, .ask .q₁, .ask .q₀]) := by decide

/-- A asserts `p₁`, checks it, B confirms. -/
def trace68 : List (Rule Agent Fact Q) :=
  [.freeSpeech (ofMove (.assert .p₁)) .keep, .assertQud,
   .check (ofMove (.check .p₁)) .keep, .confirm (ofMove (.confirm .p₁)), .factUpdate]

/-- After (67): FACTS `{p₁}` and QUD empty. -/
theorem trace68_table : (run trace68 initial).map table =
    some ({.p₁}, [], [.confirm .p₁, .check .p₁, .assert .p₁]) := by decide

end Ex66

/-! Trace (79) p. 99 of dialogue (78): `q₀` whom Max invites, `q₁` when the
guests arrive, not influencing `q₀`; `p₀` resolves `q₀`, `p₁` is About `q₁`. -/
namespace Ex79

inductive Fact
  | p₀
  | p₁
  deriving DecidableEq, Repr

inductive Q
  | q₀
  | q₁
  | polar (p : Fact)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  Resolves f q := q = .polar f ∨ f = .p₀ ∧ q = .q₀
  decResolves _ _ := inferInstanceAs (Decidable (_ ∨ _))
  polar := .polar
  About f q := f = .p₀ ∧ q = .q₀ ∨ f = .p₁ ∧ q = .q₁
  Influences _ _ := False
  decAbout _ _ := inferInstanceAs (Decidable (_ ∨ _))
  decInfluences _ _ := inferInstanceAs (Decidable False)
  resolves_polar _ := Or.inl rfl

instance : Clarifiable Agent Fact Q where
  mean _ _ := .q₀
  focus _ _ := .q₀

/-- A asks `q₀` then `q₁` (QCoord); B answers `q₀`; A accepts; B answers `q₁`. -/
def trace79 : List (Rule Agent Fact Q) :=
  [.freeSpeech (ofMove (.ask .q₀)) .keep, .askQud, .qcoord (ofMove (.ask .q₁)),
   .qspec (ofMove (.assert .p₀)) .change, .assertQud,
   .accept (ofMove (.accept .p₀)), .factUpdate,
   .qspec (ofMove (.assert .p₁)) .change, .assertQud]

/-- After (78): FACTS `{p₀}`, QUD `⟨p₁?, q₁⟩`. -/
theorem trace : (run trace79 initial).map table =
    some ({.p₀}, [.polar .p₁, .q₁],
      [.assert .p₁, .accept .p₀, .assert .p₀, .ask .q₁, .ask .q₀]) := by decide

end Ex79

/-! ### Activity relevance: dialogue (95) p. 108

B takes the genre to be CasualChat (ex. 88a), whose anticipated issues are
how A is and how B is. "I'm off" is About the latter and, once accepted,
resolves it; that A is present already resolves the former. -/

namespace Ex95

inductive Fact
  | here
  | off
  deriving DecidableEq, Repr

inductive Q
  | howA
  | howB
  | polar (p : Fact)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  Resolves f q := q = .polar f ∨ f = .here ∧ q = .howA ∨ f = .off ∧ q = .howB
  decResolves _ _ := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
  polar := .polar
  About f q := f = .off ∧ q = .howB
  Influences _ _ := False
  decAbout _ _ := inferInstanceAs (Decidable (_ ∧ _))
  decInfluences _ _ := inferInstanceAs (Decidable False)
  resolves_polar _ := Or.inl rfl

instance : Clarifiable Agent Fact Q where
  mean _ _ := .howA
  focus _ _ := .howA

/-- CasualChat (88a) is the type of the gameboards that end a conversation in which the issues
`λP.P(A)` and `λP.P(B)` have been resolved, with nothing left under discussion. -/
def casualChat : Set (Board Agent Fact Q) :=
  {d | d.qud = [] ∧ ∀ q ∈ [Q.howA, .howB], ∃ f ∈ d.facts, Content.Resolves f q}

instance : DecidablePred (· ∈ casualChat) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem initiating_off :
    IsInitiating casualChat ((initial {.here}).recordMove (ofMove IllocutionaryAct.greet))
      (ofMove (.assert .off)) :=
  ⟨rfl, _, ⟨[.assertQud, .accept (ofMove (.accept .off)), .factUpdate], rfl⟩, by decide⟩

end Ex95

/-! ### Grounding and clarification: dialogue (90) of Ch. 6, p. 201

A asks whether George is here. A, omniscient about her own utterance,
instantiates its contextual parameter and integrates it; B cannot, and
initiates clarification by Parameter Focussing with "Is WHO here?". After that
utterance the two gameboards are those of Ch. 6 (91) p. 202: A has `p?` under
discussion and B's clarification request pending; B has the question who A is
asking about under discussion and A's utterance pending. -/

namespace George

inductive Fact
  | georgeHere
  deriving DecidableEq, Repr

/-- `p?`; `λx.Ask(A, B, ?In(l, x))`, the focussed question; and `λx.Mean(A, u, x)`. -/
inductive Q
  | polar (p : Fact)
  | whoAsked
  | meant (u : SubUtterance grammar)
  deriving DecidableEq

instance : Content Fact Q where
  Resolves f q := q = .polar f
  decResolves _ _ := inferInstanceAs (Decidable (_ = _))
  polar := .polar
  About _ _ := False
  Influences _ _ := False
  decAbout _ _ := inferInstanceAs (Decidable False)
  decInfluences _ _ := inferInstanceAs (Decidable False)
  resolves_polar _ := rfl

instance : Clarifiable Agent Fact Q where
  mean _ u := .meant u
  focus _ _ := .whoAsked

/-- The sub-utterance "George". -/
def george : SubUtterance grammar := { form := "George", category := .np, denotation := .george }

/-- A's utterance, with the referent of "George" a contextual parameter. -/
def u₀ : Utterance Fact Q :=
  { form := "Is George here?", category := .s, content := .ask (.polar .georgeHere),
    parameters := {.george}, constituents := {george} }

/-- A's utterance with its parameter witnessed. -/
def w₀ : Utterance Fact Q := u₀.instantiate {.george}

/-- B's clarification request. -/
def u₁ : Utterance Fact Q := { form := "Is WHO here?", category := .s, content := .ask .whoAsked }

/-- A: utter `u₀`, instantiate it, integrate it by Free Speech, hear `u₁`. -/
def traceA : List (Rule Agent Fact Q) :=
  [.pendingUpdate u₀ .A .B, .contextualInstantiation {.george},
   .pendified (.freeSpeech w₀ .keep), .askQud, .pendingUpdate u₁ .B .A]

/-- B: hear `u₀`, clarify by Parameter Focussing with `u₁`. -/
def traceB : List (Rule Agent Fact Q) :=
  [.pendingUpdate u₀ .A .B, .parameterFocussing george u₁]

/-- (91b): A's gameboard. -/
theorem dgb_A : run traceA initial = some
    { speaker := .B, addressee := .A, pending := [u₁], qud := [⟨.polar .georgeHere, ∅⟩],
      moves := [w₀] } := by decide

/-- (91c): B's gameboard. -/
theorem dgb_B : run traceB initial = some
    { speaker := .B, addressee := .A, pending := [u₀], qud := [⟨.whoAsked, {george}⟩],
      moves := [u₁] } := by decide

theorem differ : ∀ dA ∈ run traceA initial, ∀ dB ∈ run traceB initial,
    dA.qud ≠ dB.qud ∧ dA.pending ≠ dB.pending := by
  simp only [dgb_A, dgb_B, Option.mem_def, Option.some.injEq]
  rintro _ rfl _ rfl
  decide

/-- A integrates B's request by CR Accommodation: the focussed question becomes
MaxQUD and the request is no longer pending. -/
theorem accommodate :
    (run (traceA ++ [.crAccommodation george]) initial).map
        (fun d ↦ (d.qud.map (·.question), d.pending)) =
      some ([.whoAsked, .polar .georgeHere], []) := by decide

end George

/-! ### Who holds the turn (Chs. 1 and 8)

Only the addressee has the two clarification-request readings of "Bo?" and only the original
speaker its self-correction reading (ex. 22); bare "Why?" is resolved differently by whoever holds
the turn, the Turn-Taking Puzzle (ex. 23); and mid-utterance self-repair is the within-utterance
analogue of a clarification request (ex. 24). Each turns on the turn a rule leaves, a general
property of the inventory. -/

section Turn

variable {P Fact Q : Type} [DecidableEq P] [DecidableEq Fact] [DecidableEq Q] [Content Fact Q]
  [Clarifiable P Fact Q] {d d' : Board P Fact Q}

variable {u : SubUtterance grammar} {cr : Utterance Fact Q}

theorem speaker_parameterIdentification
    (h : (Rule.parameterIdentification u cr).apply d = some d') : d'.speaker = d.addressee :=
  d.speaker_clarify h

theorem speaker_parameterFocussing (h : (Rule.parameterFocussing u cr).apply d = some d') :
    d'.speaker = d.addressee :=
  d.speaker_clarify h

theorem speaker_repair (h : (Rule.repair u cr).apply d = some d') : d'.speaker = d.speaker :=
  d.speaker_clarify h

theorem speaker_qspec {m : Utterance Fact Q} {t : Turn} (h : (Rule.qspec m t).apply d = some d') :
    d'.speaker = (t.act d).speaker := by
  unfold Rule.apply at h
  split at h <;> simp only [Option.ite_none_right_eq_some, reduceCtorEq] at h
  obtain ⟨-, h⟩ := h
  cases h
  rfl

end Turn

/-! The rows of exx. 22–24: A asks about Bo, or which members of the audience own a parakeet, and
either A or B follows with "Bo?" or "Why?". -/
namespace Ex22

inductive Fact
  | p₀
  deriving DecidableEq, Repr

/-- A's question, the follow-up `why` influencing it, `p?`, and `λx.Mean(A, u, x)`. -/
inductive Q
  | q₀
  | why
  | polar (p : Fact)
  | meant (u : SubUtterance grammar)
  deriving DecidableEq

instance : Content Fact Q where
  Resolves f q := q = .polar f
  decResolves _ _ := inferInstanceAs (Decidable (_ = _))
  polar := .polar
  About _ _ := False
  Influences q' q := q' = .why ∧ q = .q₀
  decAbout _ _ := inferInstanceAs (Decidable False)
  decInfluences _ _ := inferInstanceAs (Decidable (_ ∧ _))
  resolves_polar _ := rfl

instance : Clarifiable Agent Fact Q where
  mean _ u := .meant u
  focus _ _ := .q₀

/-- The sub-utterance "Bo". -/
def bo : SubUtterance grammar := { form := "Bo", category := .np, denotation := .bo }

/-- A's question, with the referent of "Bo" a contextual parameter. -/
def u₀ : Utterance Fact Q :=
  { form := "Who does Bo admire?", category := .s, content := .ask .q₀,
    parameters := {.bo}, constituents := {bo} }

/-- The construction of a row: a clarification request by the addressee, a self-repair by the
original speaker, or a bare follow-up question. -/
inductive Construction
  | clarification
  | selfRepair
  | followUp
  deriving DecidableEq, Repr

/-- A row: its construction and the turn the book records after it. -/
structure Row where
  construction : Construction
  turn : Turn
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row :=
  (ex.parse? (α := Row) "speaker" [("addressee", ⟨.clarification, .change⟩),
      ("original speaker", ⟨.selfRepair, .keep⟩)]).orElse fun _ ↦
    (ex.parse? "repair" [("other-initiated", ⟨.clarification, .change⟩),
        ("self-initiated", ⟨.selfRepair, .keep⟩)]).orElse fun _ ↦
      ex.parse? "turn" [("kept", ⟨.followUp, .keep⟩), ("taken", ⟨.followUp, .change⟩)]

/-- The gameboard the row's second utterance meets: A's question pending, for a clarification
request or a repair addressing its constituent "Bo", or under discussion, for a follow-up. -/
def Row.board (r : Row) : Board Agent Fact Q :=
  match r.construction with
  | .clarification | .selfRepair => initial.pushPending u₀
  | .followUp => (initial.recordMove (ofMove (.ask .q₀))).pushQud ⟨.q₀, ∅⟩

/-- The rule the construction instantiates: Parameter Identification or repair over "Bo", or
QSPEC with the influencing `why`, taking whichever turn the row records. -/
def Row.rule (r : Row) : Rule Agent Fact Q :=
  match r.construction with
  | .clarification => .parameterIdentification bo (ofMove (.ask (.meant bo)))
  | .selfRepair => .repair bo (ofMove (.ask (.meant bo)))
  | .followUp => .qspec (ofMove (.ask .why)) r.turn

/-- The seven rows of exx. 22–24. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_turn :
    ∀ r ∈ rows, (r.rule.apply r.board).map (·.speaker) = some (r.turn.act r.board).speaker := by
  decide

end Ex22

/-! ### Taxonomies

The clarification-request forms of the BNC study reported in §6.2.1 (Table
6.1 p. 153), and the non-sentential-utterance classes of Table 7.3 p. 221 with
their functional grouping in Table 7.4 p. 222, Sluice split into its reprise
and direct uses. Readings of clarification requests are `RFReading`. -/

/-- The eight clarification-request forms (§6.2.1). -/
inductive CRForm
  /-- "Eh? / What? / Pardon?" -/
  | wot
  /-- A context-independent request, "What did you say?" -/
  | explicit
  /-- Verbatim repetition of the troubled utterance -/
  | literalReprise
  /-- Repetition with a constituent replaced by a wh-phrase -/
  | whSubstitutedReprise
  /-- A bare wh-phrase -/
  | repriseSluice
  /-- A bare phrase -/
  | repriseFragment
  /-- The sentence with the targeted constituent omitted -/
  | gap
  /-- A guess completing an unfinished sentence -/
  | filler
  deriving DecidableEq, Repr

/-- The functional grouping of Table 7.4. -/
inductive NSUFunction
  | positiveFeedback
  | answer
  | metacommunicativeQuery
  | extensionMove
  deriving DecidableEq, Repr

/-- The NSU classes of Table 7.3, with Sluice split as in Table 7.4. -/
inductive NSUClass
  /-- "mmh" -/
  | plainAcknowledgement
  /-- "Bo, hmm." -/
  | repeatedAcknowledgement
  /-- "Bo?" -/
  | clarificationEllipsis
  /-- "Okay?" -/
  | checkQuestion
  /-- "Who?" reprising the antecedent -/
  | repriseSluice
  /-- completing "Did Bo …" with "leave?" -/
  | filler
  /-- "Bo" -/
  | shortAnswer
  /-- "Yes" -/
  | affirmativeAnswer
  /-- "No" -/
  | rejection
  /-- "Bo, yes." -/
  | repeatedAffirmativeAnswer
  /-- "No, Max." -/
  | helpfulRejection
  /-- "Maybe" -/
  | propositionalModifier
  /-- "Great!" -/
  | factiveModifier
  /-- "Yesterday" -/
  | bareModifierPhrase
  /-- "Who?" requesting new information -/
  | directSluice
  /-- "And Max." -/
  | conjunctionFragment
  deriving DecidableEq, Repr

/-- The function of each class (Table 7.4). -/
def NSUClass.function : NSUClass → NSUFunction
  | .plainAcknowledgement | .repeatedAcknowledgement => .positiveFeedback
  | .clarificationEllipsis | .checkQuestion | .repriseSluice | .filler => .metacommunicativeQuery
  | .shortAnswer | .affirmativeAnswer | .rejection | .repeatedAffirmativeAnswer
  | .helpfulRejection | .propositionalModifier => .answer
  | .factiveModifier | .bareModifierPhrase | .directSluice | .conjunctionFragment => .extensionMove

end Ginzburg2012
