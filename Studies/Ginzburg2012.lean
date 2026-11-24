module

public import Linglib.Discourse.Gameboard.Rule
public import Linglib.Data.Examples.Ginzburg2012
public import Linglib.Data.Examples.Readers

/-!
# Ginzburg (2012): The Interactive Stance

This file formalizes the conversational rules of [ginzburg-2012] over the dialogue gameboard
`Gameboard`: each participant's turn holder and addressee, the commonly accepted FACTS, the MOVES
made, the questions under discussion and, once metacommunication enters, the ungrounded utterances
PENDING. A rule is a relation between a gameboard meeting its preconditions and the gameboards
its effects describe. The move rules of Ch. 4 generate one transition relation and the rules of
grounding and clarification a second that includes it, and a conversation's possible developments
are the reflexive transitive closure.

Asking a question keeps `non-resolve-cond` exactly when no fact resolves it, the Question
Introduction Appropriateness Condition, and FACTS update restores the condition. A move a genre
makes initiating is coherent. Each clarification rule is a question merged with Utterance
Interpolation, so it makes the clarified constituent of the maximal pending utterance the
focus-establishing constituent of MaxQUD, and Parameter Identification is self-repair followed by
a change of turn.

The worked traces of Ch. 4 reach the tabulated gameboards, and after "Is George here? / Is WHO
here?" the two participants' gameboards differ in QUD and PENDING although both processed the
same utterances. The clarification rules pass the turn to the clarifier, repair keeps it, and
QSPEC leaves it open; the rows of Chs. 1 and 8 record who holds the turn after a clarification
request, a self-repair and a bare follow-up question.

## Implementation notes

* The schematic content types of the traces (`Content`, `Clarifiable`) fix exactly the aboutness,
  influence and resolution relations each trace's side conditions require. Utterances are
  written orthographically, and the categories and contextual parameters are those the examples
  need.
* Contextual Instantiation takes the labels of the parameters it witnesses rather than the
  witnessing record, so the utterance it produces is a contextual extension of MaxPending by
  `LocutionaryProposition.exists_eq_instantiate_iff`.
* The backwards-looking appropriateness repair follows its statement in the text, (31) p. 287.
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

open Gameboard

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

/-- A sub-utterance of the examples has an orthographic form, its category, and as its denotation
the parameter it contributes. -/
abbrev Constituent := SubUtterance String Category Parameter

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
  mean : P → Constituent → Q
  focus : IllocutionaryAct Fact Q → Constituent → Q

/-- An utterance with illocutionary content. -/
abbrev Utterance (Fact Q : Type) :=
  LocutionaryProposition String Category Parameter Parameter (IllocutionaryAct Fact Q)

/-- A gameboard whose utterances, in MOVES and PENDING, carry illocutionary content. -/
abbrev Board (P Fact Q : Type) :=
  Gameboard P Fact (Utterance Fact Q) (InformationStructure Q Constituent)

/-- The two participants of a duologue. -/
inductive Agent
  | A
  | B
  deriving DecidableEq, Repr

section Rules

variable {P Fact Q : Type} [DecidableEq Fact] [DecidableEq Q] [Content Fact Q]

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

omit [DecidableEq Fact] [DecidableEq Q] in
/-- A clarification rule pairing its question with the clarified constituent makes that
constituent, a constituent of MaxPending, the focus-establishing constituent of MaxQUD. -/
theorem focusEstablishing_clarification {q : Utterance Fact Q → Q} {u : Constituent}
    {d d' : Board P Fact Q}
    (h : Clarification Copropositional u (fun v ↦ ⟨q v, {u}⟩) d d') :
    (∃ v ∈ d.maxPending, u ∈ v.constituents) ∧
      d'.qud.head?.map (·.focusEstablishing) = some {u} := by
  obtain ⟨v, hv, hu, h⟩ := h.qud
  exact ⟨⟨v, hv, hu⟩, by simp [h]⟩

/-! ### Move rules (Ch. 4)

Each rule relates a gameboard meeting its preconditions to the gameboards its effects describe.
Accept and Confirm change the turn; Free Speech, QSPEC and checking leave it underspecified; the
rest keep it. -/

/-- Greeting opens a conversation with no moves made and nothing under discussion. -/
def Greeting : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ d.moves = [] ∧ d.qud = [] ∧ d' = d.recordMove (ofMove IllocutionaryAct.greet)

/-- Counter-greeting answers a greeting. -/
def CounterGreeting : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ d.latestContent = some .greet ∧
    d' = d.swapTurn.recordMove (ofMove IllocutionaryAct.counterGreet)

/-- Free Speech: with nothing under discussion, any move may be made. -/
def FreeSpeech : Board P Fact Q → Board P Fact Q → Prop :=
  turnUnderspec fun d d' ↦ d.qud = [] ∧ ∃ u, d' = d.recordMove u

/-- QSPEC: a move specific to MaxQUD may be made. -/
def QSpec : Board P Fact Q → Board P Fact Q → Prop :=
  turnUnderspec fun d d' ↦
    ∃ i ∈ d.qud.head?, ∃ u, QSpecific u.content i.question ∧ d' = d.recordMove u

/-- Ask QUD-incrementation: the question asked becomes MaxQUD. -/
def AskQud : Board P Fact Q → Board P Fact Q → Prop :=
  QudIncrementation fun
    | .ask q => some q
    | _ => none

/-- Assert QUD-incrementation: `p?` becomes MaxQUD once `p` is asserted. -/
def AssertQud : Board P Fact Q → Board P Fact Q → Prop :=
  QudIncrementation fun
    | .assert p => some (Content.polar p)
    | _ => none

/-- Assertion checking: the asserter asks for confirmation of `p` while `p?` is MaxQUD. -/
def Check : Board P Fact Q → Board P Fact Q → Prop :=
  turnUnderspec fun d d' ↦ ∃ p u, d.latestContent = some (.assert p) ∧ u.content = .check p ∧
    d.maxQud = some (Content.polar p) ∧ d' = d.recordMove u

/-- Accept: the addressee accepts the assertion of `p` while `p?` is MaxQUD. -/
def Accept : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ p u, d.latestContent = some (.assert p) ∧ u.content = .accept p ∧
    d.maxQud = some (Content.polar p) ∧ d' = d.swapTurn.recordMove u

/-- Confirm: the addressee confirms the checked `p` while `p?` is MaxQUD. -/
def Confirm : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ p u, d.latestContent = some (.check p) ∧ u.content = .confirm p ∧
    d.maxQud = some (Content.polar p) ∧ d' = d.swapTurn.recordMove u

/-- Fact update/QUD-downdate: an accepted or confirmed `p` joins FACTS, and the questions the
facts now resolve leave QUD. -/
def FactUpdate : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ p, (d.latestContent = some (.accept p) ∨ d.latestContent = some (.confirm p)) ∧
    d.maxQud = some (Content.polar p) ∧ d' = (d.addFact p).downdateQud Content.Resolves

/-- QCoord: the asker of `q` follows it with a question `q₁` that does not influence `q`, which
joins QUD below it. -/
def QCoord : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ q q₁ u i rest, d.latestContent = some (.ask q) ∧ u.content = .ask q₁ ∧
    d.qud = i :: rest ∧ i.question = q ∧ ¬Content.Influences (Fact := Fact) q₁ q ∧
    d' = { d.recordMove u with qud := i :: ⟨q₁, ∅⟩ :: rest }

/-- The transition relation of the move rules of [ginzburg-2012] Ch. 4, as Appendix B lists
them. -/
inductive Move : Board P Fact Q → Board P Fact Q → Prop
  | greeting {d d'} : Greeting d d' → Move d d'
  | counterGreeting {d d'} : CounterGreeting d d' → Move d d'
  | freeSpeech {d d'} : FreeSpeech d d' → Move d d'
  | qspec {d d'} : QSpec d d' → Move d d'
  | askQud {d d'} : AskQud d d' → Move d d'
  | assertQud {d d'} : AssertQud d d' → Move d d'
  | check {d d'} : Check d d' → Move d d'
  | accept {d d'} : Accept d d' → Move d d'
  | confirm {d d'} : Confirm d d' → Move d d'
  | factUpdate {d d'} : FactUpdate d d' → Move d d'
  | qcoord {d d'} : QCoord d d' → Move d d'

/-! ### QUD well-formedness

The Question Introduction Appropriateness Condition (52) p. 89 lets a question
enter QUD only if no fact resolves it; (53) builds it into the gameboard type
as `non-resolve-cond`, here the predicate `Gameboard.NonResolveCond`. -/

omit [DecidableEq Fact] [DecidableEq Q] in
theorem askQud_nonResolveCond_iff {d d' : Board P Fact Q} {q : Q}
    (hm : d.latestContent = some (.ask q)) (h : AskQud d d') :
    d'.NonResolveCond Content.Resolves ↔
      (¬∃ f ∈ d.facts, Content.Resolves f q) ∧ d.NonResolveCond Content.Resolves :=
  h.nonResolveCond_iff _ (by rw [hm]; rfl)

omit [DecidableEq Q] in
theorem factUpdate_nonResolveCond {d d' : Board P Fact Q}
    (h : FactUpdate d d') : d'.NonResolveCond Content.Resolves := by
  obtain ⟨_, -, -, rfl⟩ := h
  exact Gameboard.nonResolveCond_downdateQud _ _

omit [DecidableEq Q] in
theorem factUpdate_polar {d d' : Board P Fact Q} {p : Fact}
    (hm : d.latestContent = some (.accept p))
    (h : FactUpdate d d') : ∀ i ∈ d'.qud, i.question ≠ Content.polar p := by
  have := factUpdate_nonResolveCond h
  intro i hi hq
  refine this i hi ⟨p, ?_, hq ▸ Content.resolves_polar p⟩
  obtain ⟨p', hp', -, rfl⟩ := h
  rw [hm] at hp'
  obtain rfl : p = p' := by simpa using hp'
  exact Finset.mem_insert_self _ _

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
  ∃ d', Relation.ReflTransGen Move (d.recordMove u) d' ∧ d' ∈ G

/-- Initiating Move: with QUD empty, a move relevant to the assumed genre. -/
def IsInitiating (G : Set (Board P Fact Q)) (d : Board P Fact Q) (u : Utterance Fact Q) : Prop :=
  d.qud = [] ∧ GenreRelevant G d u

/-! ### Grounding and clarification (Ch. 6, §8.2)

A Clarification Context Update Rule fixes the question it accommodates and who takes the turn,
and is merged with Utterance Interpolation ((71) p. 192). In the final versions of the rules
(Appendix B (26e) p. 374, and (31) p. 287 for repair), MaxQUD is paired with the clarified
sub-utterance, a constituent of the maximal pending utterance, as its focus-establishing
constituent, which a reprise fragment must then match in category (p. 254). Backwards-looking
appropriateness repair ((31) p. 287) is Parameter Identification ((70) p. 192) without the turn
change: the speaker of a pending utterance accommodates the issue of what they meant by one of its
constituents and continues co-propositionally with it. -/

/-- Pending Update: an utterance by one participant to another becomes MaxPending. -/
def PendingUpdate : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ u speaker addressee, d' = d.pendingUpdate u speaker addressee

/-- Contextual Instantiation witnesses some parameters of MaxPending, as an agent does who
believes their witnesses are the ones the speaker intended. -/
def ContextualInstantiation : Board P Fact Q → Board P Fact Q → Prop :=
  PendingReplacement fun v w ↦ ∃ s, w = v.instantiate s

/-- Pendification of the rules `R`: the move they record originates in PENDING, with no
contextual parameter left to witness. -/
def Pendified (R : Board P Fact Q → Board P Fact Q → Prop) :
    Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ u rest, d.pending = u :: rest ∧ u.parameters = ∅ ∧
    R { d with pending := rest } d' ∧ d'.latestMove = some u

variable [Clarifiable P Fact Q]

/-- Backwards-looking appropriateness repair: the speaker keeps the turn to say what they meant
by a constituent `u` of MaxPending. -/
def Repair : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ u, Clarification Copropositional u
    (fun _ ↦ ⟨Clarifiable.mean (Fact := Fact) d.speaker u, {u}⟩) d d'

/-- Parameter Identification: the addressee takes the turn to ask what the speaker meant by a
constituent `u` of MaxPending. -/
def ParameterIdentification : Board P Fact Q → Board P Fact Q → Prop :=
  passTurn Repair

/-- Parameter Focussing: the addressee takes the turn to ask the content of MaxPending with the
parameter of its constituent `u` abstracted. -/
def ParameterFocussing : Board P Fact Q → Board P Fact Q → Prop :=
  passTurn fun d d' ↦ ∃ u, Clarification Copropositional u
    (fun v ↦ ⟨Clarifiable.focus (P := P) v.content u, {u}⟩) d d'

/-- CR Accommodation integrates the other party's clarification request, so the clarified speaker
is the current addressee. -/
def CRAccommodation : Board P Fact Q → Board P Fact Q → Prop :=
  fun d d' ↦ ∃ u v rest v₀ q, d.pending = v :: rest ∧ d.latestMove = some v₀ ∧
    u ∈ v₀.constituents ∧ qudContrib v.content = some q ∧
    (q = Clarifiable.mean (Fact := Fact) d.addressee u ∨
      q = Clarifiable.focus (P := P) v₀.content u) ∧
    d' = { (d.pushQud ⟨q, {u}⟩).recordMove v with pending := rest }

/-- The transition relation of grounding and clarification, which includes the move rules:
Pending Update, Contextual Instantiation, pendification, the two Clarification Context Update
Rules, CR Accommodation, and repair. -/
inductive Grounding : Board P Fact Q → Board P Fact Q → Prop
  | move {d d'} : Move d d' → Grounding d d'
  | pendingUpdate {d d'} : PendingUpdate d d' → Grounding d d'
  | contextualInstantiation {d d'} : ContextualInstantiation d d' → Grounding d d'
  | pendified {d d'} : Pendified Move d d' → Grounding d d'
  | parameterIdentification {d d'} : ParameterIdentification d d' → Grounding d d'
  | parameterFocussing {d d'} : ParameterFocussing d d' → Grounding d d'
  | crAccommodation {d d'} : CRAccommodation d d' → Grounding d d'
  | repair {d d'} : Repair d d' → Grounding d d'

omit [DecidableEq Q] in
/-- A move a genre makes initiating is coherent (Ch. 4 M-Coherence; Appendix B Utterance
Coherence). -/
theorem coherent_of_isInitiating {G : Set (Board P Fact Q)} {d : Board P Fact Q}
    {u : Utterance Fact Q} (h : IsInitiating G d u) : Coherent Grounding d u :=
  ⟨d.recordMove u, .move (.freeSpeech (le_turnUnderspec _ _ ⟨h.1, u, rfl⟩)), rfl⟩

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

/-- After (65), in which A asks `q₀`, B asks `q₁`, A asserts `p₁`, B accepts, B asserts `p₂` and
A accepts: FACTS `{p₁, p₂}`, QUD `⟨q₀⟩`, the six moves recorded. -/
theorem trace : ∃ d, Relation.ReflTransGen Move (initial : Board Agent Fact Q) d ∧ table d =
    ({.p₁, .p₂}, [.q₀],
      [.accept .p₂, .assert .p₂, .accept .p₁, .assert .p₁, .ask .q₁, .ask .q₀]) :=
  ⟨_, .head (.freeSpeech (turnUnderspec_of ⟨rfl, ofMove (.ask .q₀), rfl⟩)) <|
    .head (.askQud ⟨_, rfl, rfl⟩) <|
    .head (.qspec (turnUnderspec_swapTurn_of ⟨_, rfl, ofMove (.ask .q₁), by decide, rfl⟩)) <|
    .head (.askQud ⟨_, rfl, rfl⟩) <|
    .head (.qspec (turnUnderspec_swapTurn_of ⟨_, rfl, ofMove (.assert .p₁), by decide, rfl⟩)) <|
    .head (.assertQud ⟨_, rfl, rfl⟩) <|
    .head (.accept ⟨.p₁, ofMove (.accept .p₁), rfl, rfl, rfl, rfl⟩) <|
    .head (.factUpdate ⟨.p₁, .inl rfl, rfl, rfl⟩) <|
    .head (.qspec (turnUnderspec_of ⟨_, rfl, ofMove (.assert .p₂), by decide, rfl⟩)) <|
    .head (.assertQud ⟨_, rfl, rfl⟩) <|
    .head (.accept ⟨.p₂, ofMove (.accept .p₂), rfl, rfl, rfl, rfl⟩) <|
    .head (.factUpdate ⟨.p₂, .inl rfl, rfl, rfl⟩) .refl, by decide⟩

-- (67)
theorem trace68 : ∃ d, Relation.ReflTransGen Move (initial : Board Agent Fact Q) d ∧ table d =
    ({.p₁}, [], [.confirm .p₁, .check .p₁, .assert .p₁]) :=
  ⟨_, .head (.freeSpeech (turnUnderspec_of ⟨rfl, ofMove (.assert .p₁), rfl⟩)) <|
    .head (.assertQud ⟨_, rfl, rfl⟩) <|
    .head (.check (turnUnderspec_of ⟨.p₁, ofMove (.check .p₁), rfl, rfl, rfl, rfl⟩)) <|
    .head (.confirm ⟨.p₁, ofMove (.confirm .p₁), rfl, rfl, rfl, rfl⟩) <|
    .head (.factUpdate ⟨.p₁, .inr rfl, rfl, rfl⟩) .refl, by decide⟩

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

/-- After (78), in which A asks `q₀` then `q₁` (QCoord), B answers `q₀`, A accepts and B answers
`q₁`: FACTS `{p₀}`, QUD `⟨p₁?, q₁⟩`. -/
theorem trace : ∃ d, Relation.ReflTransGen Move (initial : Board Agent Fact Q) d ∧ table d =
    ({.p₀}, [.polar .p₁, .q₁],
      [.assert .p₁, .accept .p₀, .assert .p₀, .ask .q₁, .ask .q₀]) :=
  ⟨_, .head (.freeSpeech (turnUnderspec_of ⟨rfl, ofMove (.ask .q₀), rfl⟩)) <|
    .head (.askQud ⟨_, rfl, rfl⟩) <|
    .head (.qcoord ⟨.q₀, .q₁, ofMove (.ask .q₁), _, _, rfl, rfl, rfl, rfl, by decide, rfl⟩) <|
    .head (.qspec (turnUnderspec_swapTurn_of ⟨_, rfl, ofMove (.assert .p₀), by decide, rfl⟩)) <|
    .head (.assertQud ⟨_, rfl, rfl⟩) <|
    .head (.accept ⟨.p₀, ofMove (.accept .p₀), rfl, rfl, rfl, rfl⟩) <|
    .head (.factUpdate ⟨.p₀, .inl rfl, rfl, rfl⟩) <|
    .head (.qspec (turnUnderspec_swapTurn_of ⟨_, rfl, ofMove (.assert .p₁), by decide, rfl⟩)) <|
    .head (.assertQud ⟨_, rfl, rfl⟩) .refl, by decide⟩

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

/-- CasualChat (88a) is the type of the gameboards that end a conversation in which the issues
`λP.P(A)` and `λP.P(B)` have been resolved, with nothing left under discussion. -/
def casualChat : Set (Board Agent Fact Q) :=
  {d | d.qud = [] ∧ ∀ q ∈ [Q.howA, .howB], ∃ f ∈ d.facts, Content.Resolves f q}

instance : DecidablePred (· ∈ casualChat) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem initiating_off :
    IsInitiating casualChat ((initial {.here}).recordMove (ofMove IllocutionaryAct.greet))
      (ofMove (.assert .off)) :=
  ⟨rfl, _, .head (.assertQud ⟨_, rfl, rfl⟩) <|
    .head (.accept ⟨.off, ofMove (.accept .off), rfl, rfl, rfl, rfl⟩) <|
    .head (.factUpdate ⟨.off, .inl rfl, rfl, rfl⟩) .refl, by decide⟩

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
  | meant (u : Constituent)
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
def george : Constituent := { form := "George", category := .np, denotation := .george }

/-- A's utterance, with the referent of "George" a contextual parameter. -/
def u₀ : Utterance Fact Q :=
  { form := "Is George here?", category := .s, content := .ask (.polar .georgeHere),
    parameters := {.george}, constituents := {george} }

/-- A's utterance with its parameter witnessed. -/
def w₀ : Utterance Fact Q := u₀.instantiate {.george}

/-- B's clarification request. -/
def u₁ : Utterance Fact Q := { form := "Is WHO here?", category := .s, content := .ask .whoAsked }

/-- (91b): A's gameboard, with `p?` under discussion and B's clarification request pending. -/
def dgbA : Board Agent Fact Q :=
  { speaker := .B, addressee := .A, pending := [u₁], qud := [⟨.polar .georgeHere, ∅⟩],
    moves := [w₀] }

/-- (91c): B's gameboard, with who A is asking about under discussion and A's utterance
pending. -/
def dgbB : Board Agent Fact Q :=
  { speaker := .B, addressee := .A, pending := [u₀], qud := [⟨.whoAsked, {george}⟩],
    moves := [u₁] }

theorem reflTransGen_dgbA : Relation.ReflTransGen Grounding initial dgbA :=
  .head (.pendingUpdate ⟨u₀, .A, .B, rfl⟩) <|
    .head (.contextualInstantiation ⟨u₀, [], w₀, rfl, ⟨{.george}, rfl⟩, rfl⟩) <|
    .head (.pendified ⟨w₀, [], rfl, by decide,
      .freeSpeech (turnUnderspec_of ⟨rfl, w₀, rfl⟩), rfl⟩) <|
    .head (.move (.askQud ⟨_, rfl, rfl⟩)) <|
    .head (.pendingUpdate ⟨u₁, .B, .A, rfl⟩) .refl

theorem reflTransGen_dgbB : Relation.ReflTransGen Grounding initial dgbB :=
  .head (.pendingUpdate ⟨u₀, .A, .B, rfl⟩) <|
    .head (.parameterFocussing
      ⟨_, ⟨george, u₀, rfl, Finset.mem_singleton_self _, u₁, rfl, rfl⟩, rfl⟩) .refl

theorem differ : dgbA.qud ≠ dgbB.qud ∧ dgbA.pending ≠ dgbB.pending := by
  decide

theorem accommodate : ∃ d, CRAccommodation dgbA d ∧
    (d.qud.map (·.question), d.pending) = ([.whoAsked, .polar .georgeHere], []) :=
  ⟨_, ⟨george, u₁, [], w₀, .whoAsked, rfl, rfl, Finset.mem_singleton_self _, rfl, .inr rfl, rfl⟩,
    by decide⟩

end George

/-! ### Who holds the turn (Chs. 1 and 8)

Only the addressee has the two clarification-request readings of "Bo?" and only the original
speaker its self-correction reading (ex. 22); bare "Why?" is resolved differently by whoever holds
the turn, the Turn-Taking Puzzle (ex. 23); and mid-utterance self-repair is the within-utterance
analogue of a clarification request (ex. 24). Each turns on the turn a rule leaves, a general
property of the inventory. -/

section Turn

variable {P Fact Q : Type} [Content Fact Q] [Clarifiable P Fact Q] {d d' : Board P Fact Q}

omit [Clarifiable P Fact Q] in
theorem qSpec_swapTurn_iff : QSpec d d'.swapTurn ↔ QSpec d d' :=
  turnUnderspec_swapTurn_iff

theorem Repair.speaker (h : Repair d d') : d'.speaker = d.speaker :=
  let ⟨_, h⟩ := h
  h.speaker

theorem ParameterIdentification.speaker (h : ParameterIdentification d d') :
    d'.speaker = d.addressee := by
  obtain ⟨e, ⟨_, he⟩, rfl⟩ := h
  exact he.addressee

theorem ParameterFocussing.speaker (h : ParameterFocussing d d') : d'.speaker = d.addressee := by
  obtain ⟨e, ⟨_, he⟩, rfl⟩ := h
  exact he.addressee

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
  | meant (u : Constituent)
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
def bo : Constituent := { form := "Bo", category := .np, denotation := .bo }

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

/-- A row: its construction and who holds the turn after it, A being the original speaker. -/
structure Row where
  construction : Construction
  next : Agent
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row :=
  (ex.parse? (α := Row) "speaker" [("addressee", ⟨.clarification, .B⟩),
      ("original speaker", ⟨.selfRepair, .A⟩)]).orElse fun _ ↦
    (ex.parse? "repair" [("other-initiated", ⟨.clarification, .B⟩),
        ("self-initiated", ⟨.selfRepair, .A⟩)]).orElse fun _ ↦
      ex.parse? "turn" [("kept", ⟨.followUp, .A⟩), ("taken", ⟨.followUp, .B⟩)]

/-- The gameboard the row's second utterance meets: A's question pending, for a clarification
request or a repair addressing its constituent "Bo", or under discussion, for a follow-up. -/
def Row.board (r : Row) : Board Agent Fact Q :=
  match r.construction with
  | .clarification | .selfRepair => initial.pushPending u₀
  | .followUp => (initial.recordMove (ofMove (.ask .q₀))).pushQud ⟨.q₀, ∅⟩

/-- The seven rows of exx. 22–24. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_turn : ∀ r ∈ rows,
    match r.construction with
    | .clarification => Coherent ParameterIdentification r.board (ofMove (.ask (.meant bo))) ∧
        ∀ d', ParameterIdentification r.board d' → d'.speaker = r.next
    | .selfRepair => Coherent Repair r.board (ofMove (.ask (.meant bo))) ∧
        ∀ d', Repair r.board d' → d'.speaker = r.next
    | .followUp => ∃ d', QSpec r.board d' ∧ d'.latestMove = some (ofMove (.ask .why)) ∧
        d'.speaker = r.next := by
  intro r hr
  have key := (by decide : ∀ r ∈ rows, (r.construction = .clarification → r.next = .B) ∧
    (r.construction = .selfRepair → r.next = .A)) r hr
  obtain ⟨c, n⟩ := r
  cases c
  · obtain rfl : n = .B := key.1 rfl
    exact ⟨⟨_, ⟨_, ⟨bo, u₀, rfl, Finset.mem_singleton_self _, ofMove (.ask (.meant bo)),
      rfl, rfl⟩, rfl⟩, rfl⟩, fun _ h ↦ h.speaker⟩
  · obtain rfl : n = .A := key.2 rfl
    exact ⟨⟨_, ⟨bo, u₀, rfl, Finset.mem_singleton_self _, ofMove (.ask (.meant bo)),
      rfl, rfl⟩, rfl⟩, fun _ h ↦ h.speaker⟩
  · cases n
    · exact ⟨_, turnUnderspec_of ⟨_, rfl, ofMove (.ask .why), by decide, rfl⟩, rfl, rfl⟩
    · exact ⟨_, turnUnderspec_swapTurn_of ⟨_, rfl, ofMove (.ask .why), by decide, rfl⟩, rfl, rfl⟩

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
