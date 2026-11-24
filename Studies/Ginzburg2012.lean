module

public import Linglib.Discourse.Gameboard.Rule
public import Linglib.Discourse.Gameboard.Question
public import Linglib.Semantics.Questions.Inquisitive.Declarative
public import Linglib.Data.Examples.Ginzburg2012
public import Linglib.Data.Examples.Readers

/-!
# Ginzburg (2012): The Interactive Stance

This file formalizes the conversational rules of [ginzburg-2012] over the dialogue gameboard
`Gameboard`: each participant's turn holder and addressee, the commonly accepted FACTS, the MOVES
made, the questions under discussion and, once metacommunication enters, the ungrounded utterances
PENDING. The rules form a labelled relation between gameboards: a step integrates a move, or is
the participant's own bookkeeping. The move rules of Ch. 4 are one such relation and the rules
of grounding and clarification a second that includes it, and a conversation develops along the
reflexive transitive closure of the steps.

A move a genre makes initiating is coherent. Each clarification rule is a question merged with
Utterance Interpolation, so it makes the clarified constituent of the maximal pending utterance
the focus-establishing constituent of MaxQUD. Parameter Identification and self-repair
accommodate the same question, the first as a reply and the second as a continuation.

For propositions that are sets of worlds, a potentially resolving answer to a question is a
proposition that resolves the polar closure of the issue the question raises, and every
proposition is about every question that has a value: a proposition entails the disjunction of a
simple answer and its negation. The book's entailment is that of situation semantics, on which
this fails, so the traces take aboutness, influence and resolution as given.

The worked traces of Ch. 4 reach the tabulated gameboards, and after "Is George here? / Is WHO
here?" the two participants' gameboards differ in QUD and PENDING although both processed the
same utterances. QSPEC puts no condition on who
speaks; the rows of Chs. 1 and 8 record who holds the turn after a clarification request, a
self-repair and a bare follow-up question.

## Implementation notes

* The move rules follow Ch. 4, where Accept requires `p?` to be MaxQUD; the version of Appendix B
  drops that precondition and updates the contextual parameters of the assertion. Initiating
  Move is stated without its effect on QUD: in the book the issue the move is relevant to
  becomes MaxQUD and the move is co-propositional with it.
* The trace of the dialogue in which an assertion is checked and confirmed ends with QUD empty,
  the result of Fact update on `⟨p₁?⟩`.
* CR Accommodation removes the clarification request from PENDING when it makes it LatestMove.
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

/-- The other participant. -/
def Agent.other : Agent → Agent
  | .A => .B
  | .B => .A

/-! ### Answerhood over sets of worlds (§3.3.7)

A question is a propositional abstract, a partial function `q : R →. Set W` from records to
propositions. -/

section Answerhood

variable {R W : Type*} {p : Set W} {q : R →. Set W}

/-- (45): a simple answer to `q` is an instantiation of `q` or the negation of one. -/
def SimpleAnswer (q : R →. Set W) (p : Set W) : Prop :=
  ∃ a ∈ q.ran, p = a ∨ p = aᶜ

/-- `p` is about `q` when it entails a disjunction of simple answers to `q`. -/
def About (p : Set W) (q : R →. Set W) : Prop :=
  ∃ p₁ p₂, SimpleAnswer q p₁ ∧ SimpleAnswer q p₂ ∧ p ⊆ p₁ ∪ p₂

/-- A potentially resolving answer to `q` entails an instantiation of `q` or the negation of
every instantiation. -/
def PotentiallyResolves (p : Set W) (q : R →. Set W) : Prop :=
  (∃ a ∈ q.ran, p ⊆ a) ∨ ∀ a ∈ q.ran, p ⊆ aᶜ

/-- Over sets of worlds, every proposition is about every question that has a value. -/
theorem about_iff : About p q ↔ q.ran.Nonempty :=
  ⟨fun ⟨_, _, ⟨a, ha, _⟩, _⟩ ↦ ⟨a, ha⟩, fun ⟨a, ha⟩ ↦
    ⟨a, aᶜ, ⟨a, ha, .inl rfl⟩, ⟨a, ha, .inr rfl⟩, by simp⟩⟩

/-- A potentially resolving answer to `q` is a proposition that resolves the polar closure of
the issue `q` raises. -/
theorem potentiallyResolves_iff_mem_query :
    PotentiallyResolves p q ↔ p ∈ (Gameboard.issue q).query := by
  simp only [PotentiallyResolves, Gameboard.issue, Question.mem_query, Question.mem_generate,
    Question.info_generate, Set.subset_compl_comm (s := p), Set.sUnion_subset_iff]
  constructor
  · rintro (h | h)
    · exact .inl (.inr h)
    · exact .inr h
  · rintro ((rfl | h) | h)
    · exact .inr fun a _ ↦ by simp
    · exact .inl h
    · exact .inr h

end Answerhood

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

/-- `a` addresses to `b` an utterance of which only the content `c` matters. -/
def tells (a b : P) (c : IllocutionaryAct Fact Q) : Move P (Utterance Fact Q) :=
  ⟨a, b, ofMove c⟩

omit [DecidableEq Fact] [DecidableEq Q] in
/-- A clarification rule pairing its question with the clarified constituent makes that
constituent, a constituent of MaxPending, the focus-establishing constituent of MaxQUD. -/
theorem focusEstablishing_clarification {q : Utterance Fact Q → Q} {u : Constituent}
    {d d' : Board P Fact Q} {m : Move P (Utterance Fact Q)}
    (h : Clarification Copropositional u (fun v ↦ ⟨q v, {u}⟩) d m d') :
    (∃ v ∈ d.maxPending, u ∈ v.constituents) ∧
      d'.qud.head?.map (·.focusEstablishing) = some {u} := by
  obtain ⟨v, hv, hu, h⟩ := h.qud
  exact ⟨⟨v, hv, hu⟩, by simp [h]⟩

/-! ### Move rules (Ch. 4)

A step labelled `some m` integrates the move `m` as LatestMove, and a step labelled `none` is
bookkeeping. Accept and Confirm are replies; Greeting, Free Speech, QSPEC and checking put no
condition on who speaks. -/

/-- The move rules of [ginzburg-2012] Ch. 4, as Appendix B lists them. -/
inductive Step : Board P Fact Q → Option (Move P (Utterance Fact Q)) → Board P Fact Q → Prop
  /-- Greeting opens a conversation with no moves made and nothing under discussion. -/
  | greeting {d : Board P Fact Q} (m : Move P (Utterance Fact Q)) :
      d.moves = [] → d.qud = [] → m.utterance.content = .greet → d.IsContinuation m →
      Step d (some m) (d.say m)
  /-- Counter-greeting answers a greeting. -/
  | counterGreeting {d : Board P Fact Q} (m : Move P (Utterance Fact Q)) :
      d.latestContent = some .greet → d.qud = [] → m.utterance.content = .counterGreet →
      d.IsReply m → Step d (some m) (d.say m)
  /-- Free Speech: with nothing under discussion, any move may be made. -/
  | freeSpeech {d : Board P Fact Q} (m : Move P (Utterance Fact Q)) :
      d.qud = [] → Step d (some m) (d.say m)
  /-- QSPEC: a move specific to MaxQUD may be made. -/
  | qspec {d : Board P Fact Q} {i : InformationStructure Q Constituent}
      (m : Move P (Utterance Fact Q)) :
      d.qud.head? = some i → QSpecific m.utterance.content i.question →
      Step d (some m) (d.say m)
  /-- Ask QUD-incrementation: the question asked becomes MaxQUD. -/
  | askQud {d : Board P Fact Q} {q : Q} :
      d.latestContent = some (.ask q) → Step d none (d.pushQud ⟨q, ∅⟩)
  /-- Assert QUD-incrementation: `p?` becomes MaxQUD once `p` is asserted. -/
  | assertQud {d : Board P Fact Q} {p : Fact} :
      d.latestContent = some (.assert p) → Step d none (d.pushQud ⟨Content.polar p, ∅⟩)
  /-- Assertion checking: once `p` is asserted and `p?` is MaxQUD, either participant may ask
  for confirmation of `p`. -/
  | check {d : Board P Fact Q} {p : Fact} (m : Move P (Utterance Fact Q)) :
      d.latestContent = some (.assert p) → m.utterance.content = .check p →
      d.maxQud = some (Content.polar p) → Step d (some m) (d.say m)
  /-- Accept: the addressee accepts the assertion of `p` while `p?` is MaxQUD. -/
  | accept {d : Board P Fact Q} {p : Fact} (m : Move P (Utterance Fact Q)) :
      d.latestContent = some (.assert p) → m.utterance.content = .accept p →
      d.maxQud = some (Content.polar p) → d.IsReply m → Step d (some m) (d.say m)
  /-- Confirm: the addressee confirms the checked `p` while `p?` is MaxQUD. -/
  | confirm {d : Board P Fact Q} {p : Fact} (m : Move P (Utterance Fact Q)) :
      d.latestContent = some (.check p) → m.utterance.content = .confirm p →
      d.maxQud = some (Content.polar p) → d.IsReply m → Step d (some m) (d.say m)
  /-- Fact update/QUD-downdate: an accepted or confirmed `p` joins FACTS, and the questions the
  facts now resolve leave QUD. -/
  | factUpdate {d : Board P Fact Q} {p : Fact} :
      d.latestContent = some (.accept p) ∨ d.latestContent = some (.confirm p) →
      d.maxQud = some (Content.polar p) →
      Step d none ((d.addFact p).downdateQud Content.Resolves)
  /-- QCoord: the asker of `q` follows it with a question `q₁` that does not influence `q`,
  which joins QUD below it. -/
  | qcoord {d : Board P Fact Q} {q q₁ : Q} {i : InformationStructure Q Constituent}
      {rest : List (InformationStructure Q Constituent)} (m : Move P (Utterance Fact Q)) :
      d.latestContent = some (.ask q) → m.utterance.content = .ask q₁ → d.qud = i :: rest →
      i.question = q → ¬Content.Influences (Fact := Fact) q₁ q → d.IsContinuation m →
      Step d (some m) { d.say m with qud := i :: ⟨q₁, ∅⟩ :: rest }

omit [DecidableEq Q] in
theorem factUpdate_polar (d : Board P Fact Q) (p : Fact) :
    ∀ i ∈ ((d.addFact p).downdateQud Content.Resolves).qud, i.question ≠ Content.polar p :=
  fun i hi hq ↦ Gameboard.nonResolveCond_downdateQud _ _ i hi
    ⟨p, Finset.mem_insert_self _ _, hq ▸ Content.resolves_polar p⟩

/-! ### Conversational genres (§4.6)

A genre is a type of the gameboards that end conversations of that kind (ex. 88
pp. 104–105), here a set of gameboards; the three genres of (88) differ only in the issues
they require among the questions no longer under discussion. A move is relevant to a genre
when some development of the gameboard after it is of that type, `outcome(dgb, G)` fulfilled
(exx. 89–90 p. 105). Initiating Move (ex. 94 p. 108) is Free Speech restricted to moves the
speaker takes to be relevant to the genre, which the private part of their information state
records (ex. 93 p. 107); here the genre is an argument. -/

/-- `m` is relevant to `G` in `d` when some development of `d` extended by `m` is of type `G`. -/
def GenreRelevant (G : Set (Board P Fact Q)) (d : Board P Fact Q)
    (m : Move P (Utterance Fact Q)) : Prop :=
  ∃ d', Relation.ReflTransGen (fun d d' ↦ ∃ l, Step d l d') (d.say m) d' ∧ d' ∈ G

/-- Initiating Move: with QUD empty, a move relevant to the assumed genre. -/
def IsInitiating (G : Set (Board P Fact Q)) (d : Board P Fact Q)
    (m : Move P (Utterance Fact Q)) : Prop :=
  d.qud = [] ∧ GenreRelevant G d m

/-! ### Grounding and clarification (Ch. 6, §8.2)

A Clarification Context Update Rule fixes the question it accommodates and who makes the move,
and is merged with Utterance Interpolation ((71) p. 192). In the final versions of the rules
(Appendix B (26e) p. 374, and (31) p. 287 for repair), MaxQUD is paired with the clarified
sub-utterance, a constituent of the maximal pending utterance, as its focus-establishing
constituent, which a reprise fragment must then match in category (p. 254). Backwards-looking
appropriateness repair ((31) p. 287) is Parameter Identification ((70) p. 192) made by the
speaker: the speaker of a pending utterance accommodates the issue of what they meant by one of
its constituents and continues co-propositionally with it. -/

variable [Clarifiable P Fact Q]

/-- Backwards-looking appropriateness repair: the speaker continues, saying what they meant by
a constituent `u` of MaxPending. -/
def Repair (d : Board P Fact Q) (m : Move P (Utterance Fact Q)) (d' : Board P Fact Q) : Prop :=
  d.IsContinuation m ∧ ∃ u, Clarification Copropositional u
    (fun _ ↦ ⟨Clarifiable.mean (Fact := Fact) d.speaker u, {u}⟩) d m d'

/-- Parameter Identification: the addressee replies, asking what the speaker meant by a
constituent `u` of MaxPending. -/
def ParameterIdentification (d : Board P Fact Q) (m : Move P (Utterance Fact Q))
    (d' : Board P Fact Q) : Prop :=
  d.IsReply m ∧ ∃ u, Clarification Copropositional u
    (fun _ ↦ ⟨Clarifiable.mean (Fact := Fact) d.speaker u, {u}⟩) d m d'

/-- Parameter Focussing: the addressee replies, asking the content of MaxPending with the
parameter of its constituent `u` abstracted. -/
def ParameterFocussing (d : Board P Fact Q) (m : Move P (Utterance Fact Q))
    (d' : Board P Fact Q) : Prop :=
  d.IsReply m ∧ ∃ u, Clarification Copropositional u
    (fun v ↦ ⟨Clarifiable.focus (P := P) v.content u, {u}⟩) d m d'

/-- The rules of grounding and clarification, which include the move rules. -/
inductive GroundingStep :
    Board P Fact Q → Option (Move P (Utterance Fact Q)) → Board P Fact Q → Prop
  | step {d d' : Board P Fact Q} {l : Option (Move P (Utterance Fact Q))} :
      Step d l d' → GroundingStep d l d'
  /-- Pending Update: an utterance becomes MaxPending. -/
  | pendingUpdate {d : Board P Fact Q} (m : Move P (Utterance Fact Q)) :
      GroundingStep d none (d.pendingUpdate m.utterance m.speaker m.addressee)
  /-- Contextual Instantiation witnesses the parameters `s` of MaxPending, as an agent does who
  believes their witnesses are the ones the speaker intended. -/
  | contextualInstantiation {d : Board P Fact Q} {v : Utterance Fact Q}
      {rest : List (Utterance Fact Q)} (s : Finset Parameter) :
      d.pending = v :: rest → GroundingStep d none { d with pending := v.instantiate s :: rest }
  /-- Pendification of the move rules: the move they integrate is MaxPending, with no
  contextual parameter left to witness. -/
  | pendified {d d' : Board P Fact Q} {u : Utterance Fact Q} {rest : List (Utterance Fact Q)} :
      d.pending = u :: rest → u.parameters = ∅ →
      Step { d with pending := rest } (some ⟨d.speaker, d.addressee, u⟩) d' →
      GroundingStep d (some ⟨d.speaker, d.addressee, u⟩) d'
  | repair {d d' : Board P Fact Q} {m : Move P (Utterance Fact Q)} :
      Repair d m d' → GroundingStep d (some m) d'
  | parameterIdentification {d d' : Board P Fact Q} {m : Move P (Utterance Fact Q)} :
      ParameterIdentification d m d' → GroundingStep d (some m) d'
  | parameterFocussing {d d' : Board P Fact Q} {m : Move P (Utterance Fact Q)} :
      ParameterFocussing d m d' → GroundingStep d (some m) d'
  /-- CR Accommodation integrates the other party's clarification request, MaxPending, so the
  clarified speaker is the current addressee. -/
  | crAccommodation {d : Board P Fact Q} {u : Constituent} {v v₀ : Utterance Fact Q}
      {rest : List (Utterance Fact Q)} {q : Q} :
      d.pending = v :: rest → d.latestMove = some v₀ → u ∈ v₀.constituents →
      qudContrib v.content = some q →
      q = Clarifiable.mean (Fact := Fact) d.addressee u ∨
        q = Clarifiable.focus (P := P) v₀.content u →
      GroundingStep d (some ⟨d.speaker, d.addressee, v⟩)
        { (d.pushQud ⟨q, {u}⟩).recordMove v with pending := rest }

omit [DecidableEq Q] in
/-- A move a genre makes initiating is coherent (Ch. 4 M-Coherence; Appendix B Utterance
Coherence). -/
theorem coherent_of_isInitiating {G : Set (Board P Fact Q)} {d : Board P Fact Q}
    {m : Move P (Utterance Fact Q)} (h : IsInitiating G d m) :
    ∃ d', GroundingStep d (some m) d' :=
  ⟨_, .step (.freeSpeech m h.1)⟩

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

-- (65)
theorem trace : ∃ d,
    Relation.ReflTransGen (fun d d' ↦ ∃ l, Step d l d') (initial : Board Agent Fact Q) d ∧
    table d = ({.p₁, .p₂}, [.q₀],
      [.accept .p₂, .assert .p₂, .accept .p₁, .assert .p₁, .ask .q₁, .ask .q₀]) :=
  ⟨_, .head ⟨_, .freeSpeech (tells .A .B (.ask .q₀)) rfl⟩ <| .head ⟨_, .askQud rfl⟩ <|
    .head ⟨_, .qspec (tells .B .A (.ask .q₁)) rfl (by decide)⟩ <| .head ⟨_, .askQud rfl⟩ <|
    .head ⟨_, .qspec (tells .A .B (.assert .p₁)) rfl (by decide)⟩ <|
    .head ⟨_, .assertQud rfl⟩ <|
    .head ⟨_, .accept (tells .B .A (.accept .p₁)) rfl rfl rfl ⟨rfl, rfl⟩⟩ <|
    .head ⟨_, .factUpdate (.inl rfl) rfl⟩ <|
    .head ⟨_, .qspec (tells .B .A (.assert .p₂)) rfl (by decide)⟩ <|
    .head ⟨_, .assertQud rfl⟩ <|
    .head ⟨_, .accept (tells .A .B (.accept .p₂)) rfl rfl rfl ⟨rfl, rfl⟩⟩ <|
    .head ⟨_, .factUpdate (.inl rfl) rfl⟩ .refl, by decide⟩

-- (67)-(68)
theorem trace68 : ∃ d,
    Relation.ReflTransGen (fun d d' ↦ ∃ l, Step d l d') (initial : Board Agent Fact Q) d ∧
    table d = ({.p₁}, [], [.confirm .p₁, .check .p₁, .assert .p₁]) :=
  ⟨_, .head ⟨_, .freeSpeech (tells .A .B (.assert .p₁)) rfl⟩ <| .head ⟨_, .assertQud rfl⟩ <|
    .head ⟨_, .check (tells .A .B (.check .p₁)) rfl rfl rfl⟩ <|
    .head ⟨_, .confirm (tells .B .A (.confirm .p₁)) rfl rfl rfl ⟨rfl, rfl⟩⟩ <|
    .head ⟨_, .factUpdate (.inr rfl) rfl⟩ .refl, by decide⟩

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

-- (78)
theorem trace : ∃ d,
    Relation.ReflTransGen (fun d d' ↦ ∃ l, Step d l d') (initial : Board Agent Fact Q) d ∧
    table d = ({.p₀}, [.polar .p₁, .q₁],
      [.assert .p₁, .accept .p₀, .assert .p₀, .ask .q₁, .ask .q₀]) :=
  ⟨_, .head ⟨_, .freeSpeech (tells .A .B (.ask .q₀)) rfl⟩ <| .head ⟨_, .askQud rfl⟩ <|
    .head ⟨_, .qcoord (tells .A .B (.ask .q₁)) rfl rfl rfl rfl (by decide) ⟨rfl, rfl⟩⟩ <|
    .head ⟨_, .qspec (tells .B .A (.assert .p₀)) rfl (by decide)⟩ <|
    .head ⟨_, .assertQud rfl⟩ <|
    .head ⟨_, .accept (tells .A .B (.accept .p₀)) rfl rfl rfl ⟨rfl, rfl⟩⟩ <|
    .head ⟨_, .factUpdate (.inl rfl) rfl⟩ <|
    .head ⟨_, .qspec (tells .B .A (.assert .p₁)) rfl (by decide)⟩ <|
    .head ⟨_, .assertQud rfl⟩ .refl, by decide⟩

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
      (tells .B .A (.assert .off)) :=
  ⟨rfl, _, .head ⟨_, .assertQud rfl⟩ <|
    .head ⟨_, .accept (tells .A .B (.accept .off)) rfl rfl rfl ⟨rfl, rfl⟩⟩ <|
    .head ⟨_, .factUpdate (.inl rfl) rfl⟩ .refl, by decide⟩

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

-- A utters `u₀`, instantiates it, integrates it by Free Speech and hears `u₁`
theorem reflTransGen_dgbA :
    Relation.ReflTransGen (fun d d' ↦ ∃ l, GroundingStep d l d') initial dgbA :=
  .head ⟨_, .pendingUpdate ⟨.A, .B, u₀⟩⟩ <|
    .head ⟨_, .contextualInstantiation {.george} rfl⟩ <|
    .head ⟨_, .pendified rfl (by decide) (.freeSpeech _ rfl)⟩ <|
    .head ⟨_, .step (.askQud rfl)⟩ <| .head ⟨_, .pendingUpdate ⟨.B, .A, u₁⟩⟩ .refl

-- B hears `u₀` and clarifies by Parameter Focussing with `u₁`
theorem reflTransGen_dgbB :
    Relation.ReflTransGen (fun d d' ↦ ∃ l, GroundingStep d l d') initial dgbB :=
  .head ⟨_, .pendingUpdate ⟨.A, .B, u₀⟩⟩ <| .head ⟨_, .parameterFocussing (m := ⟨.B, .A, u₁⟩)
    ⟨⟨rfl, rfl⟩, george, u₀, rfl, Finset.mem_singleton_self _, rfl, rfl⟩⟩ .refl

theorem differ : dgbA.qud ≠ dgbB.qud ∧ dgbA.pending ≠ dgbB.pending := by
  decide

theorem accommodate : ∃ d, GroundingStep dgbA (some ⟨.B, .A, u₁⟩) d ∧
    (d.qud.map (·.question), d.pending) = ([.whoAsked, .polar .georgeHere], []) :=
  ⟨_, .crAccommodation (u := george) rfl rfl (Finset.mem_singleton_self _) rfl (.inr rfl),
    by decide⟩

end George

/-! ### Who holds the turn (Chs. 1 and 8)

Only the addressee has the two clarification-request readings of "Bo?" and only the original
speaker its self-correction reading (ex. 22); bare "Why?" is resolved differently by whoever holds
the turn, the Turn-Taking Puzzle (ex. 23); and mid-utterance self-repair is the within-utterance
analogue of a clarification request (ex. 24). Each turns on who may make the move a rule
integrates. -/

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
    | .clarification =>
        (∃ d', ParameterIdentification r.board (tells r.next r.next.other (.ask (.meant bo))) d') ∧
          ∀ m d', ParameterIdentification r.board m d' → m.speaker = r.next
    | .selfRepair =>
        (∃ d', Repair r.board (tells r.next r.next.other (.ask (.meant bo))) d') ∧
          ∀ m d', Repair r.board m d' → m.speaker = r.next
    | .followUp => ∃ d', Step r.board (some (tells r.next r.next.other (.ask .why))) d' := by
  intro r hr
  have key := (by decide : ∀ r ∈ rows, (r.construction = .clarification → r.next = .B) ∧
    (r.construction = .selfRepair → r.next = .A)) r hr
  obtain ⟨c, n⟩ := r
  cases c
  · obtain rfl : n = .B := key.1 rfl
    exact ⟨⟨_, ⟨rfl, rfl⟩, bo, u₀, rfl, Finset.mem_singleton_self _, rfl, rfl⟩,
      fun _ _ ⟨⟨h, _⟩, _⟩ ↦ h⟩
  · obtain rfl : n = .A := key.2 rfl
    exact ⟨⟨_, ⟨rfl, rfl⟩, bo, u₀, rfl, Finset.mem_singleton_self _, rfl, rfl⟩,
      fun _ _ ⟨⟨h, _⟩, _⟩ ↦ h⟩
  · cases n
    · exact ⟨_, .qspec _ rfl (by decide)⟩
    · exact ⟨_, .qspec _ rfl (by decide)⟩

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
