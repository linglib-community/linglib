module

public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Sidner1979
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Sidner (1979): Towards a Computational Theory of Definite Anaphora Comprehension

This file formalizes the focusing theory of [sidner-1979], reprinted in part as [sidner-1983].
The expected focus algorithm predicts a first sentence's discourse focus: the subject of an is-a
or there-insertion sentence, otherwise [the first phrase of the default
ordering](##Sentence.expectedFocus_le), the theme first and the agent last. A later sentence's
anaphora confirm the focus, move it to a co-specified alternate, or [pop the focus
stack](##D31.popped); the actor focus follows the agent. A pronoun prefers the discourse focus
outside agent position and the actor focus in it, unless [an earlier-established discourse focus
takes precedence](##State.cospecify_agent_of_precedence): [every *he* of D9 co-specifies
Jeff](##D9.he_jeff), and [the focus of D35 moves](##D35.movement) to the ice cream cones.

## Implementation notes

* A sentence is its form, which names the subject of an is-a or there-insertion sentence, and
  its phrases in surface order, each with the entity it specifies (for a pronoun its
  co-specification), its thematic relation at the granularity of the default expected focus
  list, whether it is a pronoun, and whether it is animate; the verb phrase, which the examples
  omit, is a phrase with the relation `verbPhrase`.
* The pipeline processes interpreted sentences: the focusing algorithm consults the
  co-specifications of the anaphora, those in agent position only when no others occur, and the
  pronoun rules order the candidates from which a predicate standing for the syntactic anaphoric
  filters and the inference mechanism selects the first.
* Only pronominal anaphora are modelled, so the steps of the focusing algorithm on do-anaphora,
  focus sets, implicit specification and nominalization are omitted, and the clause of step 3 on
  a definite noun phrase mentioning the focus is vacuous. Possessives, plural pronouns and the
  potential actor ambiguity condition are outside the model.

## References

* [sidner-1979]
* [sidner-1983]
-/

@[expose] public section

namespace Sidner1979

/-- The thematic relation of a phrase to its verb at the granularity of the default expected
focus list: the theme, any other position, the agent, and the verb phrase itself. -/
inductive Thematic
  | theme | other | agent | verbPhrase
  deriving DecidableEq, Fintype

/-- The preference of the default expected focus list: the theme first, then the other
thematic positions with the agent last, then the verb phrase. -/
def Thematic.rank : Thematic → ℕ
  | .theme => 0
  | .other => 1
  | .agent => 2
  | .verbPhrase => 3

instance : LinearOrder Thematic := LinearOrder.lift' Thematic.rank (by decide)

/-- The form of a sentence as far as the expected focus algorithm consults it: an is-a or
there-insertion sentence with its subject, or a plain sentence. -/
inductive Form (E : Type*)
  | isA (subject : E) | thereInsertion (subject : E) | plain
  deriving DecidableEq

/-- A phrase of an interpreted sentence: the entity it specifies, for a pronoun its
co-specification, its thematic relation, whether it is a pronoun, and whether it is animate. -/
structure Phrase (E : Type*) where
  entity : E
  thematic : Thematic
  pronoun : Bool
  animate : Bool
  deriving DecidableEq

/-- A sentence is its form and its phrases in surface order. -/
structure Sentence (E : Type*) where
  form : Form E
  phrases : List (Phrase E)
  deriving DecidableEq

variable {E : Type*}

namespace Phrase

/-- `p.Precedes q` when the default expected focus list orders `p` no later than `q`. -/
def Precedes (p q : Phrase E) : Prop := p.thematic ≤ q.thematic

instance : DecidableRel (Precedes (E := E)) :=
  fun p q => inferInstanceAs (Decidable (p.thematic ≤ q.thematic))

instance : Std.Total (Precedes (E := E)) := ⟨fun p q => le_total p.thematic q.thematic⟩

instance : IsTrans (Phrase E) Precedes := ⟨fun _ _ _ => le_trans⟩

end Phrase

namespace Sentence

variable (s : Sentence E)

/-- The default expected focus list: the phrases in the order of `Phrase.Precedes`, surface
order breaking ties. -/
def defList : List (Phrase E) := s.phrases.insertionSort Phrase.Precedes

/-- The expected focus algorithm: the subject of an is-a or there-insertion sentence and
otherwise the first member of the default expected focus list. -/
def expectedFocus : Option E :=
  match s.form with
  | .plain => s.defList.head?.map (·.entity)
  | .isA e | .thereInsertion e => some e

/-- The agent of the sentence, the phrase in agent position. -/
def agent : Option E := (s.phrases.find? fun p => decide (p.thematic = .agent)).map (·.entity)

/-- The potential actors: the animate phrases outside agent position. -/
def potentialActors : List E :=
  (s.phrases.filter fun p => p.animate && decide (p.thematic ≠ .agent)).map (·.entity)

/-- The potential focus list given the focus: the phrases outside agent position not
co-specifying the focus, in the order of the default expected focus list. -/
def potentialFoci [DecidableEq E] (focus : Option E) : List E :=
  (s.defList.filter fun p => decide (p.thematic ≠ .agent ∧ some p.entity ≠ focus)).map (·.entity)

/-- The anaphora the focusing algorithm consults: the pronouns outside agent position, or all
the pronouns when none is outside agent position. -/
def anaphora : List E :=
  let nonAgent := s.phrases.filter fun p => p.pronoun && decide (p.thematic ≠ .agent)
  ((if nonAgent.isEmpty then s.phrases.filter (·.pronoun) else nonAgent).map (·.entity))

/-- The expected focus of a plain sentence is a phrase no later in the default expected focus
ordering than any other phrase of the sentence. -/
theorem expectedFocus_le {e : E} (hs : s.form = .plain) (h : s.expectedFocus = some e) :
    ∃ p ∈ s.phrases, p.entity = e ∧ ∀ q ∈ s.phrases, p.thematic ≤ q.thematic := by
  simp only [expectedFocus, hs] at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨l, hl⟩ := List.head?_eq_some_iff.1 hp
  have hsort := List.pairwise_insertionSort Phrase.Precedes s.phrases
  rw [← defList, hl, List.pairwise_cons] at hsort
  refine ⟨p, (List.mem_insertionSort _).1 (by rw [← defList, hl]; exact List.mem_cons_self), rfl,
    fun q hq => ?_⟩
  have hq' : q ∈ p :: l := by rw [← hl]; exact (List.mem_insertionSort _).2 hq
  rcases List.mem_cons.1 hq' with h | hq'
  · exact h ▸ le_rfl
  · exact hsort.1 q hq'

end Sentence

/-- A focus with the sentence that established it. -/
structure Focus (E : Type*) where
  entity : E
  since : ℕ
  deriving DecidableEq

/-- The state of the focusing mechanism: the discourse focus and the actor focus, the alternate
focus list (the rest of the default expected focus list after the first sentence and the
potential focus list afterwards), the potential actors, the last constituent of the previous
sentence for the recency rule, and the stacks of rejected discourse and actor foci. -/
structure State (E : Type*) where
  time : ℕ
  discourse : Option (Focus E)
  actor : Option (Focus E)
  alternates : List E
  potentialActors : List E
  last : Option E
  stack : List E
  actorStack : List E
  deriving DecidableEq

/-- The position of a pronoun as the rules for its co-specification consult it: agent
position, a subject outside agent position, or another position. -/
inductive Position
  | agent | subject | other
  deriving DecidableEq

namespace State

/-- The state before the discourse. -/
def initial : State E := ⟨0, none, none, [], [], none, [], []⟩

variable [DecidableEq E] (st : State E)

/-- The confirmation of the current focus at sentence `t` by the anaphora `a` of the sentence:
the focus is retained when an anaphor co-specifies it (step 4), moved to the first
co-specified alternate (step 5) or else to a co-specified stack member by popping the stack,
the members above it discarded (step 6), the rejected focus stacked on a move, and retained
when no anaphor co-specifies any focus (step 10). -/
def confirm (t : ℕ) (a : List E) : State E :=
  match st.discourse with
  | none => st
  | some cf =>
    if cf.entity ∈ a then st
    else match st.alternates.find? fun e => decide (e ∈ a) with
      | some e => { st with discourse := some ⟨e, t⟩, stack := cf.entity :: st.stack }
      | none =>
        match st.stack.dropWhile fun e => decide (e ∉ a) with
        | e :: rest => { st with discourse := some ⟨e, t⟩, stack := cf.entity :: rest }
        | [] => st

/-- The actor focus at sentence `t` is the agent of the sentence when it has one, the previous
actor focus being stacked when it changes. -/
def updateActor (t : ℕ) (agent : Option E) : State E :=
  match agent, st.actor with
  | none, _ => st
  | some e, none => { st with actor := some ⟨e, t⟩ }
  | some e, some af =>
    if e = af.entity then st
    else { st with actor := some ⟨e, t⟩, actorStack := af.entity :: st.actorStack }

/-- Processing a sentence: the first sentence sets the discourse focus to its expected focus
and the alternates to the rest of the default expected focus list; a later sentence confirms
or rejects the discourse focus by its anaphora and sets the alternates to its potential foci.
Both update the actor focus, the potential actors, and the last constituent. -/
def step (s : Sentence E) : State E :=
  let t := st.time + 1
  let st' := if st.time = 0 then { st with discourse := s.expectedFocus.map fun e => ⟨e, t⟩ }
    else st.confirm t s.anaphora
  let focus := st'.discourse.map (·.entity)
  { st'.updateActor t s.agent with
    time := t
    alternates := if st.time = 0 then
        (s.defList.map (·.entity)).filter fun e => decide (some e ≠ focus)
      else s.potentialFoci focus
    potentialActors := s.potentialActors
    last := s.phrases.getLast?.map (·.entity) }

/-- Processing a discourse sentence by sentence. -/
def run (d : List (Sentence E)) : State E := d.foldl step st

/-- The recency rule's candidate: for a pronoun in subject position, the last constituent of
the previous sentence when it is an alternate. -/
def recency (pos : Position) : List E :=
  match pos, st.last with
  | .other, _ | _, none => []
  | _, some e => if e ∈ st.alternates then [e] else []

/-- The discourse focus when it takes precedence over the actor focus for a pronoun in agent
position, having been established in an earlier sentence. -/
def precedence : List E :=
  match st.discourse, st.actor with
  | some d, some a => if d.since < a.since then [d.entity] else []
  | some d, none => [d.entity]
  | none, _ => []

/-- The candidates for the co-specification of a third person pronoun in the order the rules
test them. After the recency rule, a pronoun in agent position tests the discourse focus when
it takes precedence, the actor focus, the potential actors, the stacked actors, and then the
discourse focus and its alternates; a pronoun outside agent position tests the discourse
focus, its alternates, the actor focus, and the potential actors. -/
def candidates (pos : Position) : List E :=
  let df := (st.discourse.map (·.entity)).toList
  let af := (st.actor.map (·.entity)).toList
  st.recency pos ++
    match pos with
    | .agent => st.precedence ++ af ++ st.potentialActors ++ st.actorStack ++ df ++ st.alternates
    | _ => df ++ st.alternates ++ af ++ st.potentialActors

/-- The co-specification of a pronoun: the first candidate that the syntactic anaphoric filters
and the inference mechanism, `ok`, accept. -/
def cospecify (pos : Position) (ok : E → Prop) [DecidablePred ok] : Option E :=
  (st.candidates pos).find? fun e => decide (ok e)

variable {st} {t : ℕ} {a : List E} {cf : Focus E}

theorem confirm_of_mem (h : st.discourse = some cf) (ha : cf.entity ∈ a) :
    st.confirm t a = st := by
  simp [confirm, h, ha]

theorem confirm_of_not_mem (h : st.discourse = some cf) (ha : cf.entity ∉ a)
    (halt : ∃ e ∈ st.alternates, e ∈ a) :
    ∃ e ∈ st.alternates, e ∈ a ∧ (st.confirm t a).discourse = some ⟨e, t⟩ ∧
      (st.confirm t a).stack = cf.entity :: st.stack := by
  obtain ⟨e, he, hea⟩ := halt
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1
    (List.find?_isSome.2 ⟨e, he, by simpa using hea⟩ :
      (st.alternates.find? fun e => decide (e ∈ a)).isSome)
  exact ⟨e', List.mem_of_find?_eq_some he', by simpa using List.find?_some he',
    by simp [confirm, h, ha, he'], by simp [confirm, h, ha, he']⟩

theorem confirm_of_mem_stack (h : st.discourse = some cf) (ha : cf.entity ∉ a)
    (halt : ∀ e ∈ st.alternates, e ∉ a) {p q : List E} {e : E}
    (hs : st.stack = p ++ e :: q) (hp : ∀ x ∈ p, x ∉ a) (he : e ∈ a) :
    (st.confirm t a).discourse = some ⟨e, t⟩ ∧ (st.confirm t a).stack = cf.entity :: q := by
  have hfind : st.alternates.find? (fun e => decide (e ∈ a)) = none :=
    List.find?_eq_none.2 fun x hx => by simpa using halt x hx
  have hdrop : st.stack.dropWhile (fun x => !decide (x ∈ a)) = e :: q := by
    rw [hs, List.dropWhile_append_of_pos fun x hx => by simpa using hp x hx]
    simp [he]
  constructor <;> simp [confirm, h, ha, hfind, hdrop]

variable {pos : Position} {ok : E → Prop} [DecidablePred ok] {e : E}

theorem cospecify_spec (h : st.cospecify pos ok = some e) : ok e ∧ e ∈ st.candidates pos :=
  ⟨by simpa using List.find?_some h, List.mem_of_find?_eq_some h⟩

/-- The precedence clause of the animate discourse focus rule: a discourse focus established in
an earlier sentence than the actor focus and accepted by the filters co-specifies a pronoun
even in agent position. -/
theorem cospecify_agent_of_precedence {d af : Focus E} (hd : st.discourse = some d)
    (haf : st.actor = some af) (hlt : d.since < af.since) (hok : ok d.entity)
    (hrec : ∀ e ∈ st.recency .agent, ¬ ok e) : st.cospecify .agent ok = some d.entity := by
  have hp : st.precedence = [d.entity] := by simp [precedence, hd, haf, hlt]
  have hr : (st.recency .agent).find? (fun e => decide (ok e)) = none :=
    List.find?_eq_none.2 fun e he => by simpa using hrec e he
  simp [cospecify, candidates, hp, List.find?_append, hr, hok]

end State

/-! ### The examples

The entities of the sentences illustrating the expected focus algorithm and of the discourses
D2, D7, D8, D9, D10 and D14 of chapter 4 and D25, D31 and D35 of chapter 2. -/

/-- The entities of the examples. -/
inductive Entity
  | speaker | sister | zoo | today | oldMan | woods | linda | dog | allDay
  | mary | party | hildasHouse | cherryStreet
  | necklace | office | yesterday | grandmother
  | max | bloomingdales | ned | winston | trip | sneakers | mother
  | jeff | days | carl | exams | oscar | cape
  | john | mike
  | myDog | theVet | hand | medicine
  | lastWeek | strawberries | refrigerator | foodCoop
  | alfredZohar | baseball | school | dinner | iceCreamCones
  | wilbur | book | relativityTheory | quarks | fieldTheories | research
  deriving DecidableEq

open Entity

/-- A phrase realized by a name or a description. -/
def np (e : Entity) (θ : Thematic) (animate : Bool := false) : Phrase Entity :=
  ⟨e, θ, false, animate⟩

/-- A phrase realized by a pronoun. -/
def pron (e : Entity) (θ : Thematic) (animate : Bool := true) : Phrase Entity :=
  ⟨e, θ, true, animate⟩

/-- (22) I took my sister to the zoo today. -/
def ex22 : Sentence Entity :=
  ⟨.plain, [pron speaker .agent, np sister .theme true, np zoo .other, np today .other]⟩

/-- (23) There once was an old man who lived in the woods. -/
def ex23 : Sentence Entity := ⟨.thereInsertion oldMan, [np oldMan .theme true, np woods .other]⟩

/-- (24) Linda talked with her dog all day long, with no theme. -/
def ex24 : Sentence Entity :=
  ⟨.plain, [np linda .agent true, np dog .other true, np allDay .other]⟩

-- (22), (23), (24)
theorem expectedFocus_examples : ex22.expectedFocus = some sister ∧
    ex23.expectedFocus = some oldMan ∧ ex24.expectedFocus = some dog := by
  decide

namespace D2

/-- (D2-1) Mary is giving a surprise party at Hilda's house. -/
def a : Sentence Entity := ⟨.plain, [np mary .agent true, np party .theme, np hildasHouse .other]⟩

-- The recency rule: *it* co-specifies Hilda's house, the last constituent of (D2-1), before
-- the expected focus, the party.
theorem it_hildasHouse :
    ((State.initial.step a).cospecify .subject (· ∈ [party, hildasHouse]) = some hildasHouse) ↔
      Examples.d2.judgment = .acceptable := by
  decide

end D2

namespace D7

/-- (D7-1) I lost a necklace at the office yesterday. -/
def a : Sentence Entity :=
  ⟨.plain, [pron speaker .agent, np necklace .theme, np office .other, np yesterday .other]⟩

/-- (D7-2) I inherited it from my grandmother. -/
def b : Sentence Entity :=
  ⟨.plain, [pron speaker .agent, pron necklace .theme false, np grandmother .other true]⟩

-- Both *it* co-specify the discourse focus, the necklace; the alternate office is never
-- considered.
theorem it_necklace :
    ((State.initial.step a).cospecify .other (· ∈ [necklace, office]) = some necklace ∧
      (State.initial.run [a, b]).cospecify .subject (· ∈ [necklace, office]) = some necklace) ↔
      Examples.d7.judgment = .acceptable := by
  decide

end D7

namespace D8

/-- (D8-1) Yesterday Max went to Bloomingdales with Ned and Winston on a shopping trip. -/
def a : Sentence Entity :=
  ⟨.plain, [np yesterday .other, np max .agent true, np bloomingdales .theme, np ned .other true,
    np winston .other true, np trip .other]⟩

-- *He* co-specifies the actor focus: the discourse focus was established in the same sentence
-- and takes no precedence.
theorem he_max :
    ((State.initial.step a).cospecify .agent (· ∈ [max, ned, winston]) = some max) ↔
      Examples.d8.judgment = .acceptable := by
  decide

end D8

namespace D9

/-- (D9-1) I haven't seen Jeff for several days. -/
def a : Sentence Entity := ⟨.plain, [pron speaker .agent, np jeff .theme true, np days .other]⟩

/-- (D9-2) Carl thinks he's studying for his exams, the pronoun in the agent position of the
complement co-specifying Jeff. -/
def b : Sentence Entity := ⟨.plain, [np carl .agent true, pron jeff .agent, np exams .other]⟩

/-- (D9-3) Oscar says he is sick, the pronoun again in agent position. -/
def c : Sentence Entity := ⟨.plain, [np oscar .agent true, pron jeff .agent]⟩

/-- The state after (D9-2). -/
def afterB : State Entity := State.initial.run [a, b]

/-- The state after (D9-3). -/
def afterC : State Entity := afterB.step c

-- The discourse focus stays Jeff while the actor focus moves from the speaker to Carl to
-- Oscar.
theorem foci : afterB.discourse = some ⟨jeff, 1⟩ ∧ afterB.actor = some ⟨carl, 2⟩ ∧
    afterC.discourse = some ⟨jeff, 1⟩ ∧ afterC.actor = some ⟨oscar, 3⟩ := by
  decide

/-- Every *he* of D9 co-specifies Jeff: the discourse focus was established before any other
phrase satisfying person, number and gender, so it takes precedence over each actor focus even
in agent position. -/
theorem he_jeff :
    ((State.initial.step a).cospecify .agent (· ∈ [jeff, carl, oscar]) = some jeff ∧
      afterB.cospecify .agent (· ∈ [jeff, carl, oscar]) = some jeff ∧
        afterC.cospecify .agent (· ∈ [jeff, carl, oscar]) = some jeff) ↔
      Examples.d9.judgment = .acceptable := by
  decide

end D9

namespace D10

/-- (D10-1) John called up Mike yesterday. -/
def a : Sentence Entity :=
  ⟨.plain, [np john .agent true, np mike .theme true, np yesterday .other]⟩

-- (D10-2a): the discourse focus, Mike, and the actor focus, John, were established in the
-- same sentence, so the discourse focus takes no precedence and *he* co-specifies the actor
-- focus.
theorem he_john :
    ((State.initial.step a).cospecify .agent (· ∈ [john, mike]) = some john) ↔
      Examples.d10.judgment = .acceptable := by
  decide

end D10

namespace D14

/-- (D14-1) I took my dog to the vet yesterday. -/
def a : Sentence Entity :=
  ⟨.plain, [pron speaker .agent, np myDog .theme true, np theVet .other true, np yesterday .other]⟩

/-- (D14-2a) He bit him in the hand, *he* my dog and *him* the vet. -/
def b : Sentence Entity :=
  ⟨.plain, [pron myDog .agent, pron theVet .theme, np hand .other]⟩

/-- (D14-2b) He injected him with a new medicine, *he* the vet and *him* my dog. -/
def b' : Sentence Entity :=
  ⟨.plain, [pron theVet .agent, pron myDog .theme, np medicine .other]⟩

/-- The state after (D14-1). -/
def afterA : State Entity := State.initial.step a

-- Fig. 18: the actor focus, the speaker, fails the filters for *he*, so the first potential
-- actor, my dog, co-specifies it; the discourse focus, my dog, is rejected for *him* by
-- inference, dogs having no hands, so the first alternate, the vet, co-specifies it.
theorem cospecifications_a :
    (afterA.cospecify .agent (· ∈ [myDog, theVet]) = some myDog ∧
      afterA.cospecify .other (· ∈ [theVet]) = some theVet) ↔
      Examples.d14a.judgment = .acceptable := by
  decide

-- Fig. 20: the discourse focus, my dog, is retained for *him*, a dog being injectable, while
-- for *he* the actor focus and my dog are rejected, dogs giving no injections, and the vet
-- co-specifies it.
theorem cospecifications_b :
    (afterA.cospecify .agent (· ∈ [theVet]) = some theVet ∧
      afterA.cospecify .other (· ∈ [myDog, theVet]) = some myDog) ↔
      Examples.d14b.judgment = .acceptable := by
  decide

-- Fig. 19: the alternates after (D14-1) are the vet, yesterday and the speaker in the printed
-- order; after (D14-2a) the discourse focus moves to the vet with my dog stacked and the
-- actor focus to my dog with the speaker stacked; after (D14-2b) my dog is retained and the
-- vet is the actor focus.
theorem foci : afterA.alternates = [theVet, yesterday, speaker] ∧
    (afterA.step b).discourse = some ⟨theVet, 2⟩ ∧ (afterA.step b).stack = [myDog] ∧
    (afterA.step b).actor = some ⟨myDog, 2⟩ ∧ (afterA.step b).actorStack = [speaker] ∧
      (afterA.step b').discourse = some ⟨myDog, 1⟩ ∧ (afterA.step b').actor = some ⟨theVet, 2⟩ := by
  decide

end D14

namespace D25

/-- (D25-1) Last week there were some nice strawberries in the refrigerator. -/
def a : Sentence Entity :=
  ⟨.thereInsertion strawberries,
    [np lastWeek .other, np strawberries .theme, np refrigerator .other]⟩

/-- (D25-2) They came from our food co-op and were unusually fresh. -/
def b : Sentence Entity := ⟨.plain, [pron strawberries .theme false, np foodCoop .other]⟩

-- Fig. 8: *they* co-specifies the strawberries, the current focus, past the recency candidate,
-- the refrigerator, which fails number agreement; step 4 retains the focus.
theorem retained :
    ((State.initial.step a).cospecify .subject (· ∈ [strawberries]) = some strawberries ∧
      (State.initial.run [a, b]).discourse = some ⟨strawberries, 1⟩ ∧
        (State.initial.run [a, b]).stack = []) ↔
      Examples.d25.judgment = .acceptable := by
  decide

end D25

namespace D31

/-- (D31-8) Anyway, I got it while I was working on the initial part of my research, *it* the
book. -/
def h : Sentence Entity :=
  ⟨.plain, [pron speaker .agent, pron book .theme false, np research .other]⟩

/-- The state when (D31-8) is processed: the discourse focus is the elementary field theories
over the stack of Fig. 10, *quarks*, relativity theory, the book and Wilbur, with the
alternates the potential foci of (D31-7) and the actor focus Wilbur, the agent of (D31-2). -/
def beforeH : State Entity :=
  ⟨7, some ⟨fieldTheories, 6⟩, some ⟨wilbur, 2⟩, [research], [], some research,
    [quarks, relativityTheory, book, wilbur], []⟩

/-- Processing (D31-8) pops the focus stack: *it* co-specifies the stacked book past the focus
and the alternates, the intervening *quarks* and relativity theory are discarded, and the
rejected field theories are stacked, leaving Wilbur one position down. -/
theorem popped :
    ((beforeH.step h).discourse = some ⟨book, 8⟩ ∧
      (beforeH.step h).stack = [fieldTheories, wilbur]) ↔
      Examples.d31.judgment = .acceptable := by
  decide

end D31

namespace D35

/-- (D35-1) Alfred and Zohar liked to play baseball, the theme of the complement. -/
def a : Sentence Entity := ⟨.plain, [np alfredZohar .agent true, np baseball .theme]⟩

/-- (D35-2) They played it everyday after school before dinner. -/
def b : Sentence Entity :=
  ⟨.plain, [pron alfredZohar .agent, pron baseball .theme false, np school .other,
    np dinner .other]⟩

/-- (D35-3) After their game, Alfred and Zohar had ice cream cones, the game the baseball. -/
def c : Sentence Entity :=
  ⟨.plain, [np baseball .other, np alfredZohar .agent true, np iceCreamCones .theme]⟩

/-- (D35-4) They tasted really good. -/
def d : Sentence Entity := ⟨.plain, [pron iceCreamCones .theme false]⟩

/-- The movement of the discourse focus in D35: the baseball established from the verb
complement of (D35-1) is confirmed through (D35-3); the *they* of (D35-4) co-specifies the
alternate ice cream cones by the recency rule, the focus moves there and the baseball is
stacked. -/
theorem movement :
    ((State.initial.run [a, b, c]).discourse = some ⟨baseball, 1⟩ ∧
      (State.initial.run [a, b, c]).alternates = [iceCreamCones] ∧
        (State.initial.run [a, b, c]).cospecify .subject
          (· ∈ [alfredZohar, iceCreamCones]) = some iceCreamCones ∧
      (State.initial.run [a, b, c, d]).discourse = some ⟨iceCreamCones, 4⟩ ∧
        (State.initial.run [a, b, c, d]).stack = [baseball]) ↔
      Examples.d35.judgment = .acceptable := by
  decide

end D35

end Sidner1979
