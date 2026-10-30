module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Composition.Tree
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.Verbal.Applicative
public import Linglib.Syntax.Minimalist.Verbal.Voice.Denotation
public import Linglib.Data.Examples.Pylkkanen2008

/-!
# Pylkkänen (2008): Introducing Arguments

Pylkkänen's inventory of argument-introducing heads underlies two typologies. Applicative heads
are high or low: a high applicative relates the applied argument to the event and combines with
the verb phrase by Event Identification, and a low applicative relates it to the verb's theme
by a transfer of possession and takes the verb as its argument. Causative heads share one
meaning, Cause, which relates a causing event to a caused one and introduces no individual;
they vary in whether Cause is bundled with Voice and in whether it selects a root, a verb or a
phase. The book's structures, built as syntactic objects and interpreted by the composition
engine, compute its denotations for [the Chaga benefactive](##interp_chaga) and [the English
double object construction](##interp_buyTree). The diagnostics that separate the heads are facts
about composition: [an applicative head merged with an unergative verb composes exactly when it
is high](##unergative_composes_iff), and in the book's structure relating a low applied argument
to an external argument, [the low ApplP composes to a contradiction](##interp_ranMary).

## Main definitions

* `lowAppl`: the low applicative.
* `lex`: the lexicon of the book's applicative sentences in a `Model`.
* `CauseHead.Embeds`: the layers a causative head's complement may contain.

## Implementation notes

Semantic types are those of `Montague.Ty`, whose eventuality sort `v` is the book's event type
`s`, so the book's `⟨s,t⟩` is `Ty.vt` and `⟨e,⟨s,t⟩⟩` is `Ty.evt`. A constituent fails to compose
with another exactly when `Ty.combine?` returns `none`.

Voice denotes as agentive Voice, and a transitive verb such as *eat*, the book's
`λx.λe. eating(e) & theme(e,x)`, as the Event Identification of its theme with its event
predicate, so the engine's conjuncts come in another order than the book's. In (16b) the engine
asserts the theme twice, once from the verb and once from the low applicative, where the book
writes it once.

For a low applied argument over an unergative the book gives one structure, (103b), in which the
ApplP merges above Voice′ and composes to a contradiction; `ranMary` is that structure. The low
heads are also built in the high applicative's position, `unergative`, where they do not compose.

The third applicative diagnostic, the availability of the applied argument for depictive
modification, is also a typing fact in the book: a depictive phrase is of type ⟨e,⟨s,t⟩⟩ and
combines by Predicate Modification with constituents of that type, which a high Appl' is and a
low Appl' is not. The engine's predicate modification is at `⟨e,t⟩` and `⟨v,t⟩` only, so that
diagnostic is recorded in the data rows only.

The Voice-bundling status of the Bemba, Luganda, and Venda causatives is unknown (Table 3.1,
note a), so only the English, Japanese, and Finnish heads are given as `CauseHead` values.

## Errata

In (103b) the printed Voice′ denotation `λx.λe. running(e) & agent(e,y)` binds `x` and uses `y`;
the printed VoiceP denotation, with `agent(e,Mary)`, requires `agent(e,x)`, as the study reads
it.

## TODO

The second applicative diagnostic (18), that low applicatives are nonsensical with completely
static verbs such as *hold*, is a fact about the plausibility of the transfer of possession
(15) asserts, not a typing fact: the low ApplP composes with a static transitive verb
(`lowApplP_composes_transitive`). Since the transfer relation of (15) is not relativized to the
event, the clash with a static event does not follow from the denotation; the study records the
book's correlation of the two tests across Table 2.1 (`table21_static_iff_unergative`).

## References

* [pylkkanen-2008]
* [kratzer-1996]
* [marantz-1993]
* [marantz-1997]
* [cuervo-2003]
-/

@[expose] public section

namespace Pylkkanen2008


open ArgumentStructure Minimalist Examples Montague PhraseStructure.Tree
open scoped SetRel

variable {Entity E : Type*}

/-! ### Applicatives: high relates to the event, low to the theme -/

/-- The low applicative (15) relates the direct object `x` to the indirect object `y` by the
transfer relation `poss`, to-the-possession for a recipient applicative and from-the-possession
for a source applicative, and asserts that `x` is the theme of the verb `f`. -/
def lowAppl (theme : Entity → E → Prop) (poss : Entity → Entity → Prop) (x y : Entity)
    (f : Entity → E → Prop) : E → Prop :=
  fun e ↦ f x e ∧ theme x e ∧ poss x y

/-- `lowApplTy` is the type of the low applicative head (15), `⟨e,⟨e,⟨⟨e,⟨s,t⟩⟩,⟨s,t⟩⟩⟩⟩`. -/
abbrev lowApplTy : Ty := .e ⇒ .e ⇒ Ty.evt ⇒ Ty.vt

-- (17)
theorem lowAppl_not_composes_unergative :
    ∀ τ ∈ [lowApplTy, .e ⇒ Ty.evt ⇒ Ty.vt, Ty.evt ⇒ Ty.vt],
      Ty.combine? τ Ty.vt = none ∧ Ty.combine? Ty.vt τ = none := by
  decide

-- (18)
theorem lowApplP_composes_transitive : Ty.combine? (Ty.evt ⇒ Ty.vt) Ty.evt = some Ty.vt := by
  decide

-- (103b)
theorem lowAppl_agent_eq_bot {agent theme : Entity → E → Prop} (h : Disjoint agent theme)
    (poss : Entity → Entity → Prop) (run : E → Prop) (x y : Entity) :
    lowAppl theme poss x y (eventIdentification agent run) = ⊥ := by
  ext e
  simp only [Pi.disjoint_iff, Prop.disjoint_iff] at h
  simpa [lowAppl] using fun ha _ ht _ ↦ h x e ⟨ha, ht⟩

/-! ### The applicatives on the composition engine -/

section Engine

/-- A model of the book's applicative sentences: the relations of Voice by instruction, the
benefactive of the high applicative (13), the theme and the transfer relations of the low
applicatives (15), the events of the verbs, and the individuals. -/
structure Model (Entity V : Type) where
  role : Voice.Instruction → Entity → V → Prop
  benefactive : Entity → V → Prop
  theme : Entity → V → Prop
  toPossession : Entity → Entity → Prop
  fromPossession : Entity → Entity → Prop
  eating : V → Prop
  buying : V → Prop
  running : V → Prop
  he : Entity
  wife : Entity
  food : Entity
  mary : Entity
  john : Entity
  book : Entity
  speaker : Entity

/-- Voice, which introduces the external argument. -/
def agentVoice : LexicalItem.Token := ⟨.of .Voice [] "Voice", 300⟩

/-- The high benefactive applicative head of (3). -/
def applBen : LexicalItem.Token := ⟨.of .Appl [.V] "Appl_Ben", 301⟩

/-- The low recipient applicative head, (15a). -/
def applTo : LexicalItem.Token := ⟨.of .Appl [.D] "Appl_To", 302⟩

/-- The low source applicative head, (15b). -/
def applFrom : LexicalItem.Token := ⟨.of .Appl [.D] "Appl_From", 303⟩

/-- *eat*, which selects its theme. -/
def eat : LexicalItem.Token := ⟨.of .V [.D] "eat", 304⟩

/-- *food*. -/
def food : LexicalItem.Token := ⟨.of .D [] "food", 305⟩

/-- *he*. -/
def he : LexicalItem.Token := ⟨.of .D [] "he", 306⟩

/-- *wife*. -/
def wife : LexicalItem.Token := ⟨.of .D [] "wife", 307⟩

/-- *buy*, which selects its theme. -/
def buy : LexicalItem.Token := ⟨.of .V [.D] "buy", 308⟩

/-- *Mary*. -/
def mary : LexicalItem.Token := ⟨.of .D [] "Mary", 309⟩

/-- *John*. -/
def john : LexicalItem.Token := ⟨.of .D [] "John", 310⟩

/-- *the book*. -/
def theBook : LexicalItem.Token := ⟨.of .D [] "the book", 311⟩

/-- *run*, an unergative verb. -/
def run : LexicalItem.Token := ⟨.of .V [] "run", 312⟩

/-- *I*. -/
def me : LexicalItem.Token := ⟨.of .D [] "I", 313⟩

/-- (3), (6a): the Chaga benefactive, `[VoiceP he [Voice′ Voice [ApplP wife [Appl′ Appl_Ben [VP eat
food]]]]]`. -/
def chaga : LinearizedSyntacticObject := he * (agentVoice * (wife * (applBen * (eat * food))))

/-- (16b): `[VoiceP Mary [Voice′ Voice [VP buy [ApplP John [Appl′ Appl the book]]]]]`. -/
def buyTree : LinearizedSyntacticObject :=
  mary * (agentVoice * (buy * (john * (applTo * theBook))))

/-- The applicative head `h` merged with the unergative *run*, in the position of the high
applicative of (6a). -/
def unergative (h : LexicalItem.Token) : LinearizedSyntacticObject :=
  he * (agentVoice * (wife * (h * run)))

/-- (103b): `[VoiceP [ApplP I [Appl′ Appl Mary]] [Voice′ Voice run]]`, the low applicative over a
constituent whose open argument is the external argument. -/
def ranMary : LinearizedSyntacticObject := (me * (applTo * mary)) * (agentVoice * run)

variable {Entity V : Type} (M : Model Entity V)

/-- The lexicon: Voice denotes as agentive Voice, the high applicative the benefactive relation
(13), the low applicatives the entries (15), *eat* and *buy* the events of eating and buying with
their themes, *run* the events of running, and the noun phrases the model's individuals. -/
def lex (tok : LexicalItem.Token) : Option (Denotation Entity Unit Id { eventuality := V }) :=
  if tok = agentVoice then Voice.agentive.denote M.role
  else if tok = applBen then some ⟨Ty.evt, M.benefactive⟩
  else if tok = applTo then some ⟨lowApplTy, lowAppl M.theme M.toPossession⟩
  else if tok = applFrom then some ⟨lowApplTy, lowAppl M.theme M.fromPossession⟩
  else if tok = eat then some ⟨Ty.evt, eventIdentification M.theme M.eating⟩
  else if tok = buy then some ⟨Ty.evt, eventIdentification M.theme M.buying⟩
  else if tok = run then some ⟨Ty.vt, M.running⟩
  else if tok = he then some ⟨.e, M.he⟩
  else if tok = wife then some ⟨.e, M.wife⟩
  else if tok = food then some ⟨.e, M.food⟩
  else if tok = mary then some ⟨.e, M.mary⟩
  else if tok = john then some ⟨.e, M.john⟩
  else if tok = theBook then some ⟨.e, M.book⟩
  else if tok = me then some ⟨.e, M.speaker⟩
  else none

section Entries

variable {M}

private theorem lex_agentVoice : lex M agentVoice = some ⟨Ty.evt, M.role .agent⟩ := by
  simp [lex, Voice.Head.denote, Voice.agentive]

private theorem lex_applBen : lex M applBen = some ⟨Ty.evt, M.benefactive⟩ := by
  simp [lex, applBen, agentVoice]

private theorem lex_applTo : lex M applTo = some ⟨lowApplTy, lowAppl M.theme M.toPossession⟩ := by
  simp [lex, applTo, applBen, agentVoice]

private theorem lex_applFrom :
    lex M applFrom = some ⟨lowApplTy, lowAppl M.theme M.fromPossession⟩ := by
  simp [lex, applFrom, applTo, applBen, agentVoice]

private theorem lex_eat : lex M eat = some ⟨Ty.evt, eventIdentification M.theme M.eating⟩ := by
  simp [lex, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_buy : lex M buy = some ⟨Ty.evt, eventIdentification M.theme M.buying⟩ := by
  simp [lex, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_run : lex M run = some ⟨Ty.vt, M.running⟩ := by
  simp [lex, run, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_he : lex M he = some ⟨.e, M.he⟩ := by
  simp [lex, he, run, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_wife : lex M wife = some ⟨.e, M.wife⟩ := by
  simp [lex, wife, he, run, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_food : lex M food = some ⟨.e, M.food⟩ := by
  simp [lex, food, wife, he, run, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_mary : lex M mary = some ⟨.e, M.mary⟩ := by
  simp [lex, mary, food, wife, he, run, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_john : lex M john = some ⟨.e, M.john⟩ := by
  simp [lex, john, mary, food, wife, he, run, buy, eat, applFrom, applTo, applBen, agentVoice]

private theorem lex_theBook : lex M theBook = some ⟨.e, M.book⟩ := by
  simp [lex, theBook, john, mary, food, wife, he, run, buy, eat, applFrom, applTo, applBen,
    agentVoice]

private theorem lex_me : lex M me = some ⟨.e, M.speaker⟩ := by
  simp [lex, me, theBook, john, mary, food, wife, he, run, buy, eat, applFrom, applTo, applBen,
    agentVoice]

end Entries

/-- (3): the engine computes the Chaga benefactive, the event of eating the food of which he is the
agent and his wife the beneficiary, by Functional Application, Event Identification of the high
applicative, Functional Application and Event Identification of Voice. -/
theorem interp_chaga (g : Assignment Entity) :
    (chaga.toTree (·.id)).interp (lex M) g = some ⟨Ty.vt, fun e ↦
      M.role .agent M.he e ∧ M.benefactive M.wife e ∧ M.theme M.food e ∧ M.eating e⟩ := by
  simp only [chaga, LinearizedSyntacticObject.mul_def,
    LinearizedSyntacticObject.toTree_merge, LinearizedSyntacticObject.toTree_leaf,
    PhraseStructure.Tree.interp_phrase_binary, PhraseStructure.Tree.interp_terminal,
    lex_he, lex_agentVoice, lex_wife, lex_applBen, lex_eat, lex_food, Option.bind_some]
  rfl

/-- (16b): the engine computes *Mary bought John the book*, the low ApplP taking the verb as its
argument, as the event of buying the book of which Mary is the agent, the book being to John's
possession. -/
theorem interp_buyTree (g : Assignment Entity) :
    (buyTree.toTree (·.id)).interp (lex M) g = some ⟨Ty.vt, fun e ↦
      M.role .agent M.mary e ∧ (M.theme M.book e ∧ M.buying e) ∧ M.theme M.book e ∧
        M.toPossession M.book M.john⟩ := by
  simp only [buyTree, LinearizedSyntacticObject.mul_def,
    LinearizedSyntacticObject.toTree_merge, LinearizedSyntacticObject.toTree_leaf,
    PhraseStructure.Tree.interp_phrase_binary, PhraseStructure.Tree.interp_terminal,
    lex_mary, lex_agentVoice, lex_buy, lex_john, lex_applTo, lex_theBook, Option.bind_some]
  rfl

-- (17)
theorem interp_unergative (g : Assignment Entity) :
    ((unergative applBen).toTree (·.id)).interp (lex M) g = some ⟨Ty.vt, fun e ↦
        M.role .agent M.he e ∧ M.benefactive M.wife e ∧ M.running e⟩ ∧
      ((unergative applTo).toTree (·.id)).interp (lex M) g = none ∧
      ((unergative applFrom).toTree (·.id)).interp (lex M) g = none := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [unergative, LinearizedSyntacticObject.mul_def,
    LinearizedSyntacticObject.toTree_merge, LinearizedSyntacticObject.toTree_leaf,
    PhraseStructure.Tree.interp_phrase_binary, PhraseStructure.Tree.interp_terminal,
    lex_he, lex_agentVoice, lex_wife, lex_applBen, lex_applTo, lex_applFrom, lex_run,
    Option.bind_some] <;> rfl

/-- (103b): the low recipient applicative over the unergative *run*, Voice already merged,
composes, but to the empty predicate when no individual is both the agent and the theme of an
event: the transfer it asserts makes the agent of running the theme. -/
theorem interp_ranMary (g : Assignment Entity) (h : Disjoint (M.role .agent) M.theme) :
    (ranMary.toTree (·.id)).interp (lex M) g = some ⟨Ty.vt, (⊥ : V → Prop)⟩ := by
  rw [← lowAppl_agent_eq_bot h M.toPossession M.running M.mary M.speaker]
  simp only [ranMary, LinearizedSyntacticObject.mul_def,
    LinearizedSyntacticObject.toTree_merge, LinearizedSyntacticObject.toTree_leaf,
    PhraseStructure.Tree.interp_phrase_binary, PhraseStructure.Tree.interp_terminal,
    lex_me, lex_applTo, lex_mary, lex_agentVoice, lex_run, Option.bind_some]
  rfl

section CCommand

open SyntacticObject

-- (6): the applied argument asymmetrically c-commands the direct object
theorem wife_cCommands_food :
    CCommands chaga (leaf wife) (leaf food) ∧ ¬ CCommands chaga (leaf food) (leaf wife) := by
  constructor <;> decide

-- (6)
theorem john_cCommands_theBook :
    CCommands buyTree (leaf john) (leaf theBook) ∧
      ¬ CCommands buyTree (leaf theBook) (leaf john) := by
  constructor <;> decide

end CCommand

/-- The applicative head of a type of the book's inventory: the benefactive for the high
applicative and the recipient and source heads (15) for the low ones; the static-possession and
affected applicatives of [cuervo-2003] are outside it. -/
def applHead? : ApplType → Option LexicalItem.Token
  | .high => some applBen
  | .low .recipient => some applTo
  | .low .source => some applFrom
  | .low .possessor => none
  | .affected => none

/-- A model on `Unit` in which every relation holds. -/
private def unitModel : Model Unit Unit :=
  { role := fun _ _ _ ↦ True, benefactive := fun _ _ ↦ True, theme := fun _ _ ↦ True,
    toPossession := fun _ _ ↦ True, fromPossession := fun _ _ ↦ True, eating := fun _ ↦ True,
    buying := fun _ ↦ True, running := fun _ ↦ True, he := (), wife := (), food := (), mary := (),
    john := (), book := (), speaker := () }

/-- An applicative head, merged with the unergative *run*, composes in every model exactly when it
is high, Diagnostic 1 (17). -/
theorem unergative_composes_iff (a : ApplType) :
    (∃ h ∈ applHead? a, ∀ (Entity V : Type) (M : Model Entity V) (g : Assignment Entity),
      (((unergative h).toTree (·.id)).interp (lex M) g).isSome) ↔ a = .high := by
  rcases a with _ | _ | (_ | _ | _)
  · exact iff_of_true ⟨applBen, rfl, fun _ _ M g ↦ by rw [(interp_unergative M g).1]; rfl⟩ rfl
  · exact iff_of_false (fun ⟨_, h, _⟩ ↦ nomatch h) nofun
  · refine iff_of_false (fun ⟨h, hh, hall⟩ ↦ ?_) nofun
    obtain rfl := Option.some.inj hh
    simpa [(interp_unergative unitModel fun _ ↦ ()).2.1] using hall Unit Unit unitModel fun _ ↦ ()
  · refine iff_of_false (fun ⟨h, hh, hall⟩ ↦ ?_) nofun
    obtain rfl := Option.some.inj hh
    simpa [(interp_unergative unitModel fun _ ↦ ()).2.2] using hall Unit Unit unitModel fun _ ↦ ()
  · exact iff_of_false (fun ⟨_, h, _⟩ ↦ nomatch h) nofun

end Engine

/-- A `Construction` is one of the applicative constructions the book analyzes, with the head it
assigns
(Table 1.1, together with the Korean and Albanian applicatives of Chapter 2). -/
inductive Construction where
  | chagaBenefactive
  | lugandaBenefactive
  | vendaBenefactive
  | albanianBenefactive
  | japaneseGaplessAdversity
  | englishDOC
  | japaneseDOC
  | koreanDOC
  | hebrewPossessorDative
  | japaneseAdversityCausative
  | japaneseGappedAdversity
  deriving DecidableEq, Repr

/-- `c.head` is the head the book assigns to the construction `c`. -/
def Construction.head : Construction → ApplType
  | .chagaBenefactive | .lugandaBenefactive | .vendaBenefactive | .albanianBenefactive
  | .japaneseGaplessAdversity => .high
  | .englishDOC | .japaneseDOC | .koreanDOC => .low .recipient
  | .hebrewPossessorDative | .japaneseAdversityCausative | .japaneseGappedAdversity =>
    .low .source

/-- A construction composes with an unergative verb phrase when its head, merged with *run*,
composes on the engine in every model. -/
def Construction.ComposesUnergative (c : Construction) : Prop :=
  ∃ h ∈ applHead? c.head, ∀ (Entity V : Type) (M : Model Entity V) (g : Assignment Entity),
    (((unergative h).toTree (·.id)).interp (lex M) g).isSome

instance : DecidablePred Construction.ComposesUnergative := fun c ↦
  decidable_of_iff _ (unergative_composes_iff c.head).symm

/-- Table 2.1 lists each of the six languages with the construction tested, its unergative test,
and its static-verb test. -/
def table21 : List (Construction × Datum × Datum) :=
  [(.englishDOC, ex20a, ex20b), (.japaneseDOC, ex21a, ex21b), (.koreanDOC, ex22a, ex22b),
   (.lugandaBenefactive, ex23a, ex23b), (.vendaBenefactive, ex24a, ex24b),
   (.albanianBenefactive, ex25a, ex25b)]

-- Table 2.1
theorem table21_unergative :
    ∀ t ∈ table21, t.2.1.judgment = .acceptable ↔ t.1.ComposesUnergative := by
  decide

-- Table 2.1, §2.1.2
theorem table21_static_iff_unergative :
    ∀ t ∈ table21, t.2.2.judgment = .acceptable ↔ t.2.1.judgment = .acceptable := by
  decide

-- Table 2.5
theorem adversity_passives :
    Construction.japaneseGaplessAdversity.ComposesUnergative ∧
      ¬ Construction.japaneseGappedAdversity.ComposesUnergative := by
  decide

-- (102), Table 2.2
theorem possessor_dative_transitivity :
    ¬ Construction.hebrewPossessorDative.ComposesUnergative := by
  decide

/-! ### Cause introduces a causing event, not a causer -/

-- (9), (14), (13b), (16), (15b)
theorem melted_readings (M : EventStructure.Interpretation Entity E E)
    (agent causer : Entity → E → Prop) (melt : E → Prop) (john : Entity) (e : E) :
    (eventIdentification agent (M.vCause melt) john e ↔
        agent john e ∧ ∃ e', e ~[M.cause] e' ∧ melt e') ∧
      (eventIdentification causer melt john e ↔ causer john e ∧ melt e) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- `causeTy` is the type of Cause (9), `⟨⟨s,t⟩,⟨s,t⟩⟩`. -/
abbrev causeTy : Ty := Ty.vt ⇒ Ty.vt

-- (18), (16a), §3.2
theorem unaccusative_causative :
    Ty.combine? causeTy Ty.vt = some Ty.vt ∧ Ty.combine? Ty.evt Ty.vt = some Ty.evt := by
  decide

-- (42), §3.3
theorem cause_voice_order :
    Ty.combine? causeTy Ty.evt = none ∧ Ty.combine? Ty.evt causeTy = none ∧
      (Ty.combine? causeTy Ty.vt).bind (Ty.combine? Ty.evt) = some Ty.evt ∧
      (Ty.combine? Ty.evt Ty.vt).bind (Ty.combine? causeTy) = none := by
  decide

/-! ### Selection: Cause takes a root, a verb, or a phase -/

/-- The layers of the Kratzer/Marantz verbal architecture (12) are the category-neutral root, the
verb a category-defining head makes of it, and the phase closed by an external-argument
introducer, Voice or a high applicative. -/
inductive Layer where
  | root
  | verb
  | phase
  deriving DecidableEq, Repr, Fintype

/-- Layers are ordered by containment. -/
def Layer.rank : Layer → ℕ
  | .root => 0
  | .verb => 1
  | .phase => 2

instance : LinearOrder Layer := LinearOrder.lift' Layer.rank (by decide)

/-- A causative head is given by the largest layer its complement may contain (11) and whether
Cause is bundled with Voice (10). -/
structure CauseHead where
  selects : Layer
  bundled : Bool
  deriving DecidableEq, Repr

/-- `c.Embeds l` holds when a constituent of layer `l` can occur between the root and Cause. -/
def CauseHead.Embeds (c : CauseHead) (l : Layer) : Prop := l ≤ c.selects

instance (c : CauseHead) (l : Layer) : Decidable (c.Embeds l) :=
  inferInstanceAs (Decidable (_ ≤ _))

-- Table 3.2
theorem embeds_verb_iff (c : CauseHead) : c.Embeds .verb ↔ c.selects ≠ .root := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

-- Table 3.2
theorem embeds_phase_iff (c : CauseHead) : c.Embeds .phase ↔ c.selects = .phase := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- A causee position (94) exists inside Cause's complement when that complement is at least a
verb, or between Cause and Voice when Cause is not bundled with Voice. -/
def CauseHead.HasCauseePosition (c : CauseHead) : Prop := c.Embeds .verb ∨ c.bundled = false

instance (c : CauseHead) : Decidable c.HasCauseePosition :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Causatives of unergatives and transitives are impossible exactly for a root-selecting,
Voice-bundling head (Table 3.1, second row). -/
theorem hasCauseePosition_iff (c : CauseHead) :
    c.HasCauseePosition ↔ ¬ (c.selects = .root ∧ c.bundled = true) := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- The English zero-causative is root-selecting and Voice-bundling. -/
def englishZero : CauseHead := ⟨.root, true⟩

/-- The Japanese lexical causative is root-selecting, with Cause independent of Voice. -/
def japaneseLexical : CauseHead := ⟨.root, false⟩

/-- The Finnish *-tta* causative is verb-selecting, with Cause independent of Voice. -/
def finnishTta : CauseHead := ⟨.verb, false⟩

-- (95), (96)
theorem root_causativized_unergative :
    (ex95.judgment = .acceptable ↔ englishZero.HasCauseePosition) ∧
      (ex96.judgment = .acceptable ↔ japaneseLexical.HasCauseePosition) := by
  decide

end Pylkkanen2008
