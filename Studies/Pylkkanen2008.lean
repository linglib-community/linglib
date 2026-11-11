module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.ArgumentStructure.EventIdentification
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.SyntacticObject.ToTree
public import Linglib.Syntax.Minimalist.Clause.Size
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
phase. The book's structures, built as syntactic objects and interpreted by its rules of
composition, mean what it says for [the Chaga benefactive](##meanings_chaga) and [the English
double object construction](##meanings_buyTree). In the book's structure relating a low applied
argument to an external argument, the low ApplP [composes to events of which one individual is
both agent and theme](##meanings_ranMary), a contradiction when no agent of running is its theme,
so that over an unergative verb [only a high applicative is true of some
event](##unergative_satisfiable_iff), the book's first diagnostic of the two heads.

## Main definitions

* `lowAppl`: the low applicative.
* `grammar`: the book's rules of composition.
* `Word`, `Word.val`: the words of the book's applicative sentences by type, and what they
  denote in a `Model`.
* `Satisfiable`: an object true of some eventuality in a model where no agent of running is its
  theme.
* `CauseHead.Embeds`: the layers a causative head's complement may contain.

## Implementation notes

Semantic types are those over `Interpreter.Base`, whose eventuality sort `v` is the book's event
type `s`, so the book's `⟨s,t⟩` is `Ty.vt` and `⟨e,⟨s,t⟩⟩` is `Ty.evt`. Two constituents fail to
compose exactly when the grammar has no rule at their types.

Voice denotes what `Minimalist.Voice.Head.denote` gives the agentive head, the model's agent
relation, and a transitive verb such as *eat*, the book's `λx.λe. eating(e) & theme(e,x)`, the
Event Identification of its theme with its event predicate, so the conjuncts come in another
order than the book's. In (16b) the theme is asserted twice, once from the verb and once from
the low applicative, where the book writes it once.

Over an unergative the high applicative is built in its position of (6a), `unergative`, and the
low applicatives in the one structure the book gives them, (103b), `ranMary`, where the ApplP
merges above Voice′ and composes. The book accounts for their ungrammaticality by the
contradiction this yields, which follows where no agent of running is its theme; Table 2.1's
unergative test and (102) rest on it (`Construction.ApplicativizesUnergative`).

The third applicative diagnostic, the availability of the applied argument for depictive
modification, is also a typing fact in the book: a depictive phrase is of type ⟨e,⟨s,t⟩⟩ and
combines by Predicate Modification with constituents of that type, which a high Appl' is and a
low Appl' is not. Predicate modification here conjoins predicates `⟨a,t⟩`, which `⟨e,⟨s,t⟩⟩` is
not, so that diagnostic is recorded in the data rows only.

The Voice-bundling status of the Bemba, Luganda, and Venda causatives is unknown (Table 3.1,
note a), so only the English, Japanese, and Finnish heads are given as `CauseHead` values.

## TODO

The second applicative diagnostic (18), that low applicatives are nonsensical with completely
static verbs such as *hold*, is a fact about the plausibility of the transfer of possession
(15) asserts, not a typing fact: the low ApplP composes with a static transitive verb
(`lowApplP_composes_transitive`). Since the transfer relation of (15) is not relativized to the
event, the clash with a static event does not follow from the denotation; the study records the
book's correlation of the two tests across Table 2.1 (`table21_static_iff_unergative`).

The interpreted structures are assembled by hand from verbs, and the causative typology is a
separate classification of heads: the book's roots and categorizers, the selection that builds
its structures, and the bundling of Cause with Voice into one head are not what is interpreted.

## References

* [pylkkanen-2008]
* [kratzer-1996]
* [marantz-1993]
* [marantz-1997]
* [cuervo-2003]
-/

@[expose] public section

namespace Pylkkanen2008


open ArgumentStructure Minimalist Examples Interpreter
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
abbrev lowApplTy : Ty Base := .e ⇒ .e ⇒ .evt ⇒ .vt

/-- The book's rules of composition: Functional Application, Predicate Modification, and Event
Identification of a relation of individuals to events with a predicate of events. -/
abbrev grammar : ManySorted.Language (Ty Base) := Voice.grammar

/-- The rules a node admits, by the types of its daughters: every rule that applies. -/
abbrev rules {N : Type} : Interpreter grammar N := typeDriven grammar

-- (17): no rule combines a low applicative, at any stage of saturation, with an unergative verb
theorem lowAppl_not_composes_unergative :
    ∀ τ ∈ [lowApplTy, .e ⇒ .evt ⇒ .vt, .evt ⇒ .vt], ∀ u,
      IsEmpty (grammar.Binary τ .vt u) ∧ IsEmpty (grammar.Binary .vt τ u) := by
  intro τ hτ u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl <;>
    exact ⟨⟨by rintro ((m | m) | m) <;> cases m⟩, ⟨by rintro ((m | m) | m) <;> cases m⟩⟩

-- (18): the low ApplP takes a transitive verb by Functional Application
theorem lowApplP_composes_transitive :
    rules.binary () (.evt ⇒ .vt) .evt = [⟨.vt, .inl (.inl .fa)⟩] :=
  rfl

-- (103b): over a constituent whose open argument is the agent, the low ApplP holds of no event
-- exactly when, if `x` passes to `y`, `x` is the theme of no event of which it is the agent
theorem lowAppl_eventIdentification_eq_bot_iff {agent theme : Entity → E → Prop}
    {poss : Entity → Entity → Prop} {run : E → Prop} {x y : Entity} :
    lowAppl theme poss x y (eventIdentification agent run) = ⊥ ↔
      (poss x y → ∀ e, run e → agent x e → ¬ theme x e) := by
  refine ⟨fun h hp e hr ha ht ↦ (congrFun h e).mp ⟨⟨ha, hr⟩, ht, hp⟩,
    fun h ↦ funext fun e ↦ eq_false fun ⟨⟨ha, hr⟩, ht, hp⟩ ↦ h hp e hr ha ht⟩

/-! ### The applicative structures and their meanings -/

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

/-- The high benefactive applicative merged with the unergative *run*, in its position of
(6a). -/
def unergative : LinearizedSyntacticObject := he * (agentVoice * (wife * (applBen * run)))

/-- (103b): `[VoiceP [ApplP I [Appl′ Appl Mary]] [Voice′ Voice run]]`, the low applicative head `h`
over a constituent whose open argument is the external argument; *I ran Mary* with the recipient
head. -/
def ranMary (h : LexicalItem.Token) : LinearizedSyntacticObject :=
  (me * (h * mary)) * (agentVoice * run)

/-- The words of the book's applicative sentences, by semantic type. -/
inductive Word : Ty Base → Type
  | voice : Word .evt
  | applBen : Word .evt
  | applTo : Word lowApplTy
  | applFrom : Word lowApplTy
  | eat : Word .evt
  | buy : Word .evt
  | run : Word .vt
  | he : Word .e
  | wife : Word .e
  | food : Word .e
  | mary : Word .e
  | john : Word .e
  | theBook : Word .e
  | me : Word .e

/-- The word each token is. -/
def lexicon : List (LexicalItem.Token × Σ a, Word a) :=
  [(agentVoice, ⟨_, .voice⟩), (applBen, ⟨_, .applBen⟩), (applTo, ⟨_, .applTo⟩),
    (applFrom, ⟨_, .applFrom⟩), (eat, ⟨_, .eat⟩), (buy, ⟨_, .buy⟩), (run, ⟨_, .run⟩),
    (he, ⟨_, .he⟩), (wife, ⟨_, .wife⟩), (food, ⟨_, .food⟩), (mary, ⟨_, .mary⟩),
    (john, ⟨_, .john⟩), (theBook, ⟨_, .theBook⟩), (me, ⟨_, .me⟩)]

/-- The words a leaf may be: those of its token, and none for a trace. -/
def words : LexicalItem.Token ⊕ ℕ → List (Σ a, Word a)
  | .inl tok => lexicon.filterMap fun (t, w) ↦ if t.id = tok.id then some w else none
  | .inr _ => []

variable {Entity V : Type} (M : Model Entity V)

/-- What the words denote: Voice as agentive Voice, the high applicative the
benefactive relation (13), the low applicatives the entries (15), *eat* and *buy* the events of
eating and buying with their themes, *run* the events of running, and the noun phrases the
model's individuals. -/
def Word.val : {a : Ty Base} → Word a → a.Domain Entity Unit { eventuality := V }
  | _, .voice => Voice.agentive.denote M.role
  | _, .applBen => M.benefactive
  | _, .applTo => lowAppl M.theme M.toPossession
  | _, .applFrom => lowAppl M.theme M.fromPossession
  | _, .eat => eventIdentification M.theme M.eating
  | _, .buy => eventIdentification M.theme M.buying
  | _, .run => M.running
  | _, .he => M.he
  | _, .wife => M.wife
  | _, .food => M.food
  | _, .mary => M.mary
  | _, .john => M.john
  | _, .theBook => M.book
  | _, .me => M.speaker

/-- The meanings of a syntactic object in a model, by the book's rules. -/
def meanings (t : LinearizedSyntacticObject) :
    List (Denotation Entity Unit { eventuality := V }) :=
  match (t.toTree (·.id)).skeleton (fun _ ↦ false) with
  | some s => rules.values (D := Ty.Dom (Base.Dom Entity Unit { eventuality := V }))
      inferInstance (Word.val M) words s
  | none => []

/-- (3): the Chaga benefactive means the event of eating the food of which he is the agent and
his wife the beneficiary, by Functional Application of *eat* to *food*, Event Identification of
the high applicative, Functional Application to *wife*, Event Identification of Voice and
Functional Application to *he*. -/
theorem meanings_chaga : meanings M chaga = [⟨.vt, fun e ↦
    M.role .agent M.he e ∧ M.benefactive M.wife e ∧ M.theme M.food e ∧ M.eating e⟩] :=
  rfl

/-- (16b): *Mary bought John the book*, the low ApplP taking the verb as its argument, means the
event of buying the book of which Mary is the agent, the book being to John's possession. -/
theorem meanings_buyTree : meanings M buyTree = [⟨.vt, fun e ↦
    M.role .agent M.mary e ∧ (M.theme M.book e ∧ M.buying e) ∧ M.theme M.book e ∧
      M.toPossession M.book M.john⟩] :=
  rfl

-- (17): the high applicative over the unergative *run*
theorem meanings_unergative : meanings M unergative = [⟨.vt, fun e ↦
    M.role .agent M.he e ∧ M.benefactive M.wife e ∧ M.running e⟩] :=
  rfl

/-- (103b): the low recipient applicative over the unergative *run*, its ApplP merged above
Voice′, composes to the events of running of which Mary is the agent and the theme, Mary passing
to the speaker's possession; the book boxes the agent and theme conjuncts as a contradiction. -/
theorem meanings_ranMary : meanings M (ranMary applTo) = [⟨.vt, fun e ↦
    (M.role .agent M.mary e ∧ M.running e) ∧ M.theme M.mary e ∧
      M.toPossession M.mary M.speaker⟩] :=
  rfl

-- (103b), with the source head
theorem meanings_ranMary_applFrom : meanings M (ranMary applFrom) = [⟨.vt,
    lowAppl M.theme M.fromPossession M.mary M.speaker
      (eventIdentification (M.role .agent) M.running)⟩] :=
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

/-- The book's structure for an applicative head over the unergative *run*: the high applicative
in its position of (6a), a low one in the structure of (103b). The static-possession and affected
applicatives of [cuervo-2003] are outside the book's inventory. -/
def unergativeTree? : Appl.Head → Option LinearizedSyntacticObject
  | .high => some unergative
  | .low .recipient => some (ranMary applTo)
  | .low .source => some (ranMary applFrom)
  | .low .possessor => none
  | .affected => none

/-- An object is satisfiable when, in some model where no agent of running is its theme, it
means a predicate of eventualities true of some eventuality. -/
def Satisfiable (t : LinearizedSyntacticObject) : Prop :=
  ∃ (Entity V : Type) (M : Model Entity V),
    (∀ x e, M.running e → M.role .agent x e → ¬ M.theme x e) ∧
      ∃ P : V → Prop, ⟨.vt, P⟩ ∈ meanings M t ∧ ∃ e, P e

/-- A model on `Unit` in which every relation but the theme holds. -/
private def highModel : Model Unit Unit :=
  { role := fun _ _ _ ↦ True, benefactive := fun _ _ ↦ True, theme := fun _ _ ↦ False,
    toPossession := fun _ _ ↦ True, fromPossession := fun _ _ ↦ True, eating := fun _ ↦ True,
    buying := fun _ ↦ True, running := fun _ ↦ True, he := (), wife := (), food := (), mary := (),
    john := (), book := (), speaker := () }

private theorem not_satisfiable_ranMary {h : LexicalItem.Token}
    (hh : ∀ (Entity V : Type) (M : Model Entity V), ∃ poss, meanings M (ranMary h) =
      [⟨.vt, lowAppl M.theme poss M.mary M.speaker
        (eventIdentification (M.role .agent) M.running)⟩]) :
    ¬ Satisfiable (ranMary h) := by
  rintro ⟨Entity, V, M, hM, P, hP, e, he⟩
  obtain ⟨poss, hposs⟩ := hh Entity V M
  rw [hposs, List.mem_singleton, Sigma.mk.inj_iff] at hP
  have hbot := (lowAppl_eventIdentification_eq_bot_iff (poss := poss) (y := M.speaker)).2
    fun _ e hr ha ↦ hM M.mary e hr ha
  exact (congrFun ((eq_of_heq hP.2).trans hbot) e).mp he

/-- Diagnostic 1 (17), on the book's account of (103b): over the unergative *run*, an applicative
head's structure is satisfiable exactly when the head is high, the low applicatives' structure
being the contradiction where no agent of running is its theme. -/
theorem unergative_satisfiable_iff {a : Appl.Head} {t : LinearizedSyntacticObject}
    (ht : unergativeTree? a = some t) : Satisfiable t ↔ a = .high := by
  rcases a with _ | _ | (_ | _ | _) <;> simp only [unergativeTree?, Option.some.injEq,
    reduceCtorEq] at ht <;> subst ht
  · exact iff_of_true ⟨Unit, Unit, highModel, fun _ _ _ _ h ↦ h, _,
      List.mem_singleton.2 rfl, (), trivial, trivial, trivial⟩ rfl
  · exact iff_of_false (not_satisfiable_ranMary fun _ _ M ↦ ⟨_, rfl⟩) nofun
  · exact iff_of_false (not_satisfiable_ranMary fun _ _ M ↦ ⟨_, rfl⟩) nofun

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
def Construction.head : Construction → Appl.Head
  | .chagaBenefactive | .lugandaBenefactive | .vendaBenefactive | .albanianBenefactive
  | .japaneseGaplessAdversity => .high
  | .englishDOC | .japaneseDOC | .koreanDOC => .low .recipient
  | .hebrewPossessorDative | .japaneseAdversityCausative | .japaneseGappedAdversity =>
    .low .source

/-- A construction applicativizes an unergative, the first test of Table 2.1, when the book's
structure for its head over *run* is satisfiable. -/
def Construction.ApplicativizesUnergative (c : Construction) : Prop :=
  ∃ t ∈ unergativeTree? c.head, Satisfiable t

theorem Construction.applicativizesUnergative_iff (c : Construction) :
    c.ApplicativizesUnergative ↔ c.head = .high := by
  rcases ht : unergativeTree? c.head with _ | t
  · simp only [ApplicativizesUnergative, ht, Option.mem_def, reduceCtorEq, false_and,
      exists_false, false_iff]
    exact fun h ↦ by simp [h, unergativeTree?] at ht
  · simp [ApplicativizesUnergative, ht, unergative_satisfiable_iff ht]

instance : DecidablePred Construction.ApplicativizesUnergative := fun c ↦
  decidable_of_iff _ c.applicativizesUnergative_iff.symm

/-- Table 2.1 lists each of the six languages with the construction tested, its unergative test,
and its static-verb test. -/
def table21 : List (Construction × Datum × Datum) :=
  [(.englishDOC, ex20a, ex20b), (.japaneseDOC, ex21a, ex21b), (.koreanDOC, ex22a, ex22b),
   (.lugandaBenefactive, ex23a, ex23b), (.vendaBenefactive, ex24a, ex24b),
   (.albanianBenefactive, ex25a, ex25b)]

-- Table 2.1
theorem table21_unergative :
    ∀ t ∈ table21, t.2.1.judgment = .acceptable ↔ t.1.ApplicativizesUnergative := by
  decide

-- Table 2.1, §2.1.2
theorem table21_static_iff_unergative :
    ∀ t ∈ table21, t.2.2.judgment = .acceptable ↔ t.2.1.judgment = .acceptable := by
  decide

-- Table 2.5
theorem adversity_passives :
    Construction.japaneseGaplessAdversity.ApplicativizesUnergative ∧
      ¬ Construction.japaneseGappedAdversity.ApplicativizesUnergative := by
  decide

-- (102), Table 2.2
theorem possessor_dative_transitivity :
    ¬ Construction.hebrewPossessorDative.ApplicativizesUnergative := by
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
abbrev causeTy : Ty Base := .vt ⇒ .vt

-- (18), (16a), §3.2: Cause applies to an unaccusative, and Voice is identified with it
theorem unaccusative_causative :
    rules.binary () causeTy .vt = [⟨.vt, .inl (.inl .fa)⟩] ∧
      rules.binary () .evt .vt = [⟨.evt, .inr .left⟩] :=
  ⟨rfl, rfl⟩

-- (42), §3.3: no rule combines Cause with what Voice has been identified with, so that Voice
-- is above Cause
theorem cause_voice_order (u : Ty Base) :
    IsEmpty (grammar.Binary causeTy .evt u) ∧ IsEmpty (grammar.Binary .evt causeTy u) :=
  ⟨⟨by rintro ((m | m) | m) <;> cases m⟩, ⟨by rintro ((m | m) | m) <;> cases m⟩⟩

/-! ### Selection: Cause takes a root, a verb, or a phase -/

/-- The layers of the Kratzer/Marantz verbal architecture (12) are the category-neutral root, the
verb a category-defining head makes of it, and the phase closed by an external-argument
introducer, Voice or a high applicative. -/
inductive Layer where
  | root
  | verb
  | phase
  deriving DecidableEq, Repr, Fintype

/-- The size of a layer, its highest head: the root is the lexical head, the verb v, and the
phase Voice. -/
def Layer.size : Layer → ComplementSize
  | .root => ⟨.V⟩
  | .verb => .vP
  | .phase => ⟨.Voice⟩

/-- Layers are ordered by containment, as their sizes are in the extension order. -/
instance : Preorder Layer := Preorder.lift Layer.size

instance : DecidableLE Layer := fun l m ↦ inferInstanceAs (Decidable (l.size ≤ m.size))

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
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide +kernel

-- Table 3.2
theorem embeds_phase_iff (c : CauseHead) : c.Embeds .phase ↔ c.selects = .phase := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide +kernel

/-- A causee position (94) exists inside Cause's complement when that complement is at least a
verb, or between Cause and Voice when Cause is not bundled with Voice. -/
def CauseHead.HasCauseePosition (c : CauseHead) : Prop := c.Embeds .verb ∨ c.bundled = false

instance (c : CauseHead) : Decidable c.HasCauseePosition :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Causatives of unergatives and transitives are impossible exactly for a root-selecting,
Voice-bundling head (Table 3.1, second row). -/
theorem hasCauseePosition_iff (c : CauseHead) :
    c.HasCauseePosition ↔ ¬ (c.selects = .root ∧ c.bundled = true) := by
  obtain ⟨s, b⟩ := c; cases b <;> simp [CauseHead.HasCauseePosition, embeds_verb_iff]

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
  decide +kernel

end Pylkkanen2008
