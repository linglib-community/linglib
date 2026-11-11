module

public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.SyntacticObject.ToTree
public import Linglib.Syntax.Minimalist.Verbal.Voice.Denotation
public import Mathlib.Data.PFun

/-!
# Kratzer (1996): Severing the External Argument from its Verb

Kratzer's external argument is not an argument of the verb. A transitive verb denotes a relation
between its internal argument and an event, and the external argument is introduced by a separate
functional head, Voice, whose denotation is a thematic relation such as Agent; Voice combines with
the verb phrase by Event Identification, which conjoins the two at the event and leaves the
introduced participant open. Syntactically the external argument is the specifier of VoiceP, above
the verb phrase that contains the verb and its internal argument, so it c-commands the internal
argument and not conversely (`mittie_cCommands_theDog`).

The Minimalist object of *Mittie fed the dog*, interpreted by Functional Application and Event
Identification, [means](##Kratzer1996.meanings_tree) what Kratzer derives step by step, the
events of feeding the dog of which Mittie is the agent. Kratzer connects the Aktionsart of a verb
with the role of its external argument through Event Identification, which she takes to be
undefined when its inputs are restricted to disjoint sorts of eventuality. Where predicates are
partial functions defined only at the eventualities of their Aktionsart and no action is a state,
Event Identification applies to an agent head and the stative *own the dog* and [has no
value](##Kratzer1996.agent_owns_undefined), while with a holder head it [has
one](##Kratzer1996.holder_owns_defined), defined at the states.

## Implementation notes

* Voice denotes what `Minimalist.Voice.Head.denote` gives the agentive head, the model's agent
  relation; *feed*, *Mittie* and *the dog* denote the model's constants. The eventuality sort
  `v` is Kratzer's type `s`.
* The verb phrase of (21) has a non-branching V′ over *feed*. A syntactic object branches in two
  everywhere, so the verb phrase is the object *the dog* merged with *feed*.
* For (25) and (26) a predicate of eventualities is a partial function, of type `⟨v,M t⟩`, and
  the role heads and *own* denote the model's relations restricted to the eventualities of their
  sort (`PFun.res`), as Kratzer's metalanguage variable for states restricts *Holder* and *own*
  in (26). Event Identification is then itself partial, the rule `Identification`: it has a
  value when its two inputs are defined at some common eventuality, which is how "there is no
  output function" is read. The results are stated of Voice′, the constituent the rule builds.
* With total predicates Event Identification is total, and an agent head with a stative verb
  phrase gives the empty relation (`agent_stative_eq_bot`).

## References

* [kratzer-1996]
* [marantz-1984]
-/

@[expose] public section

namespace Kratzer1996

open Minimalist Interpreter ArgumentStructure

/-! ### The objects -/

/-- *Agent*, agentive Voice, which selects the verb phrase. -/
def agentVoice : LexicalItem.Token := ⟨.of .Voice [.V] "Agent", 200⟩

/-- *Holder*, the Voice head of a stative verb phrase (26). -/
def holderVoice : LexicalItem.Token := ⟨.of .Voice [.V] "Holder", 201⟩

/-- *feed*, which selects its internal argument. -/
def feed : LexicalItem.Token := ⟨.of .V [.D] "feed", 202⟩

/-- *own*, which selects its internal argument. -/
def own : LexicalItem.Token := ⟨.of .V [.D] "own", 203⟩

/-- *Mittie*, the external argument. -/
def mittie : LexicalItem.Token := ⟨.of .D [] "Mittie", 204⟩

/-- *the dog*, the internal argument. -/
def theDog : LexicalItem.Token := ⟨.of .D [] "the dog", 205⟩

/-- (21): `[VoiceP Mittie [Voice′ Agent [VP the dog feed]]]`. -/
def tree : LinearizedSyntacticObject := mittie * (agentVoice * (theDog * feed))

/-- (25): the Voice′ of *Mittie owns the dog*, the Voice head `h` merged with *own the dog*. -/
def ownsBar (h : LexicalItem.Token) : LinearizedSyntacticObject := h * (theDog * own)

section Syntax

open SyntacticObject

theorem mittie_cCommands_theDog :
    CCommands tree (leaf mittie) (leaf theDog) ∧
      ¬ CCommands tree (leaf theDog) (leaf mittie) := by
  constructor <;> decide

theorem voice_between :
    CCommands tree (leaf agentVoice) (leaf feed) ∧
      CCommands tree (leaf mittie) (leaf agentVoice) := by
  constructor <;> decide

end Syntax

/-! ### The interpretation of (21) -/

/-- The words of (21), by semantic type. -/
inductive Word : Ty Base → Type
  | agent : Word .evt
  | feed : Word .evt
  | mittie : Word .e
  | theDog : Word .e

/-- The word each token of (21) is. -/
def lexicon : List (LexicalItem.Token × Σ a, Word a) :=
  [(agentVoice, ⟨_, .agent⟩), (feed, ⟨_, .feed⟩), (mittie, ⟨_, .mittie⟩),
    (theDog, ⟨_, .theDog⟩)]

/-- The entries of a leaf in a list of tokens with their entries, and none for a trace. -/
def entries {W : Ty Base → Type} (lex : List (LexicalItem.Token × Σ a, W a)) :
    LexicalItem.Token ⊕ ℕ → List (Σ a, W a)
  | .inl tok => lex.filterMap fun (t, w) ↦ if t.id = tok.id then some w else none
  | .inr _ => []

section Interpretation

variable {Entity V : Type} (ρ : Voice.Instruction → Entity → V → Prop) (feedRel : Entity → V → Prop)
  (m d : Entity)

/-- The lexicon of (22): *Agent* denotes as agentive Voice, and *feed*, *Mittie* and *the dog*
denote the model's constants. -/
def Word.val : {a : Ty Base} → Word a → a.Domain Entity Unit { eventuality := V }
  | _, .agent => Voice.agentive.denote ρ
  | _, .feed => feedRel
  | _, .mittie => m
  | _, .theDog => d

/-- The meanings of a syntactic object by Functional Application, Predicate Modification and
Event Identification. -/
def meanings (t : LinearizedSyntacticObject) :
    List (Denotation Entity Unit { eventuality := V }) :=
  match (t.toTree (·.id)).skeleton (fun _ ↦ false) with
  | some s => (typeDriven Voice.grammar).values
      (D := Ty.Dom (Base.Dom Entity Unit { eventuality := V })) inferInstance
      (Word.val ρ feedRel m d)
      (entries lexicon) s
  | none => []

/-- (22): the one meaning of (21), by Functional Application, Event Identification and Functional
Application, is $\lambda e[\mathrm{Agent}(\mathrm{Mittie})(e) \wedge
\mathrm{feed}(\mathrm{the\ dog})(e)]$. -/
theorem meanings_tree :
    meanings ρ feedRel m d tree = [⟨.vt, fun e ↦ ρ .agent m e ∧ feedRel d e⟩] :=
  rfl

-- An agent head and a stative verb phrase such as *own the dog* (25) combine by the total Event
-- Identification to the empty relation.
theorem agent_stative_eq_bot (IsState : V → Prop) {agent : Entity → V → Prop} {P : V → Prop}
    (hagent : ∀ x e, agent x e → ¬ IsState e) (hP : ∀ e, P e → IsState e) :
    eventIdentification agent P = ⊥ :=
  eventIdentification_eq_bot_iff.2 fun x ↦ Pi.disjoint_iff.2 fun e ↦
    Prop.disjoint_iff.2 fun h ↦ hagent x e h.1 (hP e h.2)

end Interpretation

/-! ### Aktionsart and the external argument, (25)–(26) -/

/-- The type of a predicate of eventualities that is a partial function. -/
abbrev pvt : Ty Base := .v ⇒ .comp .M .t

/-- Kratzer's Event Identification (23) on partial predicates, "order irrelevant": a relation of
individuals to eventualities and a predicate of eventualities give a relation, if any. -/
inductive Identification : Ty Base → Ty Base → Ty Base → Type
  /-- The relation on the left. -/
  | left : Identification (.e ⇒ pvt) pvt (.comp .M (.e ⇒ pvt))
  /-- The relation on the right. -/
  | right : Identification pvt (.e ⇒ pvt) (.comp .M (.e ⇒ pvt))

/-- The output of Event Identification is defined when its inputs are defined at some common
eventuality, and conjoins them there. -/
def identify {X E : Type} (f : X → E →. Prop) (g : E →. Prop) : Part (X → E →. Prop) :=
  ⟨∃ x e, (f x e).Dom ∧ (g e).Dom, fun _ x e ↦ (f x e).bind fun a ↦ (g e).map fun b ↦ a ∧ b⟩

/-- The meaning of Kratzer's Event Identification. -/
def Identification.eval (D : Base → Type) :
    {l r u : Ty Base} → Identification l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .left, f, g => identify f g
  | _, _, _, .right, g, f => identify f g

/-- The rule of Event Identification that applies to two types. -/
def Identification.rules (l r : Ty Base) : List (Σ u, Identification l r u) :=
  (if h : l = (.e ⇒ pvt) ∧ r = pvt then
    [⟨.comp .M (.e ⇒ pvt), by obtain ⟨rfl, rfl⟩ := h; exact .left⟩]
  else []) ++
  if h : l = pvt ∧ r = (.e ⇒ pvt) then
    [⟨.comp .M (.e ⇒ pvt), by obtain ⟨rfl, rfl⟩ := h; exact .right⟩]
  else []

/-- Kratzer's Event Identification, as a language over the types. -/
@[reducible] def identification : ManySorted.Language (Ty Base) :=
  .mk₂ (fun _ _ ↦ PEmpty) Identification

instance (D : Base → Type) : identification.Structure (Ty.Dom D) :=
  .mk₂ nofun (Identification.eval D)

instance : identification.LocallyFinite :=
  .mk₂ (fun _ ↦ []) Identification.rules nofun fun m ↦ by
    cases m <;> simp [Identification.rules]

/-- The grammar of Functional Application and Kratzer's Event Identification. -/
abbrev partialGrammar : ManySorted.Language (Ty Base) := application.sum identification

/-- The words of (25) and (26), by semantic type. -/
inductive PWord : Ty Base → Type
  | agent : PWord (.e ⇒ pvt)
  | holder : PWord (.e ⇒ pvt)
  | own : PWord (.e ⇒ pvt)
  | theDog : PWord .e

/-- The word each token of (25) and (26) is. -/
def partialLexicon : List (LexicalItem.Token × Σ a, PWord a) :=
  [(agentVoice, ⟨_, .agent⟩), (holderVoice, ⟨_, .holder⟩), (own, ⟨_, .own⟩),
    (theDog, ⟨_, .theDog⟩)]

section Aktionsart

variable {Entity V : Type} (IsAction IsState : V → Prop) (ρ : Voice.Instruction → Entity → V → Prop)
  (ownRel : Entity → V → Prop) (d : Entity)

/-- The partial lexicon of (25) and (26), where a role head or a verb is defined at the
eventualities of its sort: *Agent* at the actions, *Holder* and *own* at the states. -/
def PWord.val : {a : Ty Base} → PWord a → a.Domain Entity Unit { eventuality := V }
  | _, .agent => fun x ↦ PFun.res (ρ .agent x) {e | IsAction e}
  | _, .holder => fun x ↦ PFun.res (ρ .holder x) {e | IsState e}
  | _, .own => fun y ↦ PFun.res (ownRel y) {e | IsState e}
  | _, .theDog => d

/-- The meanings of a syntactic object by Functional Application and Kratzer's Event
Identification, over partial predicates. -/
def partialMeanings (t : LinearizedSyntacticObject) :
    List (Denotation Entity Unit { eventuality := V }) :=
  match (t.toTree (·.id)).skeleton (fun _ ↦ false) with
  | some s => (typeDriven partialGrammar).values
      (D := Ty.Dom (Base.Dom Entity Unit { eventuality := V })) inferInstance
      (PWord.val IsAction IsState ρ ownRel d) (entries partialLexicon) s
  | none => []

/-- An agent head, defined at actions, and the stative *own the dog*, defined at states: Event
Identification applies and, when no action is a state, has no value. "Given the two input
functions, there is no output function of the required kind." -/
theorem agent_owns_undefined (hdisj : ∀ e, IsAction e → ¬ IsState e) :
    ∃ P, partialMeanings IsAction IsState ρ ownRel d (ownsBar agentVoice) =
        [⟨.comp .M (.e ⇒ pvt), P⟩] ∧ ¬ P.Dom :=
  ⟨_, rfl, fun ⟨_, e, ha, hs⟩ ↦ hdisj e ha hs⟩

/-- (26): a holder head and *own the dog* are both defined at the states, so where there is a
state Event Identification has a value: the relation defined at the states, true of an individual
and a state it holds that is one of owning the dog. -/
theorem holder_owns_defined (x : Entity) {s : V} (hs : IsState s) :
    ∃ P, partialMeanings IsAction IsState ρ ownRel d (ownsBar holderVoice) =
        [⟨.comp .M (.e ⇒ pvt), P⟩] ∧ ∃ h : P.Dom, ∀ y e,
          ((P.get h y e).Dom ↔ IsState e) ∧
            ∀ h', (P.get h y e).get h' ↔ ρ .holder y e ∧ ownRel d e :=
  ⟨_, rfl, ⟨x, s, hs, hs⟩, fun _ _ ↦ ⟨⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, h⟩⟩, fun _ ↦ Iff.rfl⟩⟩

end Aktionsart

end Kratzer1996
