module

public import Linglib.Semantics.Composition.Partial
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.Verbal.Voice.Denotation

/-!
# Kratzer (1996): Severing the External Argument from its Verb

Kratzer's external argument is not an argument of the verb. A transitive verb denotes a relation
between its internal argument and an event, and the external argument is introduced by a separate
functional head, Voice, whose denotation is a thematic relation such as Agent; Voice combines with
the verb phrase by Event Identification, which conjoins the two at the event and leaves the
introduced participant open. Syntactically the external argument is the specifier of VoiceP, above
the verb phrase that contains the verb and its internal argument, so it c-commands the internal
argument and not conversely (`mittie_cCommands_theDog`).

Run on the Minimalist object of *Mittie fed the dog*, the type-driven composition engine
[computes the denotation](##Kratzer1996.interp_tree) that Kratzer derives step by step, the events
of feeding the dog of which Mittie is the agent. Kratzer connects the Aktionsart of a verb with
the role of its external argument through Event Identification, which she takes to be undefined
when its inputs are restricted to disjoint sorts of eventuality. Where predicates are defined only
at the eventualities of their Aktionsart and no action is a state, an agent head and the stative
*own the dog* compose on the partial engine to a predicate [defined at no
eventuality](##Kratzer1996.agent_owns_undefined), while a holder head composes with it to one
[defined at the states](##Kratzer1996.holder_owns_defined).

## Implementation notes

* Voice denotes what `Minimalist.Voice.Head.denote` gives the agentive head, the model's agent
  relation; *feed*, *Mittie* and *the dog* denote the model's constants. The engine's eventuality
  sort `v` is Kratzer's type `s`. On the partial engine the role heads and *own* denote the model's
  relations restricted to the eventualities of their sort (`PFun.res`), as Kratzer's metalanguage
  variable for states restricts *Holder* and *own* in (26).
* The verb phrase of (21) has a non-branching V′ over *feed*. A syntactic object branches in two
  everywhere, so the verb phrase is the object *the dog* merged with *feed*.
* Kratzer's Event Identification is undefined when its inputs restrict the event to disjoint
  sorts: "there is no output function". On the total engine it is total, and an agent head with a
  stative verb phrase gives the empty relation (`agent_stative_eq_bot`). On the partial engine,
  with each predicate defined at its sort, it gives an output function defined at no eventuality.

## Errata

* (26) gives *Holder* as $\lambda x_e \lambda s_s[\mathrm{holder}(x)(e)]$, binding $s$ and using
  $e$. The study reads $\mathrm{holder}(x)(s)$.

## TODO

The partial engine's Event Identification is defined eventuality by eventuality, so an agent head
and a stative verb phrase give an output function defined nowhere where Kratzer has no output
function. An Event Identification defined only when its inputs are defined at some common
eventuality would make `agent_owns_undefined` the failure of the composition itself.

## References

* [kratzer-1996]
* [marantz-1984]
-/

@[expose] public section

namespace Kratzer1996

open Minimalist Montague PhraseStructure ArgumentStructure

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

/-- (25): *Mittie owns the dog*, with the Voice head `h`. -/
def ownsTree (h : LexicalItem.Token) : LinearizedSyntacticObject := mittie * (h * (theDog * own))

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

section Interpretation

variable {Entity V : Type} (ρ : Voice.Instruction → Entity → V → Prop) (feedRel : Entity → V → Prop)
  (m d : Entity)

/-- The lexicon of (22): *Agent* denotes as agentive Voice, and *feed*, *Mittie* and *the dog*
denote the model's constants. -/
def lex (tok : LexicalItem.Token) : Option (Denotation Entity Unit Id { eventuality := V }) :=
  if tok = agentVoice then some (Voice.agentive.denote ρ)
  else if tok = feed then some ⟨Ty.evt, feedRel⟩
  else if tok = mittie then some ⟨.e, m⟩
  else if tok = theDog then some ⟨.e, d⟩
  else none

/-- (22): the denotation the engine computes for (21), by Functional Application, Event
Identification and Functional Application, is $\lambda e[\mathrm{Agent}(\mathrm{Mittie})(e) \wedge
\mathrm{feed}(\mathrm{the\ dog})(e)]$. -/
theorem interp_tree (g : Assignment Entity) :
    (tree.toTree (·.id)).interp (lex ρ feedRel m d) g =
      some ⟨Ty.vt, fun e ↦ ρ .agent m e ∧ feedRel d e⟩ := by
  have hvp : ((LinearizedSyntacticObject.leaf theDog * .leaf feed).toTree (·.id)).interp
      (lex ρ feedRel m d) g = some ⟨Ty.vt, feedRel d⟩ := by
    simp [lex, theDog, feed, agentVoice, mittie]
  have hv := Voice.Head.interp_toTree_leaf_mul ρ (·.id) (v := agentVoice)
    (by simp [lex]) (show Voice.agentive.thematic = some .agent from rfl) rfl hvp
  rw [tree, LinearizedSyntacticObject.mul_def, LinearizedSyntacticObject.toTree_merge,
    Tree.interp_phrase_binary, LinearizedSyntacticObject.toTree_leaf, Tree.interp_terminal, hv]
  simp [lex, mittie, agentVoice, feed]
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

section Aktionsart

variable {Entity V : Type} (IsAction IsState : V → Prop) (ρ : Voice.Instruction → Entity → V → Prop)
  (ownRel : Entity → V → Prop) (m d : Entity)

/-- The partial lexicon of (25) and (26), where a role head or a verb is defined at the
eventualities of its sort: *Agent* at the actions, *Holder* and *own* at the states. -/
def partialLex (tok : LexicalItem.Token) : Option (PDenotation Entity Unit { eventuality := V }) :=
  if tok = agentVoice then
    some ⟨Ty.evt, Part.some fun x ↦ Part.some (PFun.res (ρ .agent x) {e | IsAction e})⟩
  else if tok = holderVoice then
    some ⟨Ty.evt, Part.some fun x ↦ Part.some (PFun.res (ρ .holder x) {e | IsState e})⟩
  else if tok = own then
    some ⟨Ty.evt, Part.some fun y ↦ Part.some (PFun.res (ownRel y) {e | IsState e})⟩
  else if tok = mittie then some ⟨.e, Part.some m⟩
  else if tok = theDog then some ⟨.e, Part.some d⟩
  else none

private theorem interpPartial_ownsTree (g : Assignment Entity) {h : LexicalItem.Token}
    (σ : Set V) (i : Voice.Instruction)
    (hh : partialLex IsAction IsState ρ ownRel m d h =
      some ⟨Ty.evt, Part.some fun x ↦ Part.some (PFun.res (ρ i x) σ)⟩) :
    ((ownsTree h).toTree (·.id)).interpPartial (partialLex IsAction IsState ρ ownRel m d) g =
      some (⟨Ty.vt, Part.some fun e ↦ (PFun.res (ρ i m) σ e).bind fun a ↦
        (PFun.res (ownRel d) {e | IsState e} e).map fun b ↦ a ∧ b⟩ :
          PDenotation Entity Unit { eventuality := V }) := by
  have hm : partialLex IsAction IsState ρ ownRel m d mittie = some ⟨.e, Part.some m⟩ := by
    simp [partialLex, mittie, agentVoice, holderVoice, own]
  have hd : partialLex IsAction IsState ρ ownRel m d theDog = some ⟨.e, Part.some d⟩ := by
    simp [partialLex, theDog, agentVoice, holderVoice, own, mittie]
  have ho : partialLex IsAction IsState ρ ownRel m d own =
      some ⟨Ty.evt, Part.some fun y ↦ Part.some (PFun.res (ownRel y) {e | IsState e})⟩ := by
    simp [partialLex, own, agentVoice, holderVoice]
  simp only [ownsTree, LinearizedSyntacticObject.mul_def, LinearizedSyntacticObject.toTree_merge,
    LinearizedSyntacticObject.toTree_leaf, Tree.interpPartial_phrase_binary,
    Tree.interpPartial_terminal, hm, hd, ho, hh, Option.bind_some]
  rw [Mode.combine?_evalPartial_fn_right, Option.bind_some]
  rw [Mode.combine?_evalPartial_eventIdentificationLeft, Option.bind_some,
    Mode.combine?_evalPartial_fn_right]
  rfl

/-- An agent head, defined at actions, and the stative *own the dog*, defined at states, where
Kratzer's Event Identification after (26) comes out undefined, compose on the partial engine to a
predicate defined at no eventuality when no action is a state. -/
theorem agent_owns_undefined (g : Assignment Entity) (hdisj : ∀ e, IsAction e → ¬ IsState e) :
    ∃ P : V →. Prop,
      ((ownsTree agentVoice).toTree (·.id)).interpPartial
          (partialLex IsAction IsState ρ ownRel m d) g =
        some (⟨Ty.vt, Part.some P⟩ : PDenotation Entity Unit { eventuality := V }) ∧
        ∀ e, ¬ (P e).Dom :=
  ⟨_, interpPartial_ownsTree IsAction IsState ρ ownRel m d g {e | IsAction e} .agent
    (by simp [partialLex]), fun e ⟨ha, hs⟩ ↦ hdisj e ha hs⟩

/-- (26): a holder head and *own the dog* compose to the predicate defined at the states, true of
those Mittie holds that are states of owning the dog. -/
theorem holder_owns_defined (g : Assignment Entity) :
    ∃ P : V →. Prop,
      ((ownsTree holderVoice).toTree (·.id)).interpPartial
          (partialLex IsAction IsState ρ ownRel m d) g =
        some (⟨Ty.vt, Part.some P⟩ : PDenotation Entity Unit { eventuality := V }) ∧
        (∀ e, (P e).Dom ↔ IsState e) ∧ ∀ e h, (P e).get h ↔ ρ .holder m e ∧ ownRel d e :=
  ⟨_, interpPartial_ownsTree IsAction IsState ρ ownRel m d g {e | IsState e} .holder
    (by simp [partialLex, holderVoice, agentVoice]), fun e ↦ ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, h⟩⟩,
    fun _ _ ↦ Iff.rfl⟩

end Aktionsart

end Kratzer1996
