module

public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Kratzer (1996): Severing the External Argument from its Verb

This file formalizes Kratzer's proposal that the external argument is not an argument of the
verb. A transitive verb denotes a relation between its internal argument and an event, and the
external argument is introduced by a separate functional head, Voice, whose denotation is a
thematic relation such as Agent. Voice and the verb phrase combine by Event Identification,
which conjoins the two at the event and leaves the introduced participant open, so that the
sentence *Mittie fed the dog* denotes the events that are feedings of the dog and of which
Mittie is the agent. Syntactically the external argument is the specifier of VoiceP, above the
verb phrase that contains the verb and its internal argument.

Because the external argument enters by Event Identification, the kind of event the verb
phrase describes constrains the role Voice can assign: an agent head is restricted to actions,
a holder head to states, and Event Identification of an agent head with a stative verb phrase
such as *own the dog* yields nothing (`agent_stative_eq_bot`).

## Implementation notes

Event Identification is `ArgumentStructure.eventIdentification`, and the agentive Voice head
is `Voice.agentive`; the derivation is stated for an arbitrary agent relation and verb. Kratzer's
Event Identification is undefined on inputs with disjoint sorts of events; the library's is
total, so the clash comes out as the empty relation. The tree is built from linearized leaf tokens,
and the paper's structural claim is its c-command relations.

## References

* [kratzer-1996]
* [marantz-1984]
-/

@[expose] public section

namespace Kratzer1996

open ArgumentStructure

section Semantics

variable {Entity E : Type*}

/-- In the denotation of *Mittie fed the dog*, Voice, denoting the agent relation, combines
with the verb phrase by Event Identification, so the agent enters above the verb. -/
def mittieFedTheDog (agent feed : Entity → E → Prop) (mittie dog : Entity) :
    E → Prop :=
  eventIdentification agent (feed dog) mittie

theorem mittieFedTheDog_iff (agent feed : Entity → E → Prop) (mittie dog : Entity)
    (e : E) : mittieFedTheDog agent feed mittie dog e ↔ agent mittie e ∧ feed dog e :=
  Iff.rfl

theorem mittieFedTheDog_congr (agent feed feed' : Entity → E → Prop) (mittie dog : Entity)
    (h : ∀ e, feed dog e ↔ feed' dog e) (e : E) :
    mittieFedTheDog agent feed mittie dog e ↔ mittieFedTheDog agent feed' mittie dog e :=
  and_congr_right fun _ ↦ h e

/-- An agent head and a stative verb phrase such as *own the dog* (25) combine by Event
Identification to the empty relation. -/
theorem agent_stative_eq_bot (IsState : E → Prop) {agent : Entity → E → Prop} {P : E → Prop}
    (hagent : ∀ x e, agent x e → ¬ IsState e) (hP : ∀ e, P e → IsState e) :
    eventIdentification agent P = ⊥ :=
  eventIdentification_eq_bot_iff.2 fun x ↦ Pi.disjoint_iff.2 fun e ↦
    Prop.disjoint_iff.2 fun h ↦ hagent x e h.1 (hP e h.2)

/-- A holder head and a stative verb phrase, (26), compose to a nonempty relation wherever there
is a state. -/
example (IsState : E → Prop) {e : E} (he : IsState e) :
    eventIdentification (fun (_ : Unit) ↦ IsState) IsState ≠ ⊥ :=
  fun h ↦ (congrFun₂ h () e).mp ⟨he, he⟩

end Semantics

section Syntax

open Minimalist SyntacticObject

/-- `voice` is agentive Voice, which subcategorizes for the verb phrase. -/
def voice : LexicalItem.Token := ⟨.of .Voice [.v] "Voice", 200⟩

/-- `little_v` is the verbalizer. -/
def little_v : LexicalItem.Token := ⟨.of .v [.V] "v", 201⟩

/-- `fed` is the verb *fed*, which subcategorizes for its internal argument. -/
def fed : LexicalItem.Token := ⟨.of .V [.D] "fed", 202⟩

/-- `mittie` is the external argument. -/
def mittie : LexicalItem.Token := ⟨.of .D [] "Mittie", 203⟩

/-- `theDog` is the internal argument. -/
def theDog : LexicalItem.Token := ⟨.of .D [] "the dog", 204⟩

/-- The tree of the sentence is `[VoiceP Mittie [Voice' Voice [vP v [VP fed [DP the dog]]]]]`. -/
def tree : LinearizedSyntacticObject := mittie * (voice * (little_v * (fed * theDog)))

theorem mittie_cCommands_theDog :
    CCommands tree (leaf mittie) (leaf theDog) ∧
      ¬ CCommands tree (leaf theDog) (leaf mittie) := by
  constructor <;> decide

theorem voice_between :
    CCommands tree (leaf voice) (leaf fed) ∧ CCommands tree (leaf mittie) (leaf voice) := by
  constructor <;> decide

theorem agentive_assignsTheta : Voice.agentive.AssignsTheta := by decide

end Syntax

end Kratzer1996
