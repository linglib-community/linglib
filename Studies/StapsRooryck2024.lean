module

public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Fragments.Romance.French.Verbs

/-!
# Staps and Rooryck (2024): Formalizing Spatial-Causal Polysemy of Agent Prepositions

Staps and Rooryck analyze the French agent prepositions *par* and *de*. Against accounts on
which the agent preposition of a passive is a vacuous case marker, they give each preposition one
polymorphically typed denotation, in the sense of Tyler and Evans's principled polysemy,
instantiated by the syntactic context. In causal adjuncts, in Copley and Harley's force-theoretic
frame, *de* names a causing situation and *par* a force. In passives the by-phrase is the
external argument of Angelopoulos, Collins and Terzi, combined with the verb by Event
Identification. The agentive instantiations share the at-issue relation Initiator and differ in
presupposition, high proto-agentivity for *par* and low for *de*, where proto-agentivity is
relational in the terms of Dowty and of Hopper and Thompson: bringing about a change,
volitionality and telicity, with change primary. Over the fragment's verbs this derives the
paper's readings, such as the exclusion of *de* by verbs of change.

## Main definitions

* `parCausal`: *par* in a causal adjunct.
* `deCausal`: *de* in a causal adjunct.
* `parAgentive`: *par* in a passive.
* `deAgentive`: *de* in a passive.
* `Construal`: the agent's relation to the event, ordered by proto-agentivity.

## Main results

* `parCausal_net_of_deCausal`: a cause *de* names is, through its net force, one *par* names.
* `voicePass_eventIdentification`: passive Voice's closure is redundant under a by-phrase.
* `change_verbs_exclude_de`: verbs of change exclude *de*.
* `psych_verbs_allow_both`: psych verbs allow both prepositions.
* `dependsOnProximate_of_dependsOnDistal`: an effect depends on a distal cause only where it
  depends on the proximate one.

## Implementation notes

The paper gives no threshold between high and low proto-agentivity and reports an informal
survey of twenty-one speakers on a six-point scale only to confirm its judgments; the means
it reports are not reproduced. Change on a contextually inferred scale, which lets the psych
verbs take *par* when the emotion has effects, is beyond the lexical construals and is not
formalized. The stative/dynamic contrast, which the paper finds never decisive on its own,
is not a coordinate of `Construal`. Straub's generalization that non-stative verbs
take *par*, stative verbs with animate agents either preposition and stative verbs with
inanimate agents *de* is described in the paper as too coarse, since a stative verb with an
inanimate agent allows *par* when a change on an inferred scale is at stake.

## References

* [staps-rooryck-2024]
* [tyler-evans-2003]
* [croft-2012]
* [copley-harley-2015]
* [copley-harley-2022]
* [angelopoulos-collins-terzi-2020]
* [kratzer-1996]
* [dowty-1991]
* [hopper-thompson-1980]
* [straub-1974]
* [halpern-pearl-2005]
-/

@[expose] public section

namespace StapsRooryck2024

open ArgumentStructure French.Verbs

/-! ### Polymorphic types -/

/-- The domain types of the paper's type system are entities, situations and forces. -/
inductive SemDomain
  | e
  | s
  | f
  deriving DecidableEq, Repr

/-- A preposition type `⟨η, ⟨θ, t⟩⟩` pairs the domain of the ground with the domain of the
figure. -/
structure PrepType where
  ground : SemDomain
  figure : SemDomain
  deriving DecidableEq, Repr

universe u

/-- `Dom` interprets the domain types in the force-theoretic frame of [copley-harley-2022], where a
force is a function from situations to situations. -/
def Dom (Entity S : Type u) : SemDomain → Type u
  | .e => Entity
  | .s => S
  | .f => S → S

/-- A relation of type `⟨η, ⟨θ, t⟩⟩` relates a ground to a figure. -/
abbrev Rel (Entity S : Type u) (t : PrepType) : Type u :=
  Dom Entity S t.ground → Dom Entity S t.figure → Prop

/-! ### Causal adjuncts -/

section Causal

variable {Entity S : Type u} (net : S → S → S)

/-- *par* in a causal adjunct, at type `⟨f, ⟨s, t⟩⟩` (14b), holds when the situation comes about
through the force, the net force of some situation the force maps to it. -/
def parCausal : Rel Entity S ⟨.f, .s⟩ := fun f s ↦ ∃ s₀, net s₀ = f ∧ f s₀ = s

/-- *de* in a causal adjunct, at type `⟨s, ⟨s, t⟩⟩` (15b), holds when the situation arises from
the causing situation, whose net force maps it to the situation. -/
def deCausal : Rel Entity S ⟨.s, .s⟩ := fun s s' ↦ net s s = s'

/-- A cause *de* names as a situation is, through its net force, a cause *par* names as a
force, so both prepositions describe the same causal event. -/
theorem parCausal_net_of_deCausal {s s' : S} (h : deCausal (Entity := Entity) net s s') :
    parCausal (Entity := Entity) net (net s) s' :=
  ⟨s, rfl, h⟩

end Causal

/-! ### By-phrases in passives -/

section Passive

variable {Entity E : Type*}

/-- The by-phrase (10b) is the agentive instantiation applied to its argument, a predicate of
events at type `⟨s, t⟩`. -/
def byPhrase (init : Entity → E → Prop) (x : Entity) : E → Prop := init x

/-- Passive Voice (9b) is the existential closure of the external argument. -/
def voicePass (p : Entity → E → Prop) : E → Prop := fun e ↦ ∃ x, p x e

/-- In (10) the by-phrase combines with the verb's denotation by Event Identification and the
closure passive Voice performs is redundant, since the by-phrase supplies the initiator. -/
theorem voicePass_eventIdentification (init : Entity → E → Prop) (body : E → Prop)
    (j : Entity) (e : E) :
    voicePass (eventIdentification (fun x e ↦ init x e ∧ body e) (byPhrase init j)) e ↔
      init j e ∧ body e :=
  ⟨fun ⟨_, ⟨_, hb⟩, hj⟩ ↦ ⟨hj, hb⟩, fun ⟨hj, hb⟩ ↦ ⟨j, ⟨hj, hb⟩, hj⟩⟩

open Classical in
/-- *par* in a passive (35a) is the initiator relation, presupposing high proto-agentivity of
the agent in the event. The evaluation point of the trivalent proposition is the event. -/
noncomputable def parAgentive (init : Entity → E → Prop) (High : Entity → E → Prop)
    (x : Entity) : E → SignType :=
  {e | High x e}.indicator fun e ↦ SignType.ofProp (init x e)

open Classical in
/-- *de* in a passive (35b) is the initiator relation, presupposing low proto-agentivity. -/
noncomputable def deAgentive (init : Entity → E → Prop) (High : Entity → E → Prop)
    (x : Entity) : E → SignType :=
  {e | ¬ High x e}.indicator fun e ↦ SignType.ofProp (init x e)

variable (init : Entity → E → Prop) (High : Entity → E → Prop) (x : Entity)

/-- The two prepositions share their at-issue content, each being the initiator relation
wherever it is defined. -/
theorem agentive_eq_one_iff_of_ne_zero (e : E) :
    (parAgentive init High x e ≠ 0 → (parAgentive init High x e = 1 ↔ init x e)) ∧
      (deAgentive init High x e ≠ 0 → (deAgentive init High x e = 1 ↔ init x e)) := by
  simp_all [parAgentive, deAgentive]

/-- Their presuppositions are complementary. -/
theorem parAgentive_ne_zero_iff (e : E) :
    parAgentive init High x e ≠ 0 ↔ deAgentive init High x e = 0 := by
  simp [parAgentive, deAgentive]

end Passive

/-! ### Proto-agentivity -/

/-- A construal records the agent's relation to the event by the relational proto-agentivity
properties the paper finds decisive, bringing about a change, volitionality and telicity. -/
structure Construal where
  change : Bool
  volition : Bool
  telic : Bool
  deriving DecidableEq, Repr, Fintype

namespace Construal

/-- In the order of proto-agentivity (34), change is primary, and among construals agreeing
on change, more volitionality or telicity is more proto-agentive. -/
protected def LE (c d : Construal) : Prop :=
  (c.change = true → d.change = true) ∧
    (c.change = d.change →
      (c.volition = true → d.volition = true) ∧ (c.telic = true → d.telic = true))

instance : LE Construal := ⟨Construal.LE⟩

instance (c d : Construal) : Decidable (c ≤ d) := by
  change Decidable (Construal.LE c d); unfold Construal.LE; infer_instance

instance : PartialOrder Construal where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLT Construal := decidableLTOfDecidableLE

/-- By (34a), a construal bringing about a change is more proto-agentive than any that does
not, whatever their volitionality and telicity. -/
theorem lt_of_change : ∀ c d : Construal, c.change = false → d.change = true → c < d := by
  decide

/-- By (34b), among construals that bring about no change, proto-agentivity is volitionality
and telicity. -/
theorem le_iff_of_not_change :
    ∀ c d : Construal, c.change = false → d.change = false →
      (c ≤ d ↔ (c.volition = true → d.volition = true) ∧ (c.telic = true → d.telic = true)) := by
  decide

end Construal

/-- The construal a verb entry lexicalizes reads change off the subject's causation entailment,
volitionality off its volition entailment, and telicity off the Vendler class. -/
def construal (v : Verb) : Construal :=
  let p := (v.slotProfile? .external).getD ∅
  ⟨decide (.causation ∈ p), decide (.volition ∈ p),
    decide ((v.vendlerClass.map Aspect.VendlerClass.telicity).getD .atelic = .telic)⟩

/-- *Par* selects a sense whose construal is at least as proto-agentive as that of every
sense the verb makes available. -/
def ParSelects (senses : List Verb) (v : Verb) : Prop :=
  ∀ u ∈ senses, construal u ≤ construal v

/-- *De* selects a sense whose construal brings about no change and is at most as
proto-agentive as that of every sense the verb makes available. -/
def DeSelects (senses : List Verb) (v : Verb) : Prop :=
  (construal v).change = false ∧ ∀ u ∈ senses, construal v ≤ construal u

instance (senses : List Verb) (v : Verb) :
    Decidable (ParSelects senses v) := by
  unfold ParSelects; infer_instance

instance (senses : List Verb) (v : Verb) :
    Decidable (DeSelects senses v) := by
  unfold DeSelects; infer_instance

/-- The prototypically transitive verbs of Table 1 bring about a change and exclude *de*. -/
theorem change_verbs_exclude_de :
    ∀ v ∈ [laver, briser, ecrire, construire, tuer], ParSelects [v] v ∧ ¬ DeSelects [v] v := by
  decide

/-- The psych verbs of Table 1 bring about no change and allow both prepositions. -/
theorem psych_verbs_allow_both :
    ∀ v ∈ [aimer, adorer, respecter], ParSelects [v] v ∧ DeSelects [v] v := by
  decide

/-- The two senses of *suivre* are goal-directed following and the positional relation. -/
def suivreSenses : List Verb := [suivreDyn, suivreStat]

/-- *Par* selects the volitional sense of *suivre* (25b). -/
theorem par_suivre : ParSelects suivreSenses suivreDyn ∧ ¬ ParSelects suivreSenses suivreStat := by
  decide

/-- *De* selects the positional sense of *suivre* (26a). -/
theorem de_suivre : DeSelects suivreSenses suivreStat ∧ ¬ DeSelects suivreSenses suivreDyn := by
  decide

/-- The two senses of *abandonner* are the telic abandoning and the stative neglect. -/
def abandonnerSenses : List Verb := [abandonner, abandonnerStat]

/-- *Par* selects the telic sense of *abandonner* (31a). -/
theorem par_abandonner :
    ParSelects abandonnerSenses abandonner ∧ ¬ ParSelects abandonnerSenses abandonnerStat := by
  decide

/-- *De* selects the atelic sense of *abandonner* (31b). -/
theorem de_abandonner :
    DeSelects abandonnerSenses abandonnerStat ∧ ¬ DeSelects abandonnerSenses abandonner := by
  decide

/-! ### Causal distance -/

section CausalModel

variable {P Q X Y Z : Type*} (g : P → X → Y) (h : Q → Y → Z)

/-- In the causal model (36), where `Y` depends on `X` and `Z` on `Y`, the effect depends on
the distal cause in a case when another value of the distal cause changes it. -/
def DependsOnDistal (p : P) (q : Q) (x : X) : Prop := ∃ x', h q (g p x') ≠ h q (g p x)

/-- The effect depends on the proximate cause in a case when another value of it changes the
effect. -/
def DependsOnProximate (p : P) (q : Q) (x : X) : Prop := ∃ y', h q y' ≠ h q (g p x)

/-- The cases in which the effect depends on the distal cause are among those in which it
depends on the proximate cause. Greater causal distance means less dependency, which the
paper offers as a reason the ablative *de* marks low proto-agentivity. -/
theorem dependsOnProximate_of_dependsOnDistal {p : P} {q : Q} {x : X}
    (hd : DependsOnDistal g h p q x) : DependsOnProximate g h p q x :=
  let ⟨x', hx⟩ := hd; ⟨g p x', hx⟩

end CausalModel

end StapsRooryck2024
