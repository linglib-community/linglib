module

public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Morphology.DistributedMorphology.Allosemy

/-!
# The composition of deverbal nominalizations

A deverbal noun is a complex head, a root categorized by v and then by n, and its readings are
the ways the meanings of the three compose. This file gives the allosemes of v and n their typed
denotations, after [wood-2023], as lexical items of the composition engine, and reads the
meanings of the complex head off its derivations by Functional Application and Predicate
Conjunction. A head with a zero alloseme is pruned, so that what is below it meets the next
head. The root is a predicate of entities or of eventualities, as the head next to it requires.
The eventive alloseme of v says that the eventuality is an activity. The simple event, state and
entity allosemes of n take a predicate of entities, and the result alloseme takes a predicate
of eventualities to the entities such an eventuality produced.

The complex event noun, eventive v under zero n, [is a predicate of
eventualities](##denotations_eventive_zero), and the nouns of the other allosemes of n are
predicates of entities; the result alloseme [composes over either alloseme of
v](##denotations_eventive_result), and over eventive v it adds that the eventuality was an
activity. [Which pairs of allosemes compose](##composes_iff) is read off the derivations.

## Implementation notes

* The alloseme of v is the one [wood-2023] adopts when event structure is built in the
  semantics, an activity that conjoins with the root. The version with a Theme role, which that
  work calls a simplification and [benz-2025] uses, is not an item here.
* Events and states are one sort of eventuality, told apart by `stative`: the simple event
  alloseme describes the eventualities that are not states, and nothing relates the activities
  to the states. A root that holds of states therefore conjoins with the activity, where
  [wood-2023] combines an end-state root with v by a rule of its own.
* The content alloseme of [benz-2025], and the allosemes of n that attach to roots, have no
  item, so no noun is composed with them here.
* With both heads pruned nothing is next to the root to fix its type, and the complex head has
  no bare structure.

## TODO

* The location alloseme of n of [wood-2023] has no constructor in `Nominalizer.Contentful`.
* The internal argument of a complex event noun, which [wood-2023] builds by coercing a sister
  of type `e` to a state the activity causes, is not composed here.

## References

* [wood-2023]
* [benz-2025]
-/

@[expose] public section

namespace DistributedMorphology.Allosemy

open Interpreter

/-- The rules of the complex head: Functional Application and Predicate Conjunction. -/
abbrev nominalGrammar : ManySorted.Language (Ty Base) := application.sum predicateModification

/-- The typed meanings of the terminals of a nominalization. -/
inductive Item : Ty Base → Type
  /-- The root as a predicate of entities. -/
  | rootEntity : Item .et
  /-- The root as a predicate of eventualities. -/
  | rootEvent : Item .vt
  /-- Eventive v: the eventuality is an activity. -/
  | activity : Item .vt
  /-- The simple event alloseme of n. -/
  | simpleEvent : Item (.et ⇒ .et)
  /-- The state alloseme of n. -/
  | state : Item (.et ⇒ .et)
  /-- The entity alloseme of n. -/
  | entity : Item (.et ⇒ .et)
  /-- The result alloseme of n. -/
  | result : Item (.vt ⇒ .et)

/-- A terminal of the complex head: the root, v with its alloseme, or n with its alloseme. -/
inductive Terminal where
  | root
  | v (a : Verbalizer.Alloseme)
  | n (a : Nominalizer.Alloseme)
  deriving DecidableEq

/-- The items a terminal may be. The root takes the type the head next to it needs; a zero
alloseme has no item, its head being pruned. -/
def Terminal.items : Terminal → List (Σ a, Item a)
  | .root => [⟨_, .rootEntity⟩, ⟨_, .rootEvent⟩]
  | .v .eventive => [⟨_, .activity⟩]
  | .n .simpleEvent => [⟨_, .simpleEvent⟩]
  | .n .state => [⟨_, .state⟩]
  | .n .entity => [⟨_, .entity⟩]
  | .n .result => [⟨_, .result⟩]
  | _ => []

/-- The bare structure of a nominalization, the root under the heads whose alloseme is not zero,
v below n; there is none when both are pruned. -/
def nominal : Verbalizer.Alloseme → Nominalizer.Alloseme → Option (Skeleton Unit Terminal)
  | .zero, .zero => none
  | .zero, n => some (.binary () (.leaf .root) (.leaf (.n n)))
  | v, .zero => some (.binary () (.leaf .root) (.leaf (.v v)))
  | v, n => some (.binary () (.binary () (.leaf .root) (.leaf (.v v))) (.leaf (.n n)))

/-- The types of the derivations of a nominalization. -/
def nominalTypes (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) : List (Ty Base) :=
  (nominal v n).elim [] fun s ↦ ((typeDriven nominalGrammar).derivs Terminal.items s).map (·.1)

/-- The allosemes `v` and `n` compose on some construal of the root. -/
def Composes (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) : Prop := nominalTypes v n ≠ []

instance : DecidableRel Composes := fun _ _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- Eventive v gives a predicate of eventualities, which among the allosemes of n only the
result alloseme takes, and which the noun keeps when n is pruned; with v pruned the root meets n
and takes the type it needs. -/
theorem composes_iff (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    Composes v n ↔ (v = .eventive ∧ (n = .zero ∨ n = .result)) ∨
      (v = .zero ∧ (n = .simpleEvent ∨ n = .state ∨ n = .entity ∨ n = .result)) := by
  revert v n
  decide

-- Apart from the content alloseme, which has no item, the allosemes that compose are those the
-- reading table gives a reading.
theorem composes_iff_reading {v : Verbalizer.Alloseme} {n : Nominalizer.Alloseme}
    (h : n ≠ .content) : Composes v n ↔ (readingFromAllosemes v n).isSome := by
  revert v n
  decide

/-! ### Denotations -/

/-- A model for nominalizations: eventualities are entities, some of them states and some
activities, and `result x e` says that the entity `x` is the result of `e`. -/
structure NominalizationModel (E V : Type) where
  /-- Eventualities as entities. -/
  ev : V ↪ E
  /-- The states. -/
  stative : V → Prop
  /-- The activities. -/
  activity : V → Prop
  /-- The entity is the result of the eventuality. -/
  result : E → V → Prop

/-- What a root says of entities and of eventualities. -/
structure RootMeaning (E V : Type) where
  onEntities : E → Prop
  onEvents : V → Prop

variable {E V : Type} (m : NominalizationModel E V) (ρ : RootMeaning E V)

/-- The denotation of an item. -/
def Item.val : {a : Ty Base} → Item a → a.Domain E Unit { eventuality := V }
  | _, .rootEntity => ρ.onEntities
  | _, .rootEvent => ρ.onEvents
  | _, .activity => m.activity
  | _, .simpleEvent => fun P x ↦ P x ∧ ∃ e, x = m.ev e ∧ ¬ m.stative e
  | _, .state => fun P x ↦ P x ∧ ∃ s, x = m.ev s ∧ m.stative s
  | _, .entity => fun P ↦ P
  | _, .result => fun P x ↦ ∃ e, P e ∧ m.result x e

/-- The denotations of a nominalization, one for each of its derivations. -/
def denotations (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    List (Denotation E Unit { eventuality := V }) :=
  (nominal v n).elim [] <| (typeDriven nominalGrammar).values
    (D := Ty.Dom (Base.Dom E Unit { eventuality := V })) inferInstance (Item.val m ρ)
    Terminal.items

/-- The complex event noun has the meaning of the verb, a predicate of eventualities. -/
theorem denotations_eventive_zero :
    denotations m ρ .eventive .zero = [⟨.vt, fun e ↦ ρ.onEvents e ∧ m.activity e⟩] :=
  rfl

-- The simple event noun: the entities the root holds of that are events.
theorem denotations_zero_simpleEvent :
    denotations m ρ .zero .simpleEvent =
      [⟨.et, fun x ↦ ρ.onEntities x ∧ ∃ e, x = m.ev e ∧ ¬ m.stative e⟩] :=
  rfl

-- The simple entity noun.
theorem denotations_zero_entity : denotations m ρ .zero .entity = [⟨.et, ρ.onEntities⟩] :=
  rfl

/-- The result noun built on the interpreted verb: what an activity of the root's kind
produced. -/
theorem denotations_eventive_result :
    denotations m ρ .eventive .result =
      [⟨.et, fun x ↦ ∃ e, (ρ.onEvents e ∧ m.activity e) ∧ m.result x e⟩] :=
  rfl

-- The result noun over zero v, with no activity.
theorem denotations_zero_result :
    denotations m ρ .zero .result = [⟨.et, fun x ↦ ∃ e, ρ.onEvents e ∧ m.result x e⟩] :=
  rfl

end DistributedMorphology.Allosemy
