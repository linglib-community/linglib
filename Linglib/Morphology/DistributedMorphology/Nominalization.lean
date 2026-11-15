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
Conjunction. The root is a predicate of entities, of eventualities, or a relation between the
two, as the head next to it requires. The eventive alloseme of v says that the eventuality is an
activity; the zero allosemes of v and n are the identity. The contentful allosemes of n make an
entity predicate: of a root that holds of an entity which is an event or a state, of a root that
holds of an entity, or, from a predicate of eventualities, of what such an eventuality produced.

So the complex event noun, eventive v under zero n, [stays a predicate of
eventualities](##denotations_eventive_zero), while every other reading is a predicate of
entities; the result reading [composes with either alloseme of v](##denotations_eventive_result),
and the two options differ by the activity. Which pairs of allosemes compose
[follows from their types](##composes_iff).

## Implementation notes

* The alloseme of v is the one [wood-2023] adopts when event structure is built in the
  semantics, an activity that conjoins with the root; the version with a Theme role, which that
  work calls a simplification, is not used.
* Events and states are one sort of eventuality, told apart by `stative`, and the simple event
  alloseme describes the eventualities that are not states.
* The content alloseme is that of [benz-2025]: its root is a relation between an entity and an
  eventuality, and the noun describes the entities with propositional content that stand in it.
  No alloseme of v composes with that relation other than the identity.
* A zero alloseme is the identity at the three types a root may take.

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
  /-- The root as a relation between an entity and an eventuality. -/
  | rootRel : Item .evt
  /-- Eventive v: the eventuality is an activity. -/
  | activity : Item .vt
  /-- A zero alloseme at a type. -/
  | id (a : Ty Base) : Item (a ⇒ a)
  /-- The simple event alloseme of n. -/
  | simpleEvent : Item (.et ⇒ .et)
  /-- The state alloseme of n. -/
  | state : Item (.et ⇒ .et)
  /-- The entity alloseme of n. -/
  | entity : Item (.et ⇒ .et)
  /-- The result alloseme of n. -/
  | result : Item (.vt ⇒ .et)
  /-- The content alloseme of n. -/
  | content : Item (.evt ⇒ .et)

/-- A terminal of the complex head: the root, v with its alloseme, or n with its alloseme. -/
inductive Terminal where
  | root
  | v (a : Verbalizer.Alloseme)
  | n (a : Nominalizer.Alloseme)
  deriving DecidableEq

/-- The items of a zero alloseme, the identity at each type a root takes. -/
def zeroItems : List (Σ a, Item a) := [⟨_, .id .et⟩, ⟨_, .id .vt⟩, ⟨_, .id .evt⟩]

/-- The items a terminal may be. The root takes whatever type the head next to it needs; the
allosemes of n that attach to roots have no item here. -/
def Terminal.items : Terminal → List (Σ a, Item a)
  | .root => [⟨_, .rootEntity⟩, ⟨_, .rootEvent⟩, ⟨_, .rootRel⟩]
  | .v .eventive => [⟨_, .activity⟩]
  | .v .zero => zeroItems
  | .n .zero => zeroItems
  | .n .simpleEvent => [⟨_, .simpleEvent⟩]
  | .n .state => [⟨_, .state⟩]
  | .n .entity => [⟨_, .entity⟩]
  | .n .result => [⟨_, .result⟩]
  | .n .content => [⟨_, .content⟩]
  | .n _ => []

/-- The complex head of a nominalization, the root categorized by v and then by n. -/
def nominal (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) : Skeleton Unit Terminal :=
  .binary () (.binary () (.leaf .root) (.leaf (.v v))) (.leaf (.n n))

/-- The types of the derivations of a nominalization. -/
def nominalTypes (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) : List (Ty Base) :=
  ((typeDriven nominalGrammar).derivs Terminal.items (nominal v n)).map (·.1)

/-- The allosemes `v` and `n` compose on some construal of the root. -/
def Composes (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) : Prop := nominalTypes v n ≠ []

instance : DecidableRel Composes := fun _ _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- Which allosemes compose follows from their types: eventive v gives a predicate of
eventualities, which only the zero and result allosemes of n take, and under zero v every
deverbal alloseme of n finds a root of its type. -/
theorem composes_iff (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    Composes v n ↔ (v = .eventive ∧ (n = .zero ∨ n = .result)) ∨
      (v = .zero ∧ n ≠ .relational ∧ n ≠ .sortal ∧ n ≠ .alienator) := by
  revert v n
  decide

-- The reading table and composition differ at two cells: two zero allosemes compose, to the bare
-- root, and the content alloseme does not compose with eventive v.
theorem composes_iff_reading {v : Verbalizer.Alloseme} {n : Nominalizer.Alloseme}
    (h : ¬ (v = .zero ∧ n = .zero)) (h' : ¬ (v = .eventive ∧ n = .content)) :
    Composes v n ↔ (readingFromAllosemes v n).isSome := by
  revert v n
  decide

/-! ### Denotations -/

/-- A model for nominalizations: eventualities are entities, some of them states and some
activities; `result x e` says that the entity `x` is the result of `e`, and `hasContent` picks
out the entities with propositional content. -/
structure NominalizationModel (E V : Type) where
  /-- Eventualities as entities. -/
  ev : V ↪ E
  /-- The states. -/
  stative : V → Prop
  /-- The activities. -/
  activity : V → Prop
  /-- The entity is the result of the eventuality. -/
  result : E → V → Prop
  /-- The entity has propositional content. -/
  hasContent : E → Prop

/-- What a root says of entities, of eventualities, and of an entity with an eventuality. -/
structure RootMeaning (E V : Type) where
  onEntities : E → Prop
  onEvents : V → Prop
  rel : E → V → Prop

variable {E V : Type} (m : NominalizationModel E V) (ρ : RootMeaning E V)

/-- The denotation of an item. -/
def Item.val : {a : Ty Base} → Item a → a.Domain E Unit { eventuality := V }
  | _, .rootEntity => ρ.onEntities
  | _, .rootEvent => ρ.onEvents
  | _, .rootRel => ρ.rel
  | _, .activity => m.activity
  | _, .id _ => fun x ↦ x
  | _, .simpleEvent => fun P x ↦ P x ∧ ∃ e, x = m.ev e ∧ ¬ m.stative e
  | _, .state => fun P x ↦ P x ∧ ∃ s, x = m.ev s ∧ m.stative s
  | _, .entity => fun P ↦ P
  | _, .result => fun P x ↦ ∃ e, P e ∧ m.result x e
  | _, .content => fun R x ↦ (∃ e, R x e) ∧ m.hasContent x

/-- The denotations of a nominalization, one for each of its derivations. -/
def denotations (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    List (Denotation E Unit { eventuality := V }) :=
  (typeDriven nominalGrammar).values
    (D := Ty.Dom (Base.Dom E Unit { eventuality := V })) inferInstance (Item.val m ρ)
    Terminal.items (nominal v n)

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

-- The content noun.
theorem denotations_zero_content :
    denotations m ρ .zero .content = [⟨.et, fun x ↦ (∃ e, ρ.rel x e) ∧ m.hasContent x⟩] :=
  rfl

end DistributedMorphology.Allosemy
