module

public import Linglib.Semantics.Composition.Sorts
public import Linglib.Morphology.DistributedMorphology.Allosemy

/-!
# The meanings of the terminals of a nominalization

A deverbal noun is a complex head, a root categorized by v and then by n, and its readings are
the ways the meanings of the three compose. This file gives the terminals their typed
denotations, the lexical items a composition reads. The root is a predicate of entities or of
eventualities, as the head next to it requires. Eventive v has two denotations in the
literature: the activity of [wood-2023], which conjoins with the root, and the Theme role of
that work's simpler version and of [benz-2025], which takes the root to a relation between an
entity and an eventuality. The simple event, state and entity allosemes of n take a predicate of
entities; the result alloseme takes a predicate of eventualities to the entities such an
eventuality produced; and the content alloseme of [benz-2025] takes a relation to the entities
with propositional content that stand in it. A head with a zero alloseme has no item and is
pruned (`Categorizer.IsZero`).

## Implementation notes

* Events and states are one sort of eventuality, told apart by `stative`: the simple event
  alloseme describes the eventualities that are not states, and nothing relates the activities
  to the states.
* The root as a relation is not a construal [wood-2023] gives it. It is here for the content
  alloseme over a pruned v, whose printed denotation applies the root to an entity and an
  eventuality.

## TODO

* The location alloseme of n of [wood-2023] has no constructor in `Nominalizer.Contentful`.

## References

* [wood-2023]
* [benz-2025]
-/

@[expose] public section

namespace DistributedMorphology.Allosemy

open Interpreter

/-- A categorizer of a nominalization with its alloseme. -/
inductive Categorizer where
  | v (a : Verbalizer.Alloseme)
  | n (a : Nominalizer.Alloseme)
  deriving DecidableEq, Repr

/-- A categorizer whose alloseme is zero, which is pruned before interpretation. -/
def Categorizer.IsZero : Categorizer → Prop
  | .v a => a = .zero
  | .n a => a = .zero

instance : DecidablePred Categorizer.IsZero
  | .v _ => inferInstanceAs (Decidable (_ = _))
  | .n _ => inferInstanceAs (Decidable (_ = _))

/-- The typed meanings of the terminals of a nominalization. -/
inductive Item : Ty Base → Type
  /-- The root as a predicate of entities. -/
  | rootEntity : Item .et
  /-- The root as a predicate of eventualities. -/
  | rootEvent : Item .vt
  /-- The root as a relation between an entity and an eventuality. -/
  | rootRel : Item .evt
  /-- Eventive v as an activity. -/
  | activity : Item .vt
  /-- Eventive v as the Theme role. -/
  | theme : Item (.vt ⇒ .evt)
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

/-- The item of an alloseme of n; the zero alloseme and those that attach to roots have none. -/
def Nominalizer.Alloseme.items : Nominalizer.Alloseme → List (Σ a, Item a)
  | .simpleEvent => [⟨_, .simpleEvent⟩]
  | .state => [⟨_, .state⟩]
  | .entity => [⟨_, .entity⟩]
  | .result => [⟨_, .result⟩]
  | .content => [⟨_, .content⟩]
  | _ => []

/-- A model for nominalizations: eventualities are entities, some of them states and some
activities; `theme x e` says that `x` is the theme of `e`, `result x e` that `x` is the result
of `e`, and `hasContent` picks out the entities with propositional content. -/
structure NominalizationModel (E V : Type) where
  /-- Eventualities as entities. -/
  ev : V ↪ E
  /-- The states. -/
  stative : V → Prop
  /-- The activities. -/
  activity : V → Prop
  /-- The entity is the theme of the eventuality. -/
  theme : E → V → Prop
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
  | _, .theme => fun P x e ↦ P e ∧ m.theme x e
  | _, .simpleEvent => fun P x ↦ P x ∧ ∃ e, x = m.ev e ∧ ¬ m.stative e
  | _, .state => fun P x ↦ P x ∧ ∃ s, x = m.ev s ∧ m.stative s
  | _, .entity => fun P ↦ P
  | _, .result => fun P x ↦ ∃ e, P e ∧ m.result x e
  | _, .content => fun R x ↦ (∃ e, R x e) ∧ m.hasContent x

end DistributedMorphology.Allosemy
