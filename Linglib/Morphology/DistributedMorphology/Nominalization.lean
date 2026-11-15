module

public import Mathlib.Logic.Embedding.Basic
public import Linglib.Morphology.DistributedMorphology.Allosemy

/-!
# The meanings of deverbal nominalizations

This file gives the allosemes of v and n their denotations, after [wood-2023]. Eventualities
are a subtype of entities, so a noun can describe an event as a thing. The eventive alloseme of
v turns the root into an event predicate with a Theme position, and its zero alloseme passes the
root up untouched (`denoteV`). Each alloseme of n then builds an entity predicate from what v
hands it (`denoteN`): the zero alloseme keeps the verb's meaning and its Theme position, the
complex event reading, while the contentful ones describe an event, a state, a plain entity, the
result of an event, or, after [benz-2025], something with propositional content. A noun
[has a Theme position only if v is eventive](##internalArg_eq_none_of_zero), and the
combinations that compose are [exactly those with a reading](##isSome_denoteN_iff).

## Implementation notes

* The complex event reading is stated of entities through the embedding of eventualities, where
  [wood-2023] states it of events.
* The result alloseme composes with either alloseme of v, the two options [benz-2025] leaves
  open; with eventive v the noun keeps the Theme position.
* With zero v, the event predicate and the Theme relation of the content reading are the
  root's.

## TODO

* The location alloseme of n of [wood-2023], which relates an entity to the place of an event,
  has no constructor in `Nominalizer.Contentful`.

## References

* [wood-2023]
* [benz-2025]
-/

@[expose] public section

namespace DistributedMorphology.Allosemy

variable {E S : Type*}

/-- A model for nominalization denotations: eventualities are entities, some of them states;
`result x e` says that the entity `x` is the result of the eventuality `e`, and `hasContent`
picks out the entities with propositional content. -/
structure NominalizationModel (E S : Type*) where
  /-- Eventualities as entities. -/
  ev : S ↪ E
  /-- The stative eventualities. -/
  stative : S → Prop
  /-- The entity is the result of the eventuality. -/
  result : E → S → Prop
  /-- The entity has propositional content, as a rumor, an idea or a claim does. -/
  hasContent : E → Prop

/-- What a root contributes to a nominalization: what it says of entities, what it says of
eventualities, and its Theme relation between an entity and an eventuality of its kind. -/
structure RootMeaning (E S : Type*) where
  onEntities : E → Prop
  onEvents : S → Prop
  theme : E → S → Prop

/-- What v hands to n: under the eventive alloseme an event predicate with the Theme position v
introduces, and under the zero alloseme the root untouched, with no argument position. -/
inductive VerbalDenotation (E S : Type*) where
  | eventive (p : S → Prop) (theme : E → S → Prop)
  | zero (ρ : RootMeaning E S)

/-- `denoteV ρ a` applies the alloseme `a` of v to the root `ρ`. -/
def denoteV (ρ : RootMeaning E S) : Verbalizer.Alloseme → VerbalDenotation E S
  | .eventive => .eventive ρ.onEvents ρ.theme
  | .zero => .zero ρ

/-- The denotation of a noun: the entities it describes, and the relation of its internal
argument when it has one. -/
structure NominalDenotation (E S : Type*) where
  /-- What the noun describes. -/
  pred : E → Prop
  /-- `internalArg y x` says that `y` fills the Theme position of the noun `x`, as *the sky* does
  in *the observation of the sky*. -/
  internalArg : Option (E → E → Prop) := none

/-- `denoteN m d a` applies the alloseme `a` of n to what v hands it, and is `none` where the two
do not compose. Over eventive v the zero alloseme describes the verb's events and keeps its
Theme position. Over zero v the simple event and state allosemes describe an event or a state
of which the root holds as an entity, the entity alloseme whatever the root holds of, and the
result alloseme what an event of the root's kind produced. The content alloseme describes the
Theme of such an event that has propositional content. -/
def denoteN (m : NominalizationModel E S) :
    VerbalDenotation E S → Nominalizer.Alloseme → Option (NominalDenotation E S)
  | .eventive p θ, .zero =>
      some { pred := fun x ↦ ∃ e, x = m.ev e ∧ p e
             internalArg := some fun y x ↦ ∃ e, x = m.ev e ∧ p e ∧ θ y e }
  | .eventive p θ, .result =>
      some { pred := fun x ↦ ∃ e, p e ∧ m.result x e
             internalArg := some fun y x ↦ ∃ e, p e ∧ θ y e ∧ m.result x e }
  | .eventive p θ, .content => some { pred := fun x ↦ (∃ e, p e ∧ θ x e) ∧ m.hasContent x }
  | .zero ρ, .simpleEvent =>
      some { pred := fun x ↦ ρ.onEntities x ∧ ∃ e, x = m.ev e ∧ ¬ m.stative e }
  | .zero ρ, .state => some { pred := fun x ↦ ρ.onEntities x ∧ ∃ s, x = m.ev s ∧ m.stative s }
  | .zero ρ, .result => some { pred := fun x ↦ ∃ e, ρ.onEvents e ∧ m.result x e }
  | .zero ρ, .entity => some { pred := ρ.onEntities }
  | .zero ρ, .content =>
      some { pred := fun x ↦ (∃ e, ρ.onEvents e ∧ ρ.theme x e) ∧ m.hasContent x }
  | _, _ => none

variable {m : NominalizationModel E S} {ρ : RootMeaning E S} {v : Verbalizer.Alloseme}
  {n : Nominalizer.Alloseme} {r : NominalDenotation E S}

/-- A noun over the zero alloseme of v has no Theme position: only v introduces one. -/
theorem internalArg_eq_none_of_zero (h : denoteN m (denoteV ρ .zero) n = some r) :
    r.internalArg = none := by
  rcases n with _ | cn
  · simp [denoteV, denoteN] at h
  · cases cn <;> simp only [denoteV, denoteN, Option.some.injEq, reduceCtorEq] at h <;>
      (try subst h) <;> rfl

/-- A noun with a Theme position is built on the eventive alloseme of v. -/
theorem eq_eventive_of_internalArg_isSome (h : denoteN m (denoteV ρ v) n = some r)
    (hr : r.internalArg.isSome) : v = .eventive := by
  rcases v with _ | ⟨⟨⟩⟩
  · rw [internalArg_eq_none_of_zero h] at hr
    exact absurd hr (by simp)
  · rfl

/-- The allosemes of v and n compose exactly where they have a reading. -/
theorem isSome_denoteN_iff (m : NominalizationModel E S) (ρ : RootMeaning E S)
    (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    (denoteN m (denoteV ρ v) n).isSome ↔ (readingFromAllosemes v n).isSome := by
  rcases v with _ | cv <;> rcases n with _ | cn <;> (try cases cv) <;> (try cases cn) <;>
    simp [readingFromAllosemes, denoteV, denoteN]

/-- The complex event reading describes eventualities. -/
theorem exists_eq_ev_of_zero (h : denoteN m (denoteV ρ .eventive) .zero = some r) {x : E}
    (hx : r.pred x) : ∃ e, x = m.ev e := by
  simp only [denoteV, denoteN, Option.some.injEq] at h
  subst h
  exact hx.imp fun _ ↦ And.left

end DistributedMorphology.Allosemy
