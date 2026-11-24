module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum

/-!
# Locatives

A *locative* is an expression that places an object in space with respect to another object, the
*ground*: *in the house*, *into the house*, *from under the table*. Its meaning has two parts.
The *configuration* is a way of being positioned with respect to the ground, such as being in it,
on it or at it. The *mode* is the way the object moves with respect to the configuration during
an event. In the *static* mode the object stays in the configuration. In a *directional* mode it
follows a path, which may lead into the configuration, out of it, through it, and so on.

This file defines the configurations, the modes and the eight shapes of a path. It also defines
the *direction* of a mode, a coarser classification into place, goal, source and route. For
example, *into the house* has the interior configuration and a cofinal path, and its direction is
goal.

## Main definitions

* `Locative.Configuration`: the interior, the surface and the exterior of a ground.
* `Locative.Direction`: place, goal, source and route.
* `Locative.Shape`: the eight shapes of a path relative to a region.
* `Locative.Mode`: the static mode and the directional modes, one for each shape.
* `Locative`: a configuration, if any, and a mode.

## Main results

* `Locative.Shape.exists_direction_transition_iff`: the pairs of a direction and a transition
  that make a shape.
* `Locative.Mode.direction_eq_place_iff`: the static mode is the only mode whose direction is
  place.

## Implementation notes

The static mode is a value of `Locative.Mode`, so every locative has a mode. The alternative is
an optional shape, but then the direction of a locative needs a default value.

The configuration of a locative is optional. A language with a single series of spatial cases has
a locative, an allative and an ablative that specify no configuration.

`Locative.Configuration` has three values, the ones that systems of spatial cases most often
distinguish. Adpositions distinguish many more.

The literature also calls the configuration the *localization* and the direction the
*directionality*.

## References

* [kracht-2002]
* [creissels-2009]
* [lestrade-2010]
* [pantcheva-2011]
* [zwarts-2005]
-/

@[expose] public section

namespace Locative

/-! ### Configurations -/

/-- The part of the ground an object is positioned in. -/
inductive Configuration where
  /-- The interior, as of *in*, *into* and *out of*. -/
  | interior
  /-- The surface, as of *on*, *onto* and *off*. -/
  | surface
  /-- The exterior, as of *at*, *to* and *from*. -/
  | exterior
  deriving DecidableEq, Repr, Fintype

/-! ### Directions -/

/-- The direction heads of a path, in containment order, Goal built on Place, Source on Goal,
and Route on Source. -/
inductive Direction where
  /-- Place is static location, the base of the others. -/
  | place
  /-- Goal is a path *to* a place. -/
  | goal
  /-- Source is a path *from* a place. -/
  | source
  /-- Route is a path *via* or *past* a place. -/
  | route
  deriving DecidableEq, Repr, Fintype

namespace Direction

/-- The number of heads below a direction. -/
def rank : Direction → Fin 4
  | place => 0
  | goal => 1
  | source => 2
  | route => 3

/-- The containment order: a direction is below those whose structure contains it. -/
instance : LinearOrder Direction := LinearOrder.lift' rank (by decide)

/-- The direction of a reversed path swaps Goal and Source and keeps Place and Route. -/
def reverse : Direction → Direction
  | goal => source
  | source => goal
  | d => d

@[simp] theorem reverse_reverse (d : Direction) : d.reverse.reverse = d := by cases d <;> rfl

end Direction

/-! ### Shapes -/

/-- How a path relates its run inside the region to its run outside. -/
inductive Transition where
  /-- The path changes its relation to the region, as *to* does. -/
  | transitional
  /-- The path is inside at one extreme point only, which bounds it, as *up to* does. -/
  | delimited
  /-- The path does not change it, as *towards* does. -/
  | nonTransitional
  deriving DecidableEq, Repr, Fintype

/-- The eight shapes of a path relative to a region. -/
inductive Shape where
  /-- A cofinal path runs outside, then inside, as *to* does. -/
  | cofinal
  /-- A coinitial path runs inside, then outside, as *from* does. -/
  | coinitial
  /-- A transitive path runs outside, inside and outside, as *past* does. -/
  | transitive
  /-- A terminative path runs outside up to its goal, which is inside, as *up to* does. -/
  | terminative
  /-- An egressive path starts inside and runs outside, as *starting from* does. -/
  | egressive
  /-- An approximative path runs outside, nearer at each point, as *towards* does. -/
  | approximative
  /-- A recessive path runs outside, farther at each point, as *away from* does. -/
  | recessive
  /-- A prolative path runs inside throughout, as *along* does. -/
  | prolative
  deriving DecidableEq, Repr, Fintype

namespace Shape

/-- The direction of a shape. -/
def direction : Shape → Direction
  | cofinal | terminative | approximative => .goal
  | coinitial | egressive | recessive => .source
  | transitive | prolative => .route

/-- The transition of a shape. -/
def transition : Shape → Transition
  | cofinal | coinitial | transitive => .transitional
  | terminative | egressive => .delimited
  | approximative | recessive | prolative => .nonTransitional

theorem direction_transition_injective :
    Function.Injective fun s : Shape ↦ (s.direction, s.transition) := by
  intro a b h
  cases a <;> cases b <;> simp_all [direction, transition]

/-- A direction and a transition make a shape exactly when the direction is not Place and a
Route is not delimited. -/
theorem exists_direction_transition_iff (d : Direction) (t : Transition) :
    (∃ s : Shape, s.direction = d ∧ s.transition = t) ↔
      d ≠ .place ∧ (d = .route → t ≠ .delimited) := by
  cases d <;> cases t <;> decide

/-- The shape of a reversed path. -/
def reverse : Shape → Shape
  | cofinal => coinitial
  | coinitial => cofinal
  | terminative => egressive
  | egressive => terminative
  | approximative => recessive
  | recessive => approximative
  | s => s

@[simp] theorem reverse_reverse (s : Shape) : s.reverse.reverse = s := by cases s <;> rfl

@[simp] theorem direction_reverse (s : Shape) : s.reverse.direction = s.direction.reverse := by
  cases s <;> rfl

@[simp] theorem transition_reverse (s : Shape) : s.reverse.transition = s.transition := by
  cases s <;> rfl

/-- A shape is bounded when it has a transition. Concatenating two paths of a bounded shape never
yields another, and concatenating two of any other shape always does. -/
def IsBounded (s : Shape) : Prop := s.transition ≠ .nonTransitional

instance : DecidablePred IsBounded := fun s ↦ inferInstanceAs (Decidable (s.transition ≠ _))

end Shape

/-! ### Modes -/

/-- The way an object moves with respect to a configuration during an event. -/
inductive Mode where
  /-- The object stays in the configuration, as with *in the house*. -/
  | static
  /-- The object moves along a path of the given shape, as with *into the house*. -/
  | directional (shape : Shape)
  deriving DecidableEq, Repr, Fintype

namespace Mode

/-- The direction of a mode, Place for the static mode. -/
def direction : Mode → Direction
  | static => .place
  | directional s => s.direction

@[simp] theorem direction_static : static.direction = .place := rfl

@[simp] theorem direction_directional (s : Shape) : (directional s).direction = s.direction := rfl

theorem direction_eq_place_iff {m : Mode} : m.direction = .place ↔ m = static := by
  rcases m with _ | s
  · simp
  · cases s <;> simp [Shape.direction]

theorem direction_surjective : Function.Surjective direction
  | .place => ⟨static, rfl⟩
  | .goal => ⟨directional .cofinal, rfl⟩
  | .source => ⟨directional .coinitial, rfl⟩
  | .route => ⟨directional .transitive, rfl⟩

/-- A mode is bounded when its path is, as that of *to* is and that of *towards* is not. -/
def IsBounded : Mode → Prop
  | static => False
  | directional s => s.IsBounded

instance : DecidablePred IsBounded
  | static => inferInstanceAs (Decidable False)
  | directional s => inferInstanceAs (Decidable s.IsBounded)

theorem IsBounded.direction_ne_place {m : Mode} (h : m.IsBounded) : m.direction ≠ .place := by
  rintro hm
  rw [direction_eq_place_iff.1 hm] at h
  exact h

end Mode

end Locative

/-- A locative is the configuration and the mode a locative expression specifies, *into the
house* the interior and a cofinal path. -/
structure Locative where
  /-- The configuration, `none` where the expression specifies none. -/
  configuration : Option Locative.Configuration := none
  /-- The mode. -/
  mode : Locative.Mode := .static
  deriving DecidableEq, Repr
