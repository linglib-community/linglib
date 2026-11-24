module

public import Linglib.Syntax.Feature.Case.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod

/-!
# Spatial cases

This file defines the vocabulary of spatial cases and adpositions: the direction `Case.Direction`,
the localization `Case.Localization`, and the shape `Case.Shape` of the path a directional marker
describes.

A spatial case combines a localization with a direction, as Pantcheva decomposes them: the
interior, surface and exterior series of Finnish, Hungarian and Daghestanian local cases each
cross a localization with Place, Goal and Source, and [the decomposition round-trips on those
cells](##Case.spatialDecomp_ofSpatial). The general locative, allative, ablative and perlative
express a direction with no localization. Blake's types of case (Table 2.7) place the spatial cases
among the semantic cases, apart from the grammatical ones, and [the spatial cases are those with a
direction](##Case.kind_eq_spatial_iff).

## Implementation notes

The terminative is a delimited goal, Pantcheva's *up to*. The exterior series is `ade`, `all` and
`abl`, Finnish's external local cases; `all` and `abl` also serve as the general allative and
ablative, with no localization, a use the decomposition does not separate.

## References

* [pantcheva-2011]
* [zwarts-2005]
* [blake-2001]
-/

@[expose] public section

namespace Case

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

/-- A shape is bounded when it has a transition. Concatenating two paths of a bounded shape
[never yields another](##Case.HasShape.not_concat), and concatenating two of any other
shape [always does](##Case.HasShape.concat). -/
def IsBounded (s : Shape) : Prop := s.transition ≠ .nonTransitional

instance : DecidablePred IsBounded := fun s ↦ inferInstanceAs (Decidable (s.transition ≠ _))

end Shape

/-! ### Localization -/

/-- The part of the reference object a spatial expression localizes in, orthogonal to the
direction. -/
inductive Localization where
  /-- The interior, as of *in*, *into* and *out of*. -/
  | interior
  /-- The surface, as of *on*, *onto* and *off*. -/
  | surface
  /-- The exterior, as of *at*, *to* and *from*. -/
  | exterior
  deriving DecidableEq, Repr, Fintype

/-! ### Spatial cases -/

/-- The direction a spatial case expresses, if any, determinable even where the localization is
not (`localizationOf`). -/
def dirOf : Case → Option Direction
  | .loc | .ine | .ade | .sup => some .place
  | .ill | .all | .sub | .ter => some .goal
  | .ela | .abl | .del => some .source
  | .perl => some .route
  | _ => none

/-- The shape of the paths a directional case expresses. The illative, allative and sublative are
cofinal, the elative, ablative and delative coinitial, the perlative transitive, and the
terminative terminative. -/
def shape? : Case → Option Shape
  | .ill | .all | .sub => some .cofinal
  | .ela | .abl | .del => some .coinitial
  | .perl => some .transitive
  | .ter => some .terminative
  | _ => none

theorem dirOf_eq_of_shape?_eq {c : Case} {s : Shape} (h : c.shape? = some s) :
    c.dirOf = some s.direction := by
  cases c <;> simp_all [shape?] <;> subst h <;> rfl

/-- The spatial case with a localization and a direction, on the three localization-specific
series. A route is localization-neutral in these inventories. -/
def ofSpatial : Localization → Direction → Option Case
  | .interior, .place => some .ine
  | .interior, .goal => some .ill
  | .interior, .source => some .ela
  | .surface, .place => some .sup
  | .surface, .goal => some .sub
  | .surface, .source => some .del
  | .exterior, .place => some .ade
  | .exterior, .goal => some .all
  | .exterior, .source => some .abl
  | _, .route => none

/-- The localization a case expresses, under the spatial reading. The general locative has none. -/
def localizationOf : Case → Option Localization
  | .ine | .ela | .ill => some .interior
  | .sup | .del | .sub => some .surface
  | .ade | .all | .abl => some .exterior
  | _ => none

/-- The localization and direction of a spatial case, where both are determinable. -/
def spatialDecomp (c : Case) : Option (Localization × Direction) :=
  match localizationOf c, dirOf c with
  | some r, some d => some (r, d)
  | _, _ => none

theorem spatialDecomp_ofSpatial (r : Localization) (d : Direction) :
    (ofSpatial r d).bind spatialDecomp = (ofSpatial r d).map fun _ ↦ (r, d) := by
  cases r <;> cases d <;> decide

/-- The localization-direction pairs whose case is in `s`. -/
def cells (s : Finset Case) : Finset (Localization × Direction) :=
  Finset.univ.filter fun p ↦ ∃ c ∈ ofSpatial p.1 p.2, c ∈ s

@[simp] theorem mem_cells {s : Finset Case} {p : Localization × Direction} :
    p ∈ cells s ↔ ∃ c ∈ ofSpatial p.1 p.2, c ∈ s := by
  simp [cells]

theorem cells_mono : Monotone cells := fun _ _ h ↦
  Finset.monotone_filter_right _ fun _ _ ⟨c, hc, hs⟩ ↦ ⟨c, hc, h hs⟩

/-- `ofDir d` is the case that expresses `d` with no localization, the general locative,
allative, ablative or perlative. -/
def ofDir : Direction → Case
  | .place => .loc
  | .goal => .all
  | .source => .abl
  | .route => .perl

@[simp] theorem dirOf_ofDir (d : Direction) : (ofDir d).dirOf = some d := by
  cases d <;> rfl

theorem ofDir_injective : Function.Injective ofDir := by
  intro d d' h
  simpa using congrArg dirOf h

theorem kind_eq_spatial_iff (c : Case) : c.kind = .spatial ↔ c.dirOf.isSome := by
  cases c <;> decide

end Case
