module

public import Linglib.Syntax.Feature.Case.Basic
public import Linglib.Semantics.Space.Locative
public import Mathlib.Data.Fintype.Prod

/-!
# Spatial cases

A spatial case combines a configuration with a direction: the interior, surface and exterior
series of the Finnish, Hungarian and Daghestanian local cases each cross a configuration with
location, destination and source. The general locative, allative, ablative and perlative express
a direction with no configuration. This file relates the values of `Case` to the configurations,
directions and shapes of `Locative`.

## Main definitions

* `Case.dirOf`, `Case.configurationOf`, `Case.shape?`: the direction, the configuration and the
  shape of the path a case expresses.
* `Case.ofSpatial`: the case of a configuration and a direction.
* `Locative.ofCase`: the locative a case expresses.

## Main results

* `Case.spatialDecomp_ofSpatial`: the case of a configuration and a direction decomposes into
  them.
* `Case.kind_eq_spatial_iff`: the spatial cases among Blake's types of case are those with a
  direction.

## Implementation notes

The terminative is a delimited goal, Pantcheva's *up to*. The exterior series is `ade`, `all` and
`abl`, Finnish's external local cases; `all` and `abl` also serve as the general allative and
ablative, with no configuration, a use the decomposition does not separate.

## References

* [pantcheva-2011]
* [creissels-2009]
* [blake-2001]
-/

@[expose] public section

namespace Case

open Locative

/-! ### Spatial cases -/

/-- The direction a spatial case expresses, if any, determinable even where the configuration
is not. -/
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

/-- The spatial case with a configuration and a direction, on the three series. A route has no
configuration in these inventories. -/
def ofSpatial : Configuration → Direction → Option Case
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

/-- The configuration a case expresses. The general locative has none. -/
def configurationOf : Case → Option Configuration
  | .ine | .ela | .ill => some .interior
  | .sup | .del | .sub => some .surface
  | .ade | .all | .abl => some .exterior
  | _ => none

/-- The configuration and direction of a spatial case, where both are determinable. -/
def spatialDecomp (c : Case) : Option (Configuration × Direction) :=
  match configurationOf c, dirOf c with
  | some r, some d => some (r, d)
  | _, _ => none

theorem spatialDecomp_ofSpatial (r : Configuration) (d : Direction) :
    (ofSpatial r d).bind spatialDecomp = (ofSpatial r d).map fun _ ↦ (r, d) := by
  cases r <;> cases d <;> decide

/-- The pairs of a configuration and a direction whose case is in `s`. -/
def cells (s : Finset Case) : Finset (Configuration × Direction) :=
  Finset.univ.filter fun p ↦ ∃ c ∈ ofSpatial p.1 p.2, c ∈ s

@[simp] theorem mem_cells {s : Finset Case} {p : Configuration × Direction} :
    p ∈ cells s ↔ ∃ c ∈ ofSpatial p.1 p.2, c ∈ s := by
  simp [cells]

theorem cells_mono : Monotone cells := fun _ _ h ↦
  Finset.monotone_filter_right _ fun _ _ ⟨c, hc, hs⟩ ↦ ⟨c, hc, h hs⟩

/-- `ofDir d` is the case that expresses `d` with no configuration, the general locative,
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

/-! ### The locative of a case -/

/-- The locative a case expresses, its configuration and the mode of its path: the illative is a
cofinal path into the interior. A case with no path is static. -/
def _root_.Locative.ofCase (c : Case) : Locative :=
  { configuration := c.configurationOf, mode := c.shape?.elim .static .directional }

@[simp] theorem _root_.Locative.direction_ofCase (c : Case) :
    (Locative.ofCase c).mode.direction = c.dirOf.getD .place := by
  cases c <;> rfl

/-- Every case with a path has a bounded one, since no case expresses *towards*. -/
theorem _root_.Locative.isBounded_ofCase_iff {c : Case} :
    (Locative.ofCase c).mode.IsBounded ↔ (Locative.ofCase c).mode.direction ≠ .place := by
  cases c <;> decide

end Case
