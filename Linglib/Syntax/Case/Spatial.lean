module

public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.Events.Path
public import Mathlib.Data.Fintype.Prod

/-!
# Spatial cases

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
* [blake-2001]
-/

@[expose] public section

namespace Case

open Spatial (Localization)
open Spatial.Path (Direction)

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
def shape? : Case → Option Spatial.Path.Shape
  | .ill | .all | .sub => some .cofinal
  | .ela | .abl | .del => some .coinitial
  | .perl => some .transitive
  | .ter => some .terminative
  | _ => none

theorem dirOf_eq_of_shape?_eq {c : Case} {s : Spatial.Path.Shape} (h : c.shape? = some s) :
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
