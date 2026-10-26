module

public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.Events.Path
public import Mathlib.Data.Fintype.Prod

/-!
# Spatial cases

A spatial case combines a localization with a direction, as Pantcheva decomposes them: the
interior, surface and exterior series of Finnish, Hungarian and Daghestanian local cases each
cross a localization with Place, Goal and Source. The general locative, allative, ablative and
perlative express a direction with no localization. Blake's types of case (Table 2.7) place
the spatial cases among the semantic cases, apart from the grammatical ones.

## Main definitions

* `Case.dirOf`, `Case.localizationOf`: the direction and the localization a spatial case
  expresses, if any.
* `Case.toCase`, `Case.spatialDecomp`: a spatial case from its localization and direction, and
  back.
* `Case.cells`: the localization-direction pairs whose case is in an inventory.
* `Case.ofDir`: the localization-neutral case of a direction.
* `Case.shape?`: the shape of the paths a directional case expresses.
* `Case.Kind`, `Case.kind`: grammatical, spatial and other semantic cases.

## Main results

* `Case.spatialDecomp_toCase`: the decomposition round-trips on the localization-specific cells.
* `Case.dirOf_ofDir`: the localization-neutral case of a direction expresses it.
* `Case.kind_eq_spatial_iff`: the spatial cases are those with a direction.

## Implementation notes

Blake names the nominative, accusative, ergative, genitive and dative as grammatical cases;
`Case.kind` adds the absolutive, the oblique, the partitive and the vocative to them. The
terminative is a delimited goal, Pantcheva's *up to*.

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

/-- Build a spatial case from its `Localization × Direction` decomposition — the
    constructor direction spatial-case fragments consume. The 3 × 3
    localization-specific cells; `route` is localization-neutral in these
    inventories (`none`). -/
def toCase : Localization → Direction → Option Case
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

/-- The localization a case expresses, under the spatial reading. The exterior series is
    `ade`, `all` and `abl`, Finnish's external local cases; `all` and `abl` also serve as the
    general allative and ablative, with no localization, a use this decomposition does not
    separate. The general locative `loc` has no localization. -/
def localizationOf : Case → Option Localization
  | .ine | .ela | .ill => some .interior
  | .sup | .del | .sub => some .surface
  | .ade | .all | .abl => some .exterior
  | _ => none

/-- Analyze a spatial case into `Localization × Direction`, where both are
    determinable (lossy on localization-conflated cells; the faithful inverse
    of `toCase` on the 3 × 3 localization-specific cells). -/
def spatialDecomp (c : Case) : Option (Localization × Direction) :=
  match localizationOf c, dirOf c with
  | some r, some d => some (r, d)
  | _, _ => none

/-- `toCase` and `spatialDecomp` are inverse on the localization-specific
    cells — the decomposition round-trips where localization is not conflated.
    (`route` is localization-neutral, hence `none` on both sides.) -/
theorem spatialDecomp_toCase (r : Localization) (d : Direction) :
    (toCase r d).bind spatialDecomp =
      (toCase r d).map (fun _ => (r, d)) := by
  cases r <;> cases d <;> decide

/-- The localization-direction pairs whose case is in `s`. -/
def cells (s : Finset Case) : Finset (Localization × Direction) :=
  Finset.univ.filter fun p ↦ ∃ c ∈ toCase p.1 p.2, c ∈ s

@[simp] theorem mem_cells {s : Finset Case} {p : Localization × Direction} :
    p ∈ cells s ↔ ∃ c ∈ toCase p.1 p.2, c ∈ s := by
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

/-! ### Types of case -/

/-- A case is grammatical, encoding a syntactic relation, or semantic, and a semantic case is
spatial when it encodes location, source, destination or path. -/
inductive Kind where
  /-- A grammatical case is a core case, the genitive or the dative. -/
  | grammatical
  /-- A spatial case encodes location, source, destination or path, alone or with another
  notion. -/
  | spatial
  /-- A semantic case that is not spatial, such as the instrumental and the comitative. -/
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- The type of a case value. -/
def kind : Case → Kind
  | .nom | .acc | .gen | .dat | .erg | .abs | .obl | .part | .voc => .grammatical
  | .loc | .ine | .ade | .sup | .ill | .all | .sub | .ela | .abl | .del | .perl | .ter =>
    .spatial
  | .inst | .com | .ben | .abess | .caus | .tem | .ess | .transl => .semantic

theorem kind_eq_spatial_iff (c : Case) : c.kind = .spatial ↔ c.dirOf.isSome := by
  cases c <;> decide

end Case
