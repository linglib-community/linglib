module

public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Semantics.Events.Path

/-!
# Spatial adpositions

A theory refines a spatial `Adposition` by decomposing its relation into an axial part, a
localization and the shape of its path, as Svenonius does in the cartographic sequence. The
shape is one of Pantcheva's eight, `Spatial.Path.Shape`, or none for a locative reading, and the
localization is `Spatial.Localization`, the vocabulary spatial cases decompose into as well. The
axial parts are what case morphology lacks, a flat paradigm rather than a ranked containment.

## Main declarations

* `Adposition.AxPart`: the axial parts (front, back, top, …).
* `Adposition.SpatialReading`: the cartographic decomposition.
* `Adposition.SpatialReading.direction`, `IsBounded`: the direction and boundedness of a
  reading, read off its shape.

## Main results

* `Adposition.SpatialReading.direction_eq_place_iff`: a reading is locative exactly when it has no
  path.

## References

* [svenonius-2010]
* [svenonius-2006]
* [pantcheva-2011]
* [zwarts-2005]
-/

@[expose] public section

namespace Adposition

/-- The axial parts are the regions a spatial adposition projects onto the Ground's axes, as
*behind* projects `back` and *under* `bottom`. -/
inductive AxPart where
  | front
  | back
  | top
  | bottom
  | side
  | interior
  | exterior
  deriving DecidableEq, Repr, Fintype

/-- A spatial reading decomposes a spatial adposition's relation into an axial part, a
localization and the shape of its path. -/
structure SpatialReading where
  /-- The axial part of an axial adposition such as *behind*; `none` for *in*, *to*,
  *from*. -/
  axPart : Option AxPart := none
  /-- The localization, interior, surface or exterior. -/
  localization : Option Spatial.Localization := none
  /-- The shape of the path, `none` for a locative reading. -/
  shape : Option Spatial.Path.Shape := none
  deriving Repr, DecidableEq

namespace SpatialReading

/-- The direction of a reading is its shape's, and Place for a locative reading. -/
def direction (r : SpatialReading) : Spatial.Path.Direction :=
  (r.shape.map (·.direction)).getD .place

/-- A reading is bounded when its path is, as *to* is and *towards* is not. -/
def IsBounded (r : SpatialReading) : Prop := ∃ s ∈ r.shape, s.IsBounded

instance : DecidablePred IsBounded := fun r ↦
  inferInstanceAs (Decidable (∃ s ∈ r.shape, s.IsBounded))

variable {r : SpatialReading}

theorem direction_eq_place_iff : r.direction = .place ↔ r.shape = none := by
  rcases r with ⟨_, _, _ | s⟩
  · simp [direction]
  · cases s <;> simp [direction, Spatial.Path.Shape.direction]

theorem IsBounded.direction_ne_place (h : r.IsBounded) : r.direction ≠ .place := by
  obtain ⟨s, hs, -⟩ := h
  simp_all [direction_eq_place_iff]

end SpatialReading

/-! ### Readings -/

/-- The reading of *behind* is axial (back) and locative. -/
def behind : SpatialReading := { axPart := some .back }

/-- The reading of *under* is axial (bottom) and locative. -/
def under : SpatialReading := { axPart := some .bottom }

/-- The reading of *into* is a cofinal path into the interior. -/
def into : SpatialReading := { localization := some .interior, shape := some .cofinal }

end Adposition
