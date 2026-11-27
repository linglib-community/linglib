module

public import Linglib.Semantics.Space.Path

/-!
# The paths a locative describes

A locative describes paths relative to a ground. Its configuration gives a region from the region
of the ground, by a place function, and its mode says how a path passes through that region. In
the static mode the path stays in the region, and in a directional mode it has the shape of the
mode.

## Main definitions

* `Locative.Mode.Holds`: a path has a mode relative to a region.
* `Locative.paths`: the paths a locative describes relative to the region of a ground.

## Main results

* `Locative.Mode.holds_static_iff`: the static mode and the prolative shape hold of the same
  paths.
* `Locative.paths_static_mono`: for a monotone place function, the paths a static locative
  describes grow with the region of the ground.

## Implementation notes

`Locative.paths` takes the place function of each configuration as an argument, since the place
functions of the configurations are not defined yet.

## TODO

* The measure of distance should depend on the region.

## References

* [kracht-2002]
* [zwarts-2005]
-/

@[expose] public section

namespace Locative

open Order

variable {ι P β : Type*} [LinearOrder ι] [BoundedOrder ι] [Preorder β]

/-- A path has a mode relative to a region: it stays in the region if the mode is static, and has
the shape of the mode otherwise. -/
def Mode.Holds (R : Set P) (γ : ι → P) (d : P → β) : Mode → Prop
  | .static => StaysIn γ R
  | .directional s => HasShape R γ d s

/-- The static mode and the prolative shape hold of the same paths. -/
theorem Mode.holds_static_iff {R : Set P} {γ : ι → P} {d : P → β} :
    Mode.static.Holds R γ d ↔ HasShape R γ d .prolative :=
  Iff.rfl

/-- The paths a locative describes relative to the region `G` of a ground, given the place
function of each configuration. -/
def paths (place : Option Configuration → Set P → Set P) (d : P → β) (l : Locative)
    (G : Set P) : Set (ι → P) :=
  {γ | l.mode.Holds (place l.configuration G) γ d}

theorem paths_static_mono {place : Option Configuration → Set P → Set P} {d : P → β}
    {c : Option Configuration} (hf : Monotone (place c)) :
    Monotone (paths (ι := ι) place d ⟨c, .static⟩) :=
  fun _ _ h _ hγ i ↦ hf h (hγ i)

end Locative
