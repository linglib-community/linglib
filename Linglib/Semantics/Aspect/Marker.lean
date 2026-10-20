module

public import Linglib.Morphology.Morph
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Semantics.Aspect.Defs

/-!
# Aspect markers

A language's grammatical aspect morphemes are entered as aspect markers: the exponent as morphs,
its spelling in a native script, its interlinear gloss, the viewpoint it marks and its register.

## Main definitions

* `Aspect.Marker`: a grammatical aspect marker and the viewpoint it marks.

## References

* [smith-1997]
-/

@[expose] public section

namespace Aspect

/-- A grammatical aspect marker is its exponent with its spelling in a native script, its gloss,
the viewpoint it marks and its register. -/
structure Marker where
  /-- The exponent, in surface order, a romanization where the language has a native script. -/
  morphs : List Morphology.Morph
  /-- The spelling in the native script. -/
  script : Option String := none
  /-- The interlinear gloss. -/
  gloss : String
  /-- The viewpoint the marker marks. -/
  viewpoint : ViewpointType
  /-- The register, `.neutral` unless the marker is confined to formal or informal use. -/
  register : SocialMeaning.Register := .neutral
  deriving DecidableEq, Repr

end Aspect
