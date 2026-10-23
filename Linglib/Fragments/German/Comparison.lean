module

public import Linglib.Syntax.Comparative

/-!
# German comparison

This file defines the German comparative construction, *X ist größer als Y* 'X is bigger than Y'.
The standard of comparison follows the particle *als* and takes its case from the compared noun
phrase, and the adjective carries the comparative ending *-er* and the superlative ending *-st*
whatever its length: Durrell notes that *mehr* and *meist* form comparatives and superlatives only
in a few special cases. The construction is a particle comparative in the sense of Stassen's WALS
chapter on comparatives, whose sample does not include German, so its type is read off the
construction (`Comparative.type`).

## References

* [durrell-2011]
* [stassen-2013]
-/

@[expose] public section

namespace German.Comparison

open Comparative

/-- The *als*-comparative marks the standard with the particle *als* and the adjective with the
bound ending *-er*. -/
def als : Comparative :=
  { standardMarker := [.free "als"], caseAssignment := .derived, degreeMarkers := [.suff "er"] }

/-- The superlative is marked by the ending *-st*, as in *das tiefste*. -/
def superlative : SuperlativeStrategy := .morphological

theorem als_type : als.type = .particle := rfl

end German.Comparison
