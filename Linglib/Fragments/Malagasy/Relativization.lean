module

public import Linglib.Syntax.Clause.Relative

/-!
# Malagasy relative clauses

Malagasy relativizes subjects only. The head noun is followed, optionally, by the invariable
relativizer *izay* and then by the clause with the relativized position left empty, as in *ny
mpianatra izay nahita ny vehivavy* 'the student that saw the woman'. Any other noun phrase must
first be promoted to subject by the voice system and then relativized as a subject. The data
are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace Malagasy

/-- The postnominal clause, optionally introduced by *izay*, leaves the relativized position
empty and relativizes subjects only. -/
def relGap : Relativizer where
  placement := .postNominal
  realize
    | .subject => {.gap}
    | _ => ∅

/-- The Malagasy relativizers. -/
def relativizers : List Relativizer := [relGap]

end Malagasy
