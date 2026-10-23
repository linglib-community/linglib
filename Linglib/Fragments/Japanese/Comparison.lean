module

public import Linglib.Syntax.Comparative
public import Linglib.Fragments.Japanese.Adpositions

/-!
# Japanese comparison

Japanese marks the standard of comparison with the postposition *yori* 'than' and leaves the
predicate without degree marking: *Taroo-wa Hanako-yori zutto haya-ku ki-ta* 'Taro came a lot
earlier than Hanako'. The standard's case is fixed by the construction, the ablative the case
fragment records for *yori* (`Japanese.Adpositions.yori`), which `Studies/Stassen1985.lean`
reads as Stassen's separative type. The superlative is formed with the adverb *itiban* 'most',
*itiban haya-ku* 'the fastest', which none of `SuperlativeStrategy`'s cases fits.

## References

* [tsujimura-2014]
* [stassen-1985]
-/

@[expose] public section

namespace Japanese.Comparison

open Comparative

/-- The *yori*-comparative marks the standard with the postposition *yori* in the ablative and has
no degree morphology. -/
def yori : Comparative :=
  { standardMarker := Adpositions.yori.morphs
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

theorem standardCase_mem_functions : ∀ k ∈ yori.standardCase, k ∈ Adpositions.yori.functions := by
  decide

end Japanese.Comparison
