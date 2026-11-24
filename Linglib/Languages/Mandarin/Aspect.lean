module

public import Linglib.Semantics.Aspect.Marker

/-!
# Mandarin aspect markers

Mandarin has no tense inflection, and temporal interpretation rests largely on a small set of
aspect particles. The verbal suffix *le* is commonly described as the perfective marker and
*guò* as the experiential marker, an experiential perfect; the preverbal *zài* marks the
progressive. *Nézha chuī le chángdí* 'Nezha played the flute' typically refers to a specific,
likely recent event, while *Nézha chuī guò chángdí* 'Nezha has played the flute before' reports
that such an experience exists. The negative counterpart of *le* is the negator *méi-yǒu*,
entered in `Languages/Mandarin/Negation.lean`. The description and examples follow
[zhao-2025], who also documents the use of *le* and *guò* in comparatives; that the two uses
share one meaning is the dissertation's analysis and lives in `Studies/Zhao2025.lean`.

## References

* [zhao-2025]
-/

@[expose] public section

namespace Mandarin.Aspect

/-- The perfective suffix *le* 了: *Nézha mǎi le yī-píng cù* 'Nezha bought a bottle of
vinegar'. -/
def le : Aspect.Marker :=
  { morphs := [.suff "le"], script := some "了", gloss := "PFV", viewpoint := .perfective }

/-- The experiential suffix *guò* 过, an experiential perfect: *Nézha chuī guò chángdí* 'Nezha
has played the flute before'. -/
def guo : Aspect.Marker :=
  { morphs := [.suff "guò"], script := some "过", gloss := "EXP", viewpoint := .perfect }

/-- The progressive *zài* 在: *Nézha zài chàng gē* 'Nezha is singing'. -/
def zai : Aspect.Marker :=
  { morphs := [.free "zài"], script := some "在", gloss := "PROG", viewpoint := .imperfective }

/-- The aspect particles. -/
def markers : List Aspect.Marker := [le, guo, zai]

end Mandarin.Aspect
