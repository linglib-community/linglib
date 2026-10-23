module

public import Linglib.Syntax.Case.Spatial

/-!
# Finnish case

Finnish has some fifteen cases, each with an ending in the singular. There are the
grammatical nominative, genitive, accusative and partitive, six local cases, and the essive,
translative, comitative, abessive and instructive. The accusative ending -t is confined to
the personal pronouns, as in *häne-t* 'him, her'. The local cases cross the direction of
motion with a region. The inessive -ssA 'in', the elative -stA 'out of' and the illative -Vn
'into' make up the interior series, and the adessive -llA 'on', the ablative -ltA 'off' and
the allative -lle 'onto' the exterior series. Finnish has no surface series, which Hungarian
has, and no dative, whose recipient function the allative covers, a gap Blake's hierarchy
registers (`Studies/Blake1994.lean`).

The comparative label of the instructive, a case of manner and means as in *jala-n* 'on
foot', is the instrumental.

## Main definitions

* `Finnish.Case`, `Finnish.Case.label`: the cases, and the comparative value each is named for.

## Main results

* `Finnish.Case.toCase_mem_image_label_iff`: the local cases are the interior and exterior series
  of the shared `Localization × Direction` decomposition.

The endings, spelled in segments, are in `Finnish.Declension`.

## References

* [karlsson-2017]
* [blake-1994]
-/

@[expose] public section

namespace Finnish

/-- The fifteen cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The genitive. -/
  | gen
  /-- The accusative. -/
  | acc
  /-- The partitive. -/
  | part
  /-- The inessive. -/
  | ine
  /-- The elative. -/
  | ela
  /-- The illative. -/
  | ill
  /-- The adessive. -/
  | ade
  /-- The ablative. -/
  | abl
  /-- The allative. -/
  | all
  /-- The essive. -/
  | ess
  /-- The translative. -/
  | transl
  /-- The comitative. -/
  | com
  /-- The abessive. -/
  | abess
  /-- The instructive, of manner and means. -/
  | instr
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for, the instrumental for the instructive. -/
def label : Case → _root_.Case
  | nom => .nom
  | gen => .gen
  | acc => .acc
  | part => .part
  | ine => .ine
  | ela => .ela
  | ill => .ill
  | ade => .ade
  | abl => .abl
  | all => .all
  | ess => .ess
  | transl => .transl
  | com => .com
  | abess => .abess
  | instr => .inst

/-- The local cases are the interior and exterior series: a cell of the shared spatial
decomposition is the label of a Finnish case exactly when its region is not the surface. -/
theorem toCase_mem_image_label_iff {r : Spatial.Localization} {d : Spatial.Path.Direction}
    {c : _root_.Case} (h : _root_.Case.toCase r d = some c) :
    c ∈ Finset.univ.image label ↔ r ≠ .surface := by
  cases r <;> cases d <;> cases h <;> decide

end Case

end Finnish
