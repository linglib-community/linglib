module

public import Linglib.Data.Statistics.Schema

/-!
# KuhlmannNivre2006: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/KuhlmannNivre2006.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The evaluation of section 4: the dependency analyses of the Danish Dependency Treebank and of the
Prague Dependency Treebank, measured by gap degree and edge degree and checked for projectivity,
planarity and well-nestedness. Table 1 prints for each treebank the number of structures at each gap
degree and at each edge degree, and the number that are projective, planar and well-nested, over all
structures and over the non-projective ones only. Each count is printed with its percentage of the
structures it is taken over; the percentages are not recorded, and the study recomputes those the
text argues from.

## References

* [kuhlmann-nivre-2006]
-/

@[expose] public section

namespace KuhlmannNivre2006

open Data.Statistics

/-- The treebank. -/
inductive Treebank where
  /-- DDT: the Danish Dependency Treebank, the whole treebank with its primary dependencies only,
  less the 17 analyses with more than one root or a node with more than one head, which
  footnote 4 sets aside as annotation errors -/
  | ddt
  /-- PDT: the analytical layer of the dedicated training section of the Prague Dependency
  Treebank -/
  | pdt
  deriving DecidableEq, Repr, Fintype

/-- A graded measure of non-projectivity. -/
inductive Measure where
  /-- gap degree: the greatest number of gaps in the projection of a node -/
  | gap
  /-- edge degree: the greatest number of connected components an edge spans whose roots its head
  does not dominate -/
  | edge
  deriving DecidableEq, Repr, Fintype

/-- A binary constraint relaxing projectivity. -/
inductive Constraint where
  /-- planar: no two edges cross -/
  | planar
  /-- well-nested: no two disjoint subtrees interleave -/
  | wellNested
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 1, p. 512: the number of structures of a treebank, of the projective ones and
of the non-projective ones. -/
structure Structures where
  /-- The number of structures, the n over all structures. -/
  all : ℕ
  /-- The number of projective structures. -/
  projective : ℕ
  /-- The number of non-projective structures, the n over them only. -/
  nonProjective : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 512, by treebank; counted in a corpus; checked against the page
images. -/
def structures : Treebank → Structures
  | .ddt => ⟨4393, 3732, 661⟩
  | .pdt => ⟨73088, 56168, 16920⟩

/-- A row of Table 1, p. 512: the number of structures of a treebank at each degree of a measure. -/
structure Degrees where
  /-- The number of structures at degree 0, 1, 2 and on up to the last degree printed for either
  treebank, a dash as none. -/
  counts : List (Option ℕ)
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 512, by measure and treebank; counted in a corpus; checked against
the page images. -/
def degrees : Measure → Treebank → Degrees
  | .gap, .ddt => ⟨[some 3732, some 654, some 7, none, none]⟩
  | .gap, .pdt => ⟨[some 56168, some 16608, some 307, some 4, some 1]⟩
  | .edge, .ddt => ⟨[some 3732, some 584, some 58, some 17, some 2, none, none]⟩
  | .edge, .pdt => ⟨[some 56168, some 16585, some 259, some 63, some 10, some 2, some 1]⟩

/-- A row of Table 1, p. 512: the number of structures of a treebank meeting a binary constraint,
over all structures and over the non-projective ones only. -/
structure Coverage where
  /-- The number of structures meeting the constraint. -/
  all : ℕ
  /-- The number of non-projective structures meeting the constraint. -/
  nonProjective : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 512, by constraint and treebank; counted in a corpus; checked
against the page images. -/
def coverage : Constraint → Treebank → Coverage
  | .planar, .ddt => ⟨3796, 64⟩
  | .planar, .pdt => ⟨60048, 3880⟩
  | .wellNested, .ddt => ⟨4388, 656⟩
  | .wellNested, .pdt => ⟨73010, 16842⟩

end KuhlmannNivre2006
