module

public import Linglib.Morphology.Word.Tree
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Finset.Basic

/-!
# Distributed Morphology

Distributed Morphology builds words in the syntax and supplies their forms late. The syntax
combines abstract morphemes: roots, which have no category, and functional morphemes, bundles of
features, among them the categorizers *n*, *v* and *a* with one of which every root combines.
Head movement and the operations after syntax gather a root and the heads above it into a complex
head, and Vocabulary Insertion realizes its terminals, choosing among Vocabulary Items by the
Subset Principle.

This file defines those objects. A complex head `ComplexHead R H` is a root of type `R` with the
heads of type `H` adjoined above it, innermost first. Taking `R` to be `Root`, an index with no
form, follows the view that roots are inserted late like every other morpheme; taking it to be a
`Morpheme` whose exponent is already supplied follows the view that a root brings its phonology
into the syntax.

## Main definitions

* `DistributedMorphology.Root`: a root, individuated by an index alone.
* `DistributedMorphology.Categorizer`: the categorizers *n*, *v* and *a*.
* `DistributedMorphology.Morpheme`: a terminal at PF, its features with the exponent Vocabulary
  Insertion substitutes for its variable Q.
* `DistributedMorphology.ComplexHead`: a root with the heads adjoined above it.
* `DistributedMorphology.ComplexHead.word`: the complex head after some steps of Merger.
* `DistributedMorphology.ComplexHead.surface`: the linear order of a complex head.

## Main statements

* `DistributedMorphology.ComplexHead.surface_eq`: the Mirror Principle.

## Implementation notes

The operations on complex heads are in their own files: Vocabulary Items and the Subset Principle in
`VocabularyInsertion/Basic.lean`, insertion from the inside out in
`VocabularyInsertion/InsideOut.lean`, the contexts rules read in `Neighborhood.lean`, the locality
of allomorphy and allosemy within words in `Locality.lean` and across phrases in
`PhrasalLocality.lean`, the configurations in which a Root is categorized and the diagnostics
that can tell them apart in `RootCategorization.lean`, the rules that change terminals before
insertion in `Impoverishment.lean`, `Fission.lean`, `Fusion.lean` and `Spellout.lean`, gender on
*n* in `Gender.lean`, and contextual meaning in `Allosemy.lean`.

## References

* [halle-marantz-1993]
* [harley-2014]
* [embick-2015]
* [baker-1985]
* [kalin-bjorkman-etal-2026]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology (Morph)

/-! ### Roots and categorizers -/

/-- A root is individuated by an arbitrary index alone, with deliberately no form or meaning, and
receives its form at Vocabulary Insertion. A different object from the comparative-concept root
of `Morphology/Root/Basic.lean`, which is a contentful morph. -/
@[ext]
structure Root where
  /-- The individuating index. -/
  index : Nat
  deriving DecidableEq, Repr

/-- Roots are their indices and nothing more. -/
def Root.equivNat : Root ≃ ℕ where
  toFun := Root.index
  invFun := Root.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The root inventory is unbounded, an open class. -/
instance : Infinite Root := Root.equivNat.infinite_iff.mpr inferInstance

/-- The categorizing heads, which merge with a root that has no category. -/
inductive Categorizer where
  | n
  | v
  | a
  deriving DecidableEq, Repr, Fintype

theorem card_categorizer : Fintype.card Categorizer = 3 := rfl

/-! ### Morphemes -/

/-- A morpheme at PF carries its features, the value of its Q variable (`none` before Vocabulary
Insertion, the exponent after), and the side on which it is linearized. -/
@[ext]
structure Morpheme (F E : Type*) where
  /-- The synsem and diacritic features. -/
  feats : Finset F
  /-- The Q variable is `none` until an exponent is substituted for it. -/
  exp : Option E := none
  /-- The side of its host the morpheme is linearized on. -/
  side : Morph.Side := .after

namespace Morpheme

variable {F E : Type*}

/-- Morphemes are compared field by field, so two feature sets listed in different orders are
equal. -/
instance [DecidableEq F] [DecidableEq E] : DecidableEq (Morpheme F E) :=
  fun _ _ ↦ decidable_of_iff _ Morpheme.ext_iff.symm

/-- The morpheme has been realized. -/
def IsRealized (s : Morpheme F E) : Prop := s.exp.isSome

instance (s : Morpheme F E) : Decidable s.IsRealized := inferInstanceAs (Decidable (_ = true))

/-- Substitute the exponent for Q. -/
def realize (s : Morpheme F E) (e : E) : Morpheme F E := { s with exp := some e }

end Morpheme

/-! ### Complex heads -/

/-- A complex head is a root with the heads adjoined above it, innermost first. -/
structure ComplexHead (R H : Type*) where
  /-- The root. -/
  root : R
  /-- The heads above the root, innermost first. -/
  heads : List H
  deriving DecidableEq, Repr

namespace ComplexHead

variable {R H : Type*} (s : ComplexHead R H)

/-- The complex head after `k` steps of Merger, the root with the first `k` heads. The remaining
heads are realized periphrastically. -/
def word (k : ℕ) : ComplexHead R H := ⟨s.root, s.heads.take k⟩

theorem heads_word_isPrefix (k : ℕ) : (s.word k).heads <+: s.heads := List.take_prefix k s.heads

theorem mem_word_of_le {k : ℕ} {i j : Fin s.heads.length} (hji : j ≤ i)
    (hi : (i : ℕ) < k) : (j : ℕ) < k := lt_of_le_of_lt hji hi

/-- The word tree, each head attached on the side its exponent takes, innermost first. -/
def toTree (side : H → Morph.Side) : Morphology.Word.Tree (R ⊕ H) :=
  Morphology.Word.Tree.attachAll (.inl s.root) (s.heads.map fun h => (side h, .inr h))

/-- The surface order of root and heads. -/
def surface (side : H → Morph.Side) : List (R ⊕ H) := (s.toTree side).toList

theorem surface_eq (side : H → Morph.Side) :
    s.surface side =
      ((s.heads.filter fun h => side h = .before).map Sum.inr).reverse ++
        Sum.inl s.root :: (s.heads.filter fun h => side h = .after).map Sum.inr := by
  simp [surface, toTree, Morphology.Word.Tree.toList_attachAll, List.filter_map, List.map_map,
    Function.comp_def]

end ComplexHead

end DistributedMorphology
