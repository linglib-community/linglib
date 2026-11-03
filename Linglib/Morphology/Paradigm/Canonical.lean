/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization
public import Mathlib.Data.Set.Function

/-!
# Canonical inflection

Corbett defines canonical inflection by comparing the forms of a paradigm. Across the cells of a
lexeme the lexical material, the stem, stays the same while the inflectional material differs,
and across lexemes at one cell the stems differ while the inflectional material stays the same.
An analysis of a realization of lexemes over cells gives each form the stem and inflectional
material it is built from by one morphotactics, and canonical inflection is the four comparisons
with every cell realized by exactly one form. When forms decompose uniquely, [the comparisons
entail that every cell has its own form](##IsCanonical.realize_disjoint), as Stump observes, and a
canonical analysis has [neither a suppletive stem nor a suppletive
affix](##IsCanonical.not_isSuppletive).

## Implementation notes

The morphotactics is one function for every cell and lexeme, so Corbett's first row, the same
composition throughout, holds by construction. A theory supplies the analysis: Distributed
Morphology the exponents of a root and of the head beside it, Paradigm Function Morphology the
stems and the property sets the realization rules spell out.

## References

* [corbett-2007]
* [stump-2016]
-/

@[expose] public section

namespace Morphology.Realization

open Function

variable {L C F Z I : Type*} [DecidableEq F]

/-- An **analysis** of a realization of lexemes over cells gives each form of a cell the stem and
inflectional material it is built from by the morphotactics `compose`. -/
structure Analysis (W : Realization L C F) (Z I : Type*) where
  /-- The pairs of a stem and inflectional material that build the forms of each cell. -/
  parts : Realization L C (Z × I)
  /-- The morphotactics joining a stem and inflectional material into a form. -/
  compose : Z → I → F
  /-- The forms of each cell are those the morphotactics builds from its pairs. -/
  realize_eq : ∀ l c, W.realize l c = (parts.realize l c).image (uncurry compose)

namespace Analysis

variable {W : Realization L C F} (P : W.Analysis Z I)

section Rows

variable [DecidableEq Z] [DecidableEq I]

/-- The lexical material of each cell, its stems. -/
def stem : Realization L C Z := P.parts.map Prod.fst

/-- The inflectional material of each cell. -/
def inflection : Realization L C I := P.parts.map Prod.snd

end Rows

/-- An analysis is **unambiguous** when its morphotactics builds distinct forms from distinct pairs
of the analysis. -/
def IsUnambiguous : Prop := Set.InjOn (uncurry P.compose) {x | ∃ l c, x ∈ P.parts.realize l c}

theorem isUnambiguous_iff : P.IsUnambiguous ↔ ∀ l c, ∀ x ∈ P.parts.realize l c, ∀ l' c',
    ∀ y ∈ P.parts.realize l' c', uncurry P.compose x = uncurry P.compose y → x = y :=
  ⟨fun h _ _ _ hx _ _ _ hy he ↦ h ⟨_, _, hx⟩ ⟨_, _, hy⟩ he,
    fun h _ ⟨_, _, hx⟩ _ ⟨_, _, hy⟩ he ↦ h _ _ _ hx _ _ _ hy he⟩

instance [Fintype L] [Fintype C] [DecidableEq Z] [DecidableEq I] :
    Decidable P.IsUnambiguous :=
  decidable_of_iff _ P.isUnambiguous_iff.symm

theorem IsUnambiguous.of_injective2 (hc : Injective2 P.compose) : P.IsUnambiguous :=
  fun _ _ _ _ h ↦ Prod.ext (hc h).1 (hc h).2

variable [DecidableEq Z] [DecidableEq I]

/-- **Canonical inflection** ([corbett-2007], [stump-2016]): every cell has exactly one form, the
stems of a lexeme are the same across its cells and differ between lexemes, and the inflectional
material of a cell differs between the cells of a lexeme and is the same across lexemes. -/
structure IsCanonical : Prop where
  /-- Every cell of every lexeme has a form. -/
  isTotal : W.IsTotal
  /-- No cell has more than one form. -/
  isUnivalent : W.IsUnivalent
  /-- Each lexeme's stems are the same across its cells. -/
  stem_isInvariant : ∀ l, P.stem.IsInvariant l
  /-- Distinct lexemes have disjoint stems at each cell. -/
  stem_disjoint : ∀ c, Pairwise (Disjoint on fun l ↦ P.stem.realize l c)
  /-- Distinct cells of a lexeme have disjoint inflectional material. -/
  inflection_disjoint : ∀ l, Pairwise (Disjoint on P.inflection.realize l)
  /-- Each cell's inflectional material is the same across lexemes. -/
  inflection_isInvariant : ∀ c, P.inflection.transpose.IsInvariant c

variable {P}

omit [DecidableEq Z] [DecidableEq I] in
/-- A form shared by two cells of an unambiguous analysis comes from a pair of both cells. -/
theorem exists_mem_of_mem_realize (hP : P.IsUnambiguous) {l l' : L} {c c' : C} {w : F}
    (hw : w ∈ W.realize l c) (hw' : w ∈ W.realize l' c') :
    ∃ x ∈ P.parts.realize l c, x ∈ P.parts.realize l' c' := by
  rw [P.realize_eq] at hw hw'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
  obtain ⟨y, hy, he⟩ := Finset.mem_image.1 hw'
  exact ⟨x, hx, hP ⟨_, _, hy⟩ ⟨_, _, hx⟩ he ▸ hy⟩

/-- In an unambiguous canonical analysis the distinct cells of a lexeme have distinct forms, and
so do corresponding cells of distinct lexemes, Corbett's comparison of outcomes. -/
theorem IsCanonical.realize_disjoint (h : P.IsCanonical) (hP : P.IsUnambiguous) :
    (∀ l, Pairwise (Disjoint on W.realize l)) ∧
      ∀ c, Pairwise (Disjoint on fun l ↦ W.realize l c) := by
  refine ⟨fun l c c' hcc ↦ Finset.disjoint_left.2 fun w hw hw' ↦ ?_,
    fun c l l' hll ↦ Finset.disjoint_left.2 fun w hw hw' ↦ ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_mem_of_mem_realize hP hw hw'
    exact Finset.disjoint_left.1 (h.inflection_disjoint l hcc)
      (Finset.mem_image_of_mem Prod.snd hx) (Finset.mem_image_of_mem Prod.snd hx')
  · obtain ⟨x, hx, hx'⟩ := exists_mem_of_mem_realize hP hw hw'
    exact Finset.disjoint_left.1 (h.stem_disjoint c hll)
      (Finset.mem_image_of_mem Prod.fst hx) (Finset.mem_image_of_mem Prod.fst hx')

/-- A canonical analysis has no suppletive stem, and no cell whose inflectional material is
suppletive across lexemes. -/
theorem IsCanonical.not_isSuppletive (h : P.IsCanonical) :
    (∀ l, ¬ P.stem.IsSuppletive l) ∧ ∀ c, ¬ P.inflection.transpose.IsSuppletive c :=
  ⟨fun l hs ↦ P.stem.not_isInvariant_of_isSuppletive hs (h.stem_isInvariant l),
    fun c hs ↦ P.inflection.transpose.not_isInvariant_of_isSuppletive hs
      (h.inflection_isInvariant c)⟩

end Analysis

end Morphology.Realization
